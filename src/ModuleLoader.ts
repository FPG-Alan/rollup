import type * as acorn from 'acorn';
import ExternalModule from './ExternalModule';
import type Graph from './Graph';
import Module, { type DynamicImport } from './Module';
import type {
	CustomPluginOptions,
	EmittedChunk,
	HasModuleSideEffects,
	LoadResult,
	ModuleInfo,
	ModuleOptions,
	NormalizedInputOptions,
	PartialNull,
	Plugin,
	ResolvedId,
	ResolveIdResult
} from './rollup/types';
import type { PluginDriver } from './utils/PluginDriver';
import { EMPTY_OBJECT } from './utils/blank';
import { readFile } from './utils/fs';
import { LOGLEVEL_WARN } from './utils/logging';
import {
	error,
	logBadLoader,
	logEntryCannotBeExternal,
	logExternalSyntheticExports,
	logImplicitDependantCannotBeExternal,
	logInconsistentImportAssertions,
	logInternalIdCannotBeExternal,
	logUnresolvedEntry,
	logUnresolvedImplicitDependant,
	logUnresolvedImport,
	logUnresolvedImportTreatedAsExternal
} from './utils/logs';
import { doAssertionsDiffer, getAssertionsFromImportExpression } from './utils/parseAssertions';
import { isAbsolute, isRelative, resolve } from './utils/path';
import relativeId from './utils/relativeId';
import { resolveId } from './utils/resolveId';
import transform from './utils/transform';

export interface UnresolvedModule {
	fileName: string | null;
	id: string;
	importer: string | undefined;
	name: string | null;
}

export type ModuleLoaderResolveId = (
	source: string,
	importer: string | undefined,
	customOptions: CustomPluginOptions | undefined,
	isEntry: boolean | undefined,
	assertions: Record<string, string>,
	skip?: readonly { importer: string | undefined; plugin: Plugin; source: string }[] | null
) => Promise<ResolvedId | null>;

type NormalizedResolveIdWithoutDefaults = Partial<PartialNull<ModuleOptions>> & {
	external?: boolean | 'absolute';
	id: string;
	resolvedBy?: string;
};

type ResolveStaticDependencyPromise = Promise<readonly [source: string, resolvedId: ResolvedId]>;
type ResolveDynamicDependencyPromise = Promise<
	readonly [dynamicImport: DynamicImport, resolvedId: ResolvedId | string | null]
>;
type LoadModulePromise = Promise<
	[
		resolveStaticDependencies: ResolveStaticDependencyPromise[],
		resolveDynamicDependencies: ResolveDynamicDependencyPromise[],
		loadAndResolveDependencies: Promise<void>
	]
>;
type PreloadType = boolean | 'resolveDependencies';
const RESOLVE_DEPENDENCIES: PreloadType = 'resolveDependencies';

export class ModuleLoader {
	private readonly hasModuleSideEffects: HasModuleSideEffects;
	private readonly implicitEntryModules = new Set<Module>();
	private readonly indexedEntryModules: { index: number; module: Module }[] = [];
	private latestLoadModulesPromise: Promise<unknown> = Promise.resolve();
	private readonly moduleLoadPromises = new Map<Module, LoadModulePromise>();
	private readonly modulesWithLoadedDependencies = new Set<Module>();
	private nextChunkNamePriority = 0;
	private nextEntryModuleIndex = 0;

	constructor(
		private readonly graph: Graph,
		private readonly modulesById: Map<string, Module | ExternalModule>,
		private readonly options: NormalizedInputOptions,
		private readonly pluginDriver: PluginDriver
	) {
		this.hasModuleSideEffects = options.treeshake
			? options.treeshake.moduleSideEffects
			: () => true;
	}

	// bundle时处理manualChunk使用
	// 例如 {vandor: ['react', 'react-dom']}
	// 会以 ['react', 'react-dom'] 为参数来调用这个函数
	// 实际可以理解为分别以'react', 'react-dom' 为entryModule重新走一遍fetchModule逻辑， 最终建立一个module子树
	// 重建过程中大部分情况下应该命中 handleExistingModule 逻辑
	async addAdditionalModules(unresolvedModules: readonly string[]): Promise<Module[]> {
		const result = this.extendLoadModulesPromise(
			Promise.all(unresolvedModules.map(id => this.loadEntryModule(id, false, undefined, null)))
		);
		await this.awaitLoadModulesPromise();
		return result;
	}

	//
	/**
	 * 添加入口模块
	 * @param unresolvedEntryModules 没有被接些的入口模块
	 * @param isUserDefined
	 * @returns
	 */
	async addEntryModules(
		unresolvedEntryModules: readonly UnresolvedModule[],
		isUserDefined: boolean
	): Promise<{
		entryModules: Module[];
		implicitEntryModules: Module[];
		newEntryModules: Module[];
	}> {
		const firstEntryModuleIndex = this.nextEntryModuleIndex;
		this.nextEntryModuleIndex += unresolvedEntryModules.length;
		const firstChunkNamePriority = this.nextChunkNamePriority;
		this.nextChunkNamePriority += unresolvedEntryModules.length;

		// extendLoadModulesPromise 没啥，就是把内部的 promise 跟 this.latestLoadModulesPromise 合并， 一起promise.all
		// 另外还有个空的error cache
		const newEntryModules = await this.extendLoadModulesPromise(
			// 一个个加载入口模块
			Promise.all(
				unresolvedEntryModules.map(({ id, importer }) =>
					this.loadEntryModule(id, true, importer, null)
				)
			).then(entryModules => {
				for (const [index, entryModule] of entryModules.entries()) {
					entryModule.isUserDefinedEntryPoint =
						entryModule.isUserDefinedEntryPoint || isUserDefined;
					addChunkNamesToModule(
						entryModule,
						unresolvedEntryModules[index],
						isUserDefined,
						firstChunkNamePriority + index
					);
					const existingIndexedModule = this.indexedEntryModules.find(
						indexedModule => indexedModule.module === entryModule
					);
					if (existingIndexedModule) {
						existingIndexedModule.index = Math.min(
							existingIndexedModule.index,
							firstEntryModuleIndex + index
						);
					} else {
						this.indexedEntryModules.push({
							index: firstEntryModuleIndex + index,
							module: entryModule
						});
					}
				}
				this.indexedEntryModules.sort(({ index: indexA }, { index: indexB }) =>
					indexA > indexB ? 1 : -1
				);
				return entryModules;
			})
		);
		await this.awaitLoadModulesPromise();
		return {
			entryModules: this.indexedEntryModules.map(({ module }) => module),
			implicitEntryModules: [...this.implicitEntryModules],
			newEntryModules
		};
	}

	async emitChunk({
		fileName,
		id,
		importer,
		name,
		implicitlyLoadedAfterOneOf,
		preserveSignature
	}: EmittedChunk): Promise<Module> {
		const unresolvedModule: UnresolvedModule = {
			fileName: fileName || null,
			id,
			importer,
			name: name || null
		};
		const module = implicitlyLoadedAfterOneOf
			? await this.addEntryWithImplicitDependants(unresolvedModule, implicitlyLoadedAfterOneOf)
			: (await this.addEntryModules([unresolvedModule], false)).newEntryModules[0];
		if (preserveSignature != null) {
			module.preserveSignature = preserveSignature;
		}
		return module;
	}

	public async preloadModule(
		resolvedId: { id: string; resolveDependencies?: boolean } & Partial<PartialNull<ModuleOptions>>
	): Promise<ModuleInfo> {
		const module = await this.fetchModule(
			this.getResolvedIdWithDefaults(resolvedId, EMPTY_OBJECT)!,
			undefined,
			false,
			resolvedId.resolveDependencies ? RESOLVE_DEPENDENCIES : true
		);
		return module.info;
	}

	resolveId: ModuleLoaderResolveId = async (
		source,
		importer,
		customOptions,
		isEntry,
		assertions,
		skip = null
	) =>
		this.getResolvedIdWithDefaults(
			this.getNormalizedResolvedIdWithoutDefaults(
				// 这里的external配置项里的外部模块吧
				this.options.external(source, importer, false)
					? false
					: await resolveId(
							source,
							importer,
							this.options.preserveSymlinks,
							this.pluginDriver,
							this.resolveId,
							skip,
							customOptions,
							typeof isEntry === 'boolean' ? isEntry : !importer,
							assertions
					  ),
				importer,
				source
			),
			assertions
		);

	private addEntryWithImplicitDependants(
		unresolvedModule: UnresolvedModule,
		implicitlyLoadedAfter: readonly string[]
	): Promise<Module> {
		const chunkNamePriority = this.nextChunkNamePriority++;
		return this.extendLoadModulesPromise(
			this.loadEntryModule(unresolvedModule.id, false, unresolvedModule.importer, null).then(
				async entryModule => {
					addChunkNamesToModule(entryModule, unresolvedModule, false, chunkNamePriority);
					if (!entryModule.info.isEntry) {
						this.implicitEntryModules.add(entryModule);
						const implicitlyLoadedAfterModules = await Promise.all(
							implicitlyLoadedAfter.map(id =>
								this.loadEntryModule(id, false, unresolvedModule.importer, entryModule.id)
							)
						);
						for (const module of implicitlyLoadedAfterModules) {
							entryModule.implicitlyLoadedAfter.add(module);
						}
						for (const dependant of entryModule.implicitlyLoadedAfter) {
							dependant.implicitlyLoadedBefore.add(entryModule);
						}
					}
					return entryModule;
				}
			)
		);
	}

	// 加载文件， 读取内容，
	private async addModuleSource(
		id: string,
		importer: string | undefined,
		module: Module
	): Promise<void> {
		let source: LoadResult;
		try {
			source = await this.graph.fileOperationQueue.run(
				// 可以通过pluginDriver.hookFirst('load', [id])来修改加载的内容
				// 如果hook不返回， 就直接读取文件内容
				async () =>
					(await this.pluginDriver.hookFirst('load', [id])) ?? (await readFile(id, 'utf8'))
			);
		} catch (error_: any) {
			let message = `Could not load ${id}`;
			if (importer) message += ` (imported by ${relativeId(importer)})`;
			message += `: ${error_.message}`;
			error_.message = message;
			throw error_;
		}
		const sourceDescription =
			typeof source === 'string'
				? { code: source }
				: source != null && typeof source === 'object' && typeof source.code === 'string'
				? source
				: error(logBadLoader(id));
		const cachedModule = this.graph.cachedModules.get(id);

		// 如果有缓存， 并且没有自定义的transformCache， 并且没有修改过， 就直接使用缓存
		if (
			cachedModule &&
			!cachedModule.customTransformCache &&
			cachedModule.originalCode === sourceDescription.code &&
			!(await this.pluginDriver.hookFirst('shouldTransformCachedModule', [
				{
					ast: cachedModule.ast,
					code: cachedModule.code,
					id: cachedModule.id,
					meta: cachedModule.meta,
					moduleSideEffects: cachedModule.moduleSideEffects,
					resolvedSources: cachedModule.resolvedIds,
					syntheticNamedExports: cachedModule.syntheticNamedExports
				}
			]))
		) {
			if (cachedModule.transformFiles) {
				for (const emittedFile of cachedModule.transformFiles)
					this.pluginDriver.emitFile(emittedFile);
			}
			// 如果有缓存， 就直接使用缓存
			module.setSource(cachedModule);
		} else {
			// 如果没有缓存， 就使用transform来处理
			module.updateOptions(sourceDescription);
			module.setSource(
				// 处理transform钩子
				await transform(sourceDescription, module, this.pluginDriver, this.options.onLog)
			);
		}
	}

	private async awaitLoadModulesPromise(): Promise<void> {
		let startingPromise;
		do {
			startingPromise = this.latestLoadModulesPromise;
			await startingPromise;
		} while (startingPromise !== this.latestLoadModulesPromise);
	}

	private extendLoadModulesPromise<T>(loadNewModulesPromise: Promise<T>): Promise<T> {
		this.latestLoadModulesPromise = Promise.all([
			loadNewModulesPromise,
			this.latestLoadModulesPromise
		]);
		this.latestLoadModulesPromise.catch(() => {
			/* Avoid unhandled Promise rejections */
		});
		return loadNewModulesPromise;
	}

	// 加载动态导入的模块
	// fetchModule->fetchModuleDependencies->fetchDynamicDependencies
	private async fetchDynamicDependencies(
		module: Module,
		resolveDynamicImportPromises: readonly ResolveDynamicDependencyPromise[]
	): Promise<void> {
		const dependencies = await Promise.all(
			resolveDynamicImportPromises.map(resolveDynamicImportPromise =>
				resolveDynamicImportPromise.then(async ([dynamicImport, resolvedId]) => {
					if (resolvedId === null) return null;
					if (typeof resolvedId === 'string') {
						dynamicImport.resolution = resolvedId;
						return null;
					}
					return (dynamicImport.resolution = await this.fetchResolvedDependency(
						relativeId(resolvedId.id),
						module.id,
						resolvedId
					));
				})
			)
		);
		for (const dependency of dependencies) {
			if (dependency) {
				module.dynamicDependencies.add(dependency);
				dependency.dynamicImporters.push(module.id);
			}
		}
	}

	// If this is a preload, then this method always waits for the dependencies of
	// the module to be resolved.
	// Otherwise, if the module does not exist, it waits for the module and all
	// its dependencies to be loaded.
	// Otherwise, it returns immediately.
	private async fetchModule(
		{ assertions, id, meta, moduleSideEffects, syntheticNamedExports }: ResolvedId,
		importer: string | undefined,
		isEntry: boolean,
		isPreload: PreloadType
	): Promise<Module> {
		const existingModule = this.modulesById.get(id);
		if (existingModule instanceof Module) {
			if (importer && doAssertionsDiffer(assertions, existingModule.info.assertions)) {
				this.options.onLog(
					LOGLEVEL_WARN,
					logInconsistentImportAssertions(existingModule.info.assertions, assertions, id, importer)
				);
			}
			await this.handleExistingModule(existingModule, isEntry, isPreload);
			return existingModule;
		}

		// 形成一个module
		const module = new Module(
			this.graph,
			id,
			this.options,
			isEntry,
			moduleSideEffects,
			syntheticNamedExports,
			meta,
			assertions
		);
		// 记入缓存
		this.modulesById.set(id, module);
		this.graph.watchFiles[id] = true;

		// addModuleSource -> Module.setSource
		// addModuleSource会加载文件内容， 并在module模块内添加处理ast
		// 在addModuleSource执行完成后, 我们已经拥有了一棵对应当前module的AST的节点实例树
		// 使用module上的 sourcesWithAssertions 和 dynamicImports 两个属性， 获取静态/动态引入的文件的id
		const loadPromise: LoadModulePromise = this.addModuleSource(id, importer, module).then(() => [
			this.getResolveStaticDependencyPromises(module),
			this.getResolveDynamicImportPromises(module),
			loadAndResolveDependenciesPromise
		]);

		// 这里我没看明白， 为什么要这样写，
		// waitForDependencyResolution 是等待 loadPromise 执行完毕，然后返回 loadPromise 返回的数组的前两条
		// 但是then回调内没有拿这个返回值啊

		const loadAndResolveDependenciesPromise = waitForDependencyResolution(loadPromise).then(() =>
			this.pluginDriver.hookParallel('moduleParsed', [module.info])
		);
		loadAndResolveDependenciesPromise.catch(() => {
			/* avoid unhandled promise rejections */
		});

		// 保存 loadPromise
		this.moduleLoadPromises.set(module, loadPromise);

		// 这边有一个await
		const resolveDependencyPromises = await loadPromise;

		// preload 在什么场景下会是true?
		// anyway, fetchModuleDependencies 继续加载module的所有依赖
		if (!isPreload) {
			await this.fetchModuleDependencies(module, ...resolveDependencyPromises);
		} else if (isPreload === RESOLVE_DEPENDENCIES) {
			await loadAndResolveDependenciesPromise;
		}
		return module;
	}

	/**
	 * 获取模块的依赖（静态导入/动态导入/reexport的导入）
	 * @param module
	 * @param resolveStaticDependencyPromises
	 * @param resolveDynamicDependencyPromises
	 * @param loadAndResolveDependenciesPromise
	 * @returns
	 */
	private async fetchModuleDependencies(
		module: Module,
		resolveStaticDependencyPromises: readonly ResolveStaticDependencyPromise[],
		resolveDynamicDependencyPromises: readonly ResolveDynamicDependencyPromise[],
		loadAndResolveDependenciesPromise: Promise<void>
	): Promise<void> {
		// 防止重入
		if (this.modulesWithLoadedDependencies.has(module)) {
			return;
		}
		// 防止重入， 标记当前模块
		this.modulesWithLoadedDependencies.add(module);
		await Promise.all([
			this.fetchStaticDependencies(module, resolveStaticDependencyPromises),
			this.fetchDynamicDependencies(module, resolveDynamicDependencyPromises)
		]);
		module.linkImports();
		// To handle errors when resolving dependencies or in moduleParsed
		await loadAndResolveDependenciesPromise;
	}

	// 递归处理module树的关键节点
	// fetchModule后， fetchStaticDependencies / fetchDynamicDependencies 均会走到这个函数
	private fetchResolvedDependency(
		source: string,
		importer: string,
		resolvedId: ResolvedId
	): Promise<Module | ExternalModule> {
		if (resolvedId.external) {
			// 如果是外部模块， 就不继续递归了， 直接返回
			const { assertions, external, id, moduleSideEffects, meta } = resolvedId;
			let externalModule = this.modulesById.get(id);
			if (!externalModule) {
				// import进来的module对于当前module来说是external module
				externalModule = new ExternalModule(
					this.options,
					id,
					moduleSideEffects,
					meta,
					external !== 'absolute' && isAbsolute(id),
					assertions
				);
				this.modulesById.set(id, externalModule);
			} else if (!(externalModule instanceof ExternalModule)) {
				return error(logInternalIdCannotBeExternal(source, importer));
			} else if (doAssertionsDiffer(externalModule.info.assertions, assertions)) {
				this.options.onLog(
					LOGLEVEL_WARN,
					logInconsistentImportAssertions(
						externalModule.info.assertions,
						assertions,
						source,
						importer
					)
				);
			}
			return Promise.resolve(externalModule);
		}

		// 这里开始递归， 初始化所有引入进来的module
		return this.fetchModule(resolvedId, importer, false, false);
	}

	// 加载静态导入的模块
	// fetchModule->fetchModuleDependencies->fetchStaticDependencies
	private async fetchStaticDependencies(
		module: Module,
		resolveStaticDependencyPromises: readonly ResolveStaticDependencyPromise[]
	): Promise<void> {
		// 这里给了我一个启发， promise resolve了之后随便传， 加上个then就能获取
		for (const dependency of await Promise.all(
			resolveStaticDependencyPromises.map(resolveStaticDependencyPromise =>
				resolveStaticDependencyPromise.then(([source, resolvedId]) =>
					this.fetchResolvedDependency(source, module.id, resolvedId)
				)
			)
		)) {
			module.dependencies.add(dependency);
			dependency.importers.push(module.id);
		}
		if (!this.options.treeshake || module.info.moduleSideEffects === 'no-treeshake') {
			for (const dependency of module.dependencies) {
				if (dependency instanceof Module) {
					dependency.importedFromNotTreeshaken = true;
				}
			}
		}
	}

	/**
	 * 对ResolveIdResult进行归一化处理
	 * resolveResult 可以是 string | NullValue | false | PartialResolvedId
	 * @param resolveIdResult
	 * @param importer
	 * @param source
	 * @returns
	 */
	private getNormalizedResolvedIdWithoutDefaults(
		resolveIdResult: ResolveIdResult,
		importer: string | undefined,
		source: string
	): NormalizedResolveIdWithoutDefaults | null {
		const { makeAbsoluteExternalsRelative } = this.options;
		if (resolveIdResult) {
			if (typeof resolveIdResult === 'object') {
				const external =
					resolveIdResult.external || this.options.external(resolveIdResult.id, importer, true);
				return {
					...resolveIdResult,
					external:
						external &&
						(external === 'relative' ||
							!isAbsolute(resolveIdResult.id) ||
							(external === true &&
								isNotAbsoluteExternal(resolveIdResult.id, source, makeAbsoluteExternalsRelative)) ||
							'absolute')
				};
			}

			const external = this.options.external(resolveIdResult, importer, true);
			return {
				external:
					external &&
					(isNotAbsoluteExternal(resolveIdResult, source, makeAbsoluteExternalsRelative) ||
						'absolute'),
				id:
					external && makeAbsoluteExternalsRelative
						? normalizeRelativeExternalId(resolveIdResult, importer)
						: resolveIdResult
			};
		}

		const id = makeAbsoluteExternalsRelative
			? normalizeRelativeExternalId(source, importer)
			: source;
		if (resolveIdResult !== false && !this.options.external(id, importer, true)) {
			return null;
		}
		return {
			external: isNotAbsoluteExternal(id, source, makeAbsoluteExternalsRelative) || 'absolute',
			id
		};
	}

	private getResolveDynamicImportPromises(module: Module): ResolveDynamicDependencyPromise[] {
		return module.dynamicImports.map(async dynamicImport => {
			const resolvedId = await this.resolveDynamicImport(
				module,
				typeof dynamicImport.argument === 'string'
					? dynamicImport.argument
					: dynamicImport.argument.esTreeNode!,
				module.id,
				getAssertionsFromImportExpression(dynamicImport.node)
			);
			if (resolvedId && typeof resolvedId === 'object') {
				dynamicImport.id = resolvedId.id;
			}
			return [dynamicImport, resolvedId] as const;
		});
	}

	// 返回一组promise, 这个promise arr执行之后, 返回一个二维数组, 每个元素是一个二元数组, 第一个元素是source, 第二个元素是resolvedId
	private getResolveStaticDependencyPromises(module: Module): ResolveStaticDependencyPromise[] {
		// eslint-disable-next-line unicorn/prefer-spread
		return Array.from(
			// module.sourcesWithAssertions是在ast节点解析时, 遇到 ImportDeclaration 节点时通过调用module.addImport添加的
			// 或者re exoprt时也会添加
			module.sourcesWithAssertions,
			async ([source, assertions]) =>
				[
					source,
					(module.resolvedIds[source] =
						module.resolvedIds[source] ||
						this.handleInvalidResolvedId(
							await this.resolveId(source, module.id, EMPTY_OBJECT, false, assertions),
							source,
							module.id,
							assertions
						))
				] as const
		);
	}

	private getResolvedIdWithDefaults(
		resolvedId: NormalizedResolveIdWithoutDefaults | null,
		assertions: Record<string, string>
	): ResolvedId | null {
		if (!resolvedId) {
			return null;
		}
		const external = resolvedId.external || false;
		return {
			assertions: resolvedId.assertions || assertions,
			external,
			id: resolvedId.id,
			meta: resolvedId.meta || {},
			moduleSideEffects:
				resolvedId.moduleSideEffects ?? this.hasModuleSideEffects(resolvedId.id, !!external),
			resolvedBy: resolvedId.resolvedBy ?? 'rollup',
			syntheticNamedExports: resolvedId.syntheticNamedExports ?? false
		};
	}

	private async handleExistingModule(module: Module, isEntry: boolean, isPreload: PreloadType) {
		const loadPromise = this.moduleLoadPromises.get(module)!;
		if (isPreload) {
			return isPreload === RESOLVE_DEPENDENCIES
				? waitForDependencyResolution(loadPromise)
				: loadPromise;
		}
		if (isEntry) {
			module.info.isEntry = true;
			this.implicitEntryModules.delete(module);
			for (const dependant of module.implicitlyLoadedAfter) {
				dependant.implicitlyLoadedBefore.delete(module);
			}
			module.implicitlyLoadedAfter.clear();
		}
		return this.fetchModuleDependencies(module, ...(await loadPromise));
	}

	private handleInvalidResolvedId(
		resolvedId: ResolvedId | null,
		source: string,
		importer: string,
		assertions: Record<string, string>
	): ResolvedId {
		if (resolvedId === null) {
			if (isRelative(source)) {
				return error(logUnresolvedImport(source, importer));
			}
			this.options.onLog(LOGLEVEL_WARN, logUnresolvedImportTreatedAsExternal(source, importer));
			return {
				assertions,
				external: true,
				id: source,
				meta: {},
				moduleSideEffects: this.hasModuleSideEffects(source, true),
				resolvedBy: 'rollup',
				syntheticNamedExports: false
			};
		} else if (resolvedId.external && resolvedId.syntheticNamedExports) {
			this.options.onLog(LOGLEVEL_WARN, logExternalSyntheticExports(source, importer));
		}
		return resolvedId;
	}

	// 加载入口模块
	private async loadEntryModule(
		unresolvedId: string,
		isEntry: boolean,
		importer: string | undefined,
		implicitlyLoadedBefore: string | null
	): Promise<Module> {
		// 获取模块路径
		const resolveIdResult = await resolveId(
			unresolvedId,
			importer,
			this.options.preserveSymlinks,
			this.pluginDriver,
			this.resolveId,
			null,
			EMPTY_OBJECT,
			true,
			EMPTY_OBJECT
		);

		if (resolveIdResult == null) {
			return error(
				implicitlyLoadedBefore === null
					? logUnresolvedEntry(unresolvedId)
					: logUnresolvedImplicitDependant(unresolvedId, implicitlyLoadedBefore)
			);
		}
		if (
			resolveIdResult === false ||
			(typeof resolveIdResult === 'object' && resolveIdResult.external)
		) {
			return error(
				implicitlyLoadedBefore === null
					? logEntryCannotBeExternal(unresolvedId)
					: logImplicitDependantCannotBeExternal(unresolvedId, implicitlyLoadedBefore)
			);
		}

		// 获取模块
		return this.fetchModule(
			// 包装成一个统一的object， object.id即为module的路径
			this.getResolvedIdWithDefaults(
				typeof resolveIdResult === 'object'
					? (resolveIdResult as NormalizedResolveIdWithoutDefaults)
					: { id: resolveIdResult },
				EMPTY_OBJECT
			)!,
			undefined,
			isEntry,
			false
		);
	}

	private async resolveDynamicImport(
		module: Module,
		specifier: string | acorn.Node,
		importer: string,
		assertions: Record<string, string>
	): Promise<ResolvedId | string | null> {
		const resolution = await this.pluginDriver.hookFirst('resolveDynamicImport', [
			specifier,
			importer,
			{ assertions }
		]);
		if (typeof specifier !== 'string') {
			if (typeof resolution === 'string') {
				return resolution;
			}
			if (!resolution) {
				return null;
			}
			return this.getResolvedIdWithDefaults(
				resolution as NormalizedResolveIdWithoutDefaults,
				assertions
			);
		}
		if (resolution == null) {
			const existingResolution = module.resolvedIds[specifier];
			if (existingResolution) {
				if (doAssertionsDiffer(existingResolution.assertions, assertions)) {
					this.options.onLog(
						LOGLEVEL_WARN,
						logInconsistentImportAssertions(
							existingResolution.assertions,
							assertions,
							specifier,
							importer
						)
					);
				}
				return existingResolution;
			}
			return (module.resolvedIds[specifier] = this.handleInvalidResolvedId(
				await this.resolveId(specifier, module.id, EMPTY_OBJECT, false, assertions),
				specifier,
				module.id,
				assertions
			));
		}
		return this.handleInvalidResolvedId(
			this.getResolvedIdWithDefaults(
				this.getNormalizedResolvedIdWithoutDefaults(resolution, importer, specifier),
				assertions
			),
			specifier,
			importer,
			assertions
		);
	}
}

function normalizeRelativeExternalId(source: string, importer: string | undefined): string {
	return isRelative(source)
		? importer
			? resolve(importer, '..', source)
			: resolve(source)
		: source;
}

function addChunkNamesToModule(
	module: Module,
	{ fileName, name }: UnresolvedModule,
	isUserDefined: boolean,
	priority: number
): void {
	if (fileName !== null) {
		module.chunkFileNames.add(fileName);
	} else if (name !== null) {
		// Always keep chunkNames sorted by priority
		let namePosition = 0;
		while (module.chunkNames[namePosition]?.priority < priority) namePosition++;
		module.chunkNames.splice(namePosition, 0, { isUserDefined, name, priority });
	}
}

function isNotAbsoluteExternal(
	id: string,
	source: string,
	makeAbsoluteExternalsRelative: boolean | 'ifRelativeSource'
): boolean {
	return (
		makeAbsoluteExternalsRelative === true ||
		(makeAbsoluteExternalsRelative === 'ifRelativeSource' && isRelative(source)) ||
		!isAbsolute(id)
	);
}

async function waitForDependencyResolution(loadPromise: LoadModulePromise) {
	const [resolveStaticDependencyPromises, resolveDynamicImportPromises] = await loadPromise;
	return Promise.all([...resolveStaticDependencyPromises, ...resolveDynamicImportPromises]);
}
