import * as acorn from 'acorn';
import flru from 'flru';
import type ExternalModule from './ExternalModule';
import Module from './Module';
import { ModuleLoader, type UnresolvedModule } from './ModuleLoader';
import GlobalScope from './ast/scopes/GlobalScope';
import { PathTracker } from './ast/utils/PathTracker';
import type {
	ModuleInfo,
	ModuleJSON,
	NormalizedInputOptions,
	RollupCache,
	RollupWatcher,
	SerializablePluginCache,
	WatchChangeHook
} from './rollup/types';
import { PluginDriver } from './utils/PluginDriver';
import Queue from './utils/Queue';
import { BuildPhase } from './utils/buildPhase';
import { addAnnotations } from './utils/commentAnnotations';
import { analyseModuleExecution } from './utils/executionOrder';
import { LOGLEVEL_WARN } from './utils/logging';
import {
	error,
	logCircularDependency,
	logImplicitDependantIsNotIncluded,
	logMissingExport
} from './utils/logs';
import type { PureFunctions } from './utils/pureFunctions';
import { getPureFunctions } from './utils/pureFunctions';
import { timeEnd, timeStart } from './utils/timers';
import { markModuleAndImpureDependenciesAsExecuted } from './utils/traverseStaticDependencies';

function normalizeEntryModules(
	entryModules: readonly string[] | Record<string, string>
): UnresolvedModule[] {
	if (Array.isArray(entryModules)) {
		return entryModules.map(id => ({
			fileName: null,
			id,
			implicitlyLoadedAfter: [],
			importer: undefined,
			name: null
		}));
	}
	return Object.entries(entryModules).map(([name, id]) => ({
		fileName: null,
		id,
		implicitlyLoadedAfter: [],
		importer: undefined,
		name
	}));
}

export default class Graph {
	readonly acornParser: typeof acorn.Parser;
	readonly astLru = flru<acorn.Node>(5);
	readonly cachedModules = new Map<string, ModuleJSON>();
	readonly deoptimizationTracker = new PathTracker();
	// 属性结构的module数据
	entryModules: Module[] = [];
	readonly fileOperationQueue: Queue;
	readonly moduleLoader: ModuleLoader;
	readonly modulesById = new Map<string, Module | ExternalModule>();
	needsTreeshakingPass = false;
	phase: BuildPhase = BuildPhase.LOAD_AND_PARSE;
	readonly pluginDriver: PluginDriver;
	readonly pureFunctions: PureFunctions;
	readonly scope = new GlobalScope();
	readonly watchFiles: Record<string, true> = Object.create(null);
	watchMode = false;

	private readonly externalModules: ExternalModule[] = [];
	private implicitEntryModules: Module[] = [];
	// 压平的module数据, 经过graph build第二步排序, 在树上越深的越靠前
	private modules: Module[] = [];
	private declare pluginCache?: Record<string, SerializablePluginCache>;

	constructor(private readonly options: NormalizedInputOptions, watcher: RollupWatcher | null) {
		if (options.cache !== false) {
			if (options.cache?.modules) {
				for (const module of options.cache.modules) this.cachedModules.set(module.id, module);
			}
			this.pluginCache = options.cache?.plugins || Object.create(null);

			// increment access counter
			for (const name in this.pluginCache) {
				const cache = this.pluginCache[name];
				for (const value of Object.values(cache)) value[0]++;
			}
		}

		if (watcher) {
			this.watchMode = true;
			const handleChange = (...parameters: Parameters<WatchChangeHook>) =>
				this.pluginDriver.hookParallel('watchChange', parameters);
			const handleClose = () => this.pluginDriver.hookParallel('closeWatcher', []);
			watcher.onCurrentRun('change', handleChange);
			watcher.onCurrentRun('close', handleClose);
		}
		this.pluginDriver = new PluginDriver(this, options, options.plugins, this.pluginCache);
		this.acornParser = acorn.Parser.extend(...(options.acornInjectPlugins as any[]));
		this.moduleLoader = new ModuleLoader(this, this.modulesById, this.options, this.pluginDriver);
		this.fileOperationQueue = new Queue(options.maxParallelFileOps);
		this.pureFunctions = getPureFunctions(options);
	}


	// 生成图的入口
	async build(): Promise<void> {
		timeStart('generate module graph', 2);
		await this.generateModuleGraph();
		timeEnd('generate module graph', 2);

		timeStart('sort and bind modules', 2);
		// 这个阶段会对module进行排序, 并且将module的依赖关系绑定到module上
		// 排序是为啥？后续有啥用？
		this.phase = BuildPhase.ANALYSE;
		this.sortModules();
		timeEnd('sort and bind modules', 2);

		timeStart('mark included statements', 2);
		this.includeStatements();
		timeEnd('mark included statements', 2);

		this.phase = BuildPhase.GENERATE;
	}

	contextParse(code: string, options: Partial<acorn.Options> = {}): acorn.Node {
		const onCommentOrig = options.onComment;
		const comments: acorn.Comment[] = [];

		options.onComment =
			onCommentOrig && typeof onCommentOrig == 'function'
				? (block, text, start, end, ...parameters) => {
						comments.push({ end, start, type: block ? 'Block' : 'Line', value: text });
						return onCommentOrig.call(options, block, text, start, end, ...parameters);
				  }
				: comments;

		const ast = this.acornParser.parse(code, {
			...(this.options.acorn as unknown as acorn.Options),
			...options
		});

		if (typeof onCommentOrig == 'object') {
			onCommentOrig.push(...comments);
		}

		options.onComment = onCommentOrig;

		// 处理无副作用的注释
		addAnnotations(comments, ast, code);

		return ast;
	}

	getCache(): RollupCache {
		// handle plugin cache eviction
		for (const name in this.pluginCache) {
			const cache = this.pluginCache[name];
			let allDeleted = true;
			for (const [key, value] of Object.entries(cache)) {
				if (value[0] >= this.options.experimentalCacheExpiry) delete cache[key];
				else allDeleted = false;
			}
			if (allDeleted) delete this.pluginCache[name];
		}

		return {
			modules: this.modules.map(module => module.toJSON()),
			plugins: this.pluginCache
		};
	}

	getModuleInfo = (moduleId: string): ModuleInfo | null => {
		const foundModule = this.modulesById.get(moduleId);
		if (!foundModule) return null;
		return foundModule.info;
	};


	// 生成图
	private async generateModuleGraph(): Promise<void> {
		({ entryModules: this.entryModules, implicitEntryModules: this.implicitEntryModules } =
			await this.moduleLoader.addEntryModules(normalizeEntryModules(this.options.input), true));
		if (this.entryModules.length === 0) {
			throw new Error('You must supply options.input to rollup');
		}

		// 现在已经有了完整的 module 树, modulesById是压扁的
		for (const module of this.modulesById.values()) {
			if (module instanceof Module) {
				this.modules.push(module);
			} else {
				this.externalModules.push(module);
			}
		}
	}

	// tree shaking
	// 对每个模块， 在其ast上， 对每一个ast node， 标记是否应该包括在最终文件内
	private includeStatements(): void {
		const entryModules = [...this.entryModules, ...this.implicitEntryModules];
		for (const module of entryModules) {
			markModuleAndImpureDependenciesAsExecuted(module);
		}
		if (this.options.treeshake) {
			let treeshakingPass = 1;
			do {
				timeStart(`treeshaking pass ${treeshakingPass}`, 3);
				this.needsTreeshakingPass = false;
				for (const module of this.modules) {
					if (module.isExecuted) {
						if (module.info.moduleSideEffects === 'no-treeshake') {
							module.includeAllInBundle();
						} else {
							module.include();
						}
					}
				}
				if (treeshakingPass === 1) {
					// We only include exports after the first pass to avoid issues with
					// the TDZ detection logic
					for (const module of entryModules) {
						if (module.preserveSignature !== false) {
							module.includeAllExports(false);
							this.needsTreeshakingPass = true;
						}
					}
				}
				timeEnd(`treeshaking pass ${treeshakingPass++}`, 3);
			} while (this.needsTreeshakingPass);
		} else {
			for (const module of this.modules) module.includeAllInBundle();
		}
		for (const externalModule of this.externalModules) externalModule.warnUnusedImports();
		for (const module of this.implicitEntryModules) {
			for (const dependant of module.implicitlyLoadedAfter) {
				if (!(dependant.info.isEntry || dependant.isIncluded())) {
					error(logImplicitDependantIsNotIncluded(dependant));
				}
			}
		}
	}




	private sortModules(): void {
		// 基本上就是把module树按照层次， 从最深的开始向上排列
		const { orderedModules, cyclePaths } = analyseModuleExecution(this.entryModules);
		for (const cyclePath of cyclePaths) {
			this.options.onLog(LOGLEVEL_WARN, logCircularDependency(cyclePath));
		}
		this.modules = orderedModules;
		for (const module of this.modules) {
			// 把module.ast的this指向module
			module.bindReferences();
		}
		this.warnForMissingExports();
	}

	private warnForMissingExports(): void {
		for (const module of this.modules) {
			for (const importDescription of module.importDescriptions.values()) {
				if (
					importDescription.name !== '*' &&
					!importDescription.module.getVariableForExportName(importDescription.name)[0]
				) {
					module.log(
						LOGLEVEL_WARN,
						logMissingExport(importDescription.name, module.id, importDescription.module.id),
						importDescription.start
					);
				}
			}
		}
	}
}
