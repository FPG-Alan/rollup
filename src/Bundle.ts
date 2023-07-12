import Chunk from './Chunk';
import ExternalChunk from './ExternalChunk';
import ExternalModule from './ExternalModule';
import type Graph from './Graph';
import Module from './Module';
import type {
	GetManualChunk,
	LogHandler,
	NormalizedInputOptions,
	NormalizedOutputOptions,
	OutputBundle
} from './rollup/types';
import type { PluginDriver } from './utils/PluginDriver';
import { getChunkAssignments } from './utils/chunkAssignment';
import commondir from './utils/commondir';
import { sortByExecutionOrder } from './utils/executionOrder';
import { getGenerateCodeSnippets } from './utils/generateCodeSnippets';
import type { HashPlaceholderGenerator } from './utils/hashPlaceholders';
import { getHashPlaceholderGenerator } from './utils/hashPlaceholders';
import { LOGLEVEL_WARN } from './utils/logging';
import {
	error,
	logCannotAssignModuleToChunk,
	logChunkInvalid,
	logInvalidOption
} from './utils/logs';
import type { OutputBundleWithPlaceholders } from './utils/outputBundle';
import { getOutputBundle, removeUnreferencedAssets } from './utils/outputBundle';
import { isAbsolute } from './utils/path';
import { renderChunks } from './utils/renderChunks';
import { timeEnd, timeStart } from './utils/timers';
import {
	URL_OUTPUT_AMD_ID,
	URL_OUTPUT_DIR,
	URL_OUTPUT_FORMAT,
	URL_OUTPUT_SOURCEMAPFILE
} from './utils/urls';

export default class Bundle {
	private readonly facadeChunkByModule = new Map<Module, Chunk>();
	private readonly includedNamespaces = new Set<Module>();

	constructor(
		private readonly outputOptions: NormalizedOutputOptions,
		private readonly unsetOptions: ReadonlySet<string>,
		private readonly inputOptions: NormalizedInputOptions,
		private readonly pluginDriver: PluginDriver,
		private readonly graph: Graph
	) {}

	async generate(isWrite: boolean): Promise<OutputBundle> {
		timeStart('GENERATE', 1);
		const outputBundleBase: OutputBundle = Object.create(null);
		const outputBundle = getOutputBundle(outputBundleBase);
		this.pluginDriver.setOutputBundle(outputBundle, this.outputOptions);

		try {
			timeStart('initialize render', 2);

			await this.pluginDriver.hookParallel('renderStart', [this.outputOptions, this.inputOptions]);

			timeEnd('initialize render', 2);
			timeStart('generate chunks', 2);

			const getHashPlaceholder = getHashPlaceholderGenerator();
			const chunks = await this.generateChunks(outputBundle, getHashPlaceholder);
			if (chunks.length > 1) {
				validateOptionsForMultiChunkOutput(this.outputOptions, this.inputOptions.onLog);
			}
			this.pluginDriver.setChunkInformation(this.facadeChunkByModule);
			for (const chunk of chunks) {
				chunk.generateExports();
			}

			timeEnd('generate chunks', 2);

			await renderChunks(
				chunks,
				outputBundle,
				this.pluginDriver,
				this.outputOptions,
				this.inputOptions.onLog
			);
		} catch (error_: any) {
			await this.pluginDriver.hookParallel('renderError', [error_]);
			throw error_;
		}

		removeUnreferencedAssets(outputBundle);

		timeStart('generate bundle', 2);

		await this.pluginDriver.hookSeq('generateBundle', [
			this.outputOptions,
			outputBundle as OutputBundle,
			isWrite
		]);
		this.finaliseAssets(outputBundle);

		timeEnd('generate bundle', 2);
		timeEnd('GENERATE', 1);
		return outputBundleBase;
	}

	// 类似 {vandor: ['react', 'react-dom']}
	private async addManualChunks(
		manualChunks: Record<string, readonly string[]>
	): Promise<Map<Module, string>> {
		const manualChunkAliasByEntry = new Map<Module, string>();
		const chunkEntries = await Promise.all(
			Object.entries(manualChunks).map(async ([alias, files]) => ({
				alias,
				// 分别以'react', 'react-dom' 为entryModule重新走一遍fetchModule逻辑， 最终建立一个module子树
				// entries即为子树的两个根
				entries: await this.graph.moduleLoader.addAdditionalModules(files)
			}))
		);
		for (const { alias, entries } of chunkEntries) {
			for (const entry of entries) {
				addModuleToManualChunk(alias, entry, manualChunkAliasByEntry);
			}
		}
		return manualChunkAliasByEntry;
	}

	private assignManualChunks(getManualChunk: GetManualChunk): Map<Module, string> {
		// eslint-disable-next-line unicorn/prefer-module
		const manualChunkAliasesWithEntry: [alias: string, module: Module][] = [];
		const manualChunksApi = {
			getModuleIds: () => this.graph.modulesById.keys(),
			getModuleInfo: this.graph.getModuleInfo
		};
		for (const module of this.graph.modulesById.values()) {
			if (module instanceof Module) {
				const manualChunkAlias = getManualChunk(module.id, manualChunksApi);
				if (typeof manualChunkAlias === 'string') {
					manualChunkAliasesWithEntry.push([manualChunkAlias, module]);
				}
			}
		}
		manualChunkAliasesWithEntry.sort(([aliasA], [aliasB]) =>
			aliasA > aliasB ? 1 : aliasA < aliasB ? -1 : 0
		);
		const manualChunkAliasByEntry = new Map<Module, string>();
		for (const [alias, module] of manualChunkAliasesWithEntry) {
			addModuleToManualChunk(alias, module, manualChunkAliasByEntry);
		}
		return manualChunkAliasByEntry;
	}

	private finaliseAssets(bundle: OutputBundleWithPlaceholders): void {
		if (this.outputOptions.validate) {
			for (const file of Object.values(bundle)) {
				if ('code' in file) {
					try {
						this.graph.contextParse(file.code, {
							ecmaVersion: 'latest'
						});
					} catch (error_: any) {
						this.inputOptions.onLog(LOGLEVEL_WARN, logChunkInvalid(file, error_));
					}
				}
			}
		}
		this.pluginDriver.finaliseAssets();
	}

	// 这应该是我要的答案
	private async generateChunks(
		bundle: OutputBundleWithPlaceholders,
		getHashPlaceholder: HashPlaceholderGenerator
	): Promise<Chunk[]> {
		const { experimentalMinChunkSize, inlineDynamicImports, manualChunks, preserveModules } =
			this.outputOptions;

		// 首先处理manualChunk相关逻辑
		const manualChunkAliasByEntry =
			typeof manualChunks === 'object'
				? await this.addManualChunks(manualChunks)
				: this.assignManualChunks(manualChunks);

		// 设置rollup包装代码
		const snippets = getGenerateCodeSnippets(this.outputOptions);
		// 过滤出所有会进入bundle的模块
		// 条件是
		// 1. 是module
		// 2. 没有被treeshaking（module.isIncluded）或者 是入口模块 或者 有动态导入
		const includedModules = getIncludedModules(this.graph.modulesById);
		const inputBase = commondir(getAbsoluteEntryModulePaths(includedModules, preserveModules));
		// 对于外部模块， 直接转化成ExternalChunk实例， 一个外部模块一个external chunk实例
		const externalChunkByModule = getExternalChunkByModule(
			this.graph.modulesById,
			this.outputOptions,
			inputBase
		);

		// 开始module到chunk的转换
		const chunks: Chunk[] = [];
		const chunkByModule = new Map<Module, Chunk>();

		// 好大一个for循环体

		// inlineDynamicImports 是配置项， 如果为true则会把动态导入的模块内联进来， 而不是单独一个chunk
		for (const { alias, modules } of inlineDynamicImports
			? [{ alias: null, modules: includedModules }]
			: // preserveModules 也是配置项，如果为true就是每个module对应一个chunk， 这基本可以认为是不打包...
			preserveModules
			? includedModules.map(module => ({ alias: null, modules: [module] }))
			: // 嘿嘿哈， 我觉得我找的就是你！！！
			  // 卧槽， 这玩意注释长的一逼啊
			  getChunkAssignments(
					// 用的是树形结构的数据

					this.graph.entryModules,
					manualChunkAliasByEntry,
					experimentalMinChunkSize,
					this.inputOptions.onLog
			  )) {
			sortByExecutionOrder(modules);
			const chunk = new Chunk(
				modules,
				this.inputOptions,
				this.outputOptions,
				this.unsetOptions,
				this.pluginDriver,
				this.graph.modulesById,
				chunkByModule,
				externalChunkByModule,
				this.facadeChunkByModule,
				this.includedNamespaces,
				alias,
				getHashPlaceholder,
				bundle,
				inputBase,
				snippets
			);
			chunks.push(chunk);
		}
		for (const chunk of chunks) {
			chunk.link();
		}
		const facades: Chunk[] = [];
		for (const chunk of chunks) {
			facades.push(...chunk.generateFacades());
		}
		return [...chunks, ...facades];
	}
}

function validateOptionsForMultiChunkOutput(
	outputOptions: NormalizedOutputOptions,
	log: LogHandler
) {
	if (outputOptions.format === 'umd' || outputOptions.format === 'iife')
		return error(
			logInvalidOption(
				'output.format',
				URL_OUTPUT_FORMAT,
				'UMD and IIFE output formats are not supported for code-splitting builds',
				outputOptions.format
			)
		);
	if (typeof outputOptions.file === 'string')
		return error(
			logInvalidOption(
				'output.file',
				URL_OUTPUT_DIR,
				'when building multiple chunks, the "output.dir" option must be used, not "output.file". To inline dynamic imports, set the "inlineDynamicImports" option'
			)
		);
	if (outputOptions.sourcemapFile)
		return error(
			logInvalidOption(
				'output.sourcemapFile',
				URL_OUTPUT_SOURCEMAPFILE,
				'"output.sourcemapFile" is only supported for single-file builds'
			)
		);
	if (!outputOptions.amd.autoId && outputOptions.amd.id)
		log(
			LOGLEVEL_WARN,
			logInvalidOption(
				'output.amd.id',
				URL_OUTPUT_AMD_ID,
				'this option is only properly supported for single-file builds. Use "output.amd.autoId" and "output.amd.basePath" instead'
			)
		);
}

function getIncludedModules(modulesById: ReadonlyMap<string, Module | ExternalModule>): Module[] {
	const includedModules: Module[] = [];
	for (const module of modulesById.values()) {
		if (
			module instanceof Module &&
			(module.isIncluded() || module.info.isEntry || module.includedDynamicImporters.length > 0)
		) {
			includedModules.push(module);
		}
	}
	return includedModules;
}

function getAbsoluteEntryModulePaths(
	includedModules: readonly Module[],
	preserveModules: boolean
): string[] {
	const absoluteEntryModulePaths: string[] = [];
	for (const module of includedModules) {
		if ((module.info.isEntry || preserveModules) && isAbsolute(module.id)) {
			absoluteEntryModulePaths.push(module.id);
		}
	}
	return absoluteEntryModulePaths;
}

function getExternalChunkByModule(
	modulesById: ReadonlyMap<string, Module | ExternalModule>,
	outputOptions: NormalizedOutputOptions,
	inputBase: string
): Map<ExternalModule, ExternalChunk> {
	const externalChunkByModule = new Map<ExternalModule, ExternalChunk>();
	for (const module of modulesById.values()) {
		if (module instanceof ExternalModule) {
			externalChunkByModule.set(module, new ExternalChunk(module, outputOptions, inputBase));
		}
	}
	return externalChunkByModule;
}

function addModuleToManualChunk(
	alias: string,
	module: Module,
	manualChunkAliasByEntry: Map<Module, string>
): void {
	const existingAlias = manualChunkAliasByEntry.get(module);

	// 防止用户错误设置manualChunk， 类似下面的情况
	// {vandor: ['react', 'react-dom']， common:['react]};

	if (typeof existingAlias === 'string' && existingAlias !== alias) {
		return error(logCannotAssignModuleToChunk(module.id, alias, existingAlias));
	}
	manualChunkAliasByEntry.set(module, alias);
}
