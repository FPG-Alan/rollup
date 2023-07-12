import { extractAssignedNames } from '@rollup/pluginutils';
import type * as acorn from 'acorn';
import { locate } from 'locate-character';
import MagicString from 'magic-string';
import ExternalModule from './ExternalModule';
import type Graph from './Graph';
import { createInclusionContext } from './ast/ExecutionContext';
import { nodeConstructors } from './ast/nodes';
import ExportAllDeclaration from './ast/nodes/ExportAllDeclaration';
import ExportDefaultDeclaration from './ast/nodes/ExportDefaultDeclaration';
import type ExportNamedDeclaration from './ast/nodes/ExportNamedDeclaration';
import Identifier from './ast/nodes/Identifier';
import type ImportDeclaration from './ast/nodes/ImportDeclaration';
import ImportDefaultSpecifier from './ast/nodes/ImportDefaultSpecifier';
import type ImportExpression from './ast/nodes/ImportExpression';
import ImportNamespaceSpecifier from './ast/nodes/ImportNamespaceSpecifier';
import Literal from './ast/nodes/Literal';
import type MetaProperty from './ast/nodes/MetaProperty';
import Program from './ast/nodes/Program';
import TemplateLiteral from './ast/nodes/TemplateLiteral';
import VariableDeclaration from './ast/nodes/VariableDeclaration';
import type { ExpressionNode, NodeBase } from './ast/nodes/shared/Node';
import ModuleScope from './ast/scopes/ModuleScope';
import { type PathTracker, UNKNOWN_PATH } from './ast/utils/PathTracker';
import ExportDefaultVariable from './ast/variables/ExportDefaultVariable';
import ExportShimVariable from './ast/variables/ExportShimVariable';
import ExternalVariable from './ast/variables/ExternalVariable';
import NamespaceVariable from './ast/variables/NamespaceVariable';
import SyntheticNamedExportVariable from './ast/variables/SyntheticNamedExportVariable';
import type Variable from './ast/variables/Variable';
import type {
	CustomPluginOptions,
	DecodedSourceMapOrMissing,
	EmittedFile,
	ExistingDecodedSourceMap,
	LogLevel,
	ModuleInfo,
	ModuleJSON,
	ModuleOptions,
	NormalizedInputOptions,
	PartialNull,
	PreserveEntrySignaturesOption,
	ResolvedId,
	ResolvedIdMap,
	RollupError,
	RollupLog,
	TransformModuleJSON
} from './rollup/types';
import { EMPTY_OBJECT } from './utils/blank';
import { BuildPhase } from './utils/buildPhase';
import { getId } from './utils/getId';
import { getNewSet, getOrCreate } from './utils/getOrCreate';
import { getOriginalLocation } from './utils/getOriginalLocation';
import { makeLegal } from './utils/identifierHelpers';
import { LOGLEVEL_WARN } from './utils/logging';
import {
	augmentCodeLocation,
	error,
	logAmbiguousExternalNamespaces,
	logCircularReexport,
	logInconsistentImportAssertions,
	logInvalidFormatForTopLevelAwait,
	logInvalidSourcemapForError,
	logMissingExport,
	logNamespaceConflict,
	logParseError,
	logShimmedExport,
	logSyntheticNamedExportsNeedNamespaceExport,
	warnDeprecation
} from './utils/logs';
import {
	doAssertionsDiffer,
	getAssertionsFromImportExportDeclaration
} from './utils/parseAssertions';
import { basename, extname } from './utils/path';
import type { PureFunctions } from './utils/pureFunctions';
import type { RenderOptions } from './utils/renderHelpers';
import { timeEnd, timeStart } from './utils/timers';
import { markModuleAndImpureDependenciesAsExecuted } from './utils/traverseStaticDependencies';
import { URL_THIS_GETMODULEINFO } from './utils/urls';
import { MISSING_EXPORT_SHIM_VARIABLE } from './utils/variableNames';

interface ImportDescription {
	module: Module | ExternalModule;
	name: string;
	source: string;
	start: number;
}

interface ExportDescription {
	identifier: string | null;
	localName: string;
}

interface ReexportDescription {
	localName: string;
	module: Module | ExternalModule;
	source: string;
	start: number;
}

export interface AstContext {
	addDynamicImport: (node: ImportExpression) => void;
	addExport: (
		node: ExportAllDeclaration | ExportNamedDeclaration | ExportDefaultDeclaration
	) => void;
	addImport: (node: ImportDeclaration) => void;
	addImportMeta: (node: MetaProperty) => void;
	code: string;
	deoptimizationTracker: PathTracker;
	error: (properties: RollupLog, pos: number) => never;
	fileName: string;
	getExports: () => string[];
	getModuleExecIndex: () => number;
	getModuleName: () => string;
	getNodeConstructor: (name: string) => typeof NodeBase;
	getReexports: () => string[];
	importDescriptions: Map<string, ImportDescription>;
	includeAllExports: () => void;
	includeDynamicImport: (node: ImportExpression) => void;
	includeVariableInModule: (variable: Variable) => void;
	log: (level: LogLevel, properties: RollupLog, pos: number) => void;
	magicString: MagicString;
	manualPureFunctions: PureFunctions;
	module: Module; // not to be used for tree-shaking
	moduleContext: string;
	options: NormalizedInputOptions;
	requestTreeshakingPass: () => void;
	traceExport: (name: string) => Variable | null;
	traceVariable: (name: string) => Variable | null;
	usesTopLevelAwait: boolean;
}

export interface DynamicImport {
	argument: string | ExpressionNode;
	id: string | null;
	node: ImportExpression;
	resolution: Module | ExternalModule | string | null;
}

const MISSING_EXPORT_SHIM_DESCRIPTION: ExportDescription = {
	identifier: null,
	localName: MISSING_EXPORT_SHIM_VARIABLE
};

function getVariableForExportNameRecursive(
	target: Module | ExternalModule,
	name: string,
	importerForSideEffects: Module | undefined,
	isExportAllSearch: boolean | undefined,
	searchedNamesAndModules = new Map<string, Set<Module | ExternalModule>>()
): [variable: Variable | null, indirectExternal?: boolean] {
	const searchedModules = searchedNamesAndModules.get(name);
	if (searchedModules) {
		if (searchedModules.has(target)) {
			return isExportAllSearch ? [null] : error(logCircularReexport(name, target.id));
		}
		searchedModules.add(target);
	} else {
		searchedNamesAndModules.set(name, new Set([target]));
	}
	return target.getVariableForExportName(name, {
		importerForSideEffects,
		isExportAllSearch,
		searchedNamesAndModules
	});
}

function getAndExtendSideEffectModules(variable: Variable, module: Module): Set<Module> {
	const sideEffectModules = getOrCreate(
		module.sideEffectDependenciesByVariable,
		variable,
		getNewSet<Module>
	);
	let currentVariable: Variable | null = variable;
	const referencedVariables = new Set([currentVariable]);
	while (true) {
		const importingModule = currentVariable.module! as Module;
		currentVariable =
			currentVariable instanceof ExportDefaultVariable
				? currentVariable.getDirectOriginalVariable()
				: currentVariable instanceof SyntheticNamedExportVariable
				? currentVariable.syntheticNamespace
				: null;
		if (!currentVariable || referencedVariables.has(currentVariable)) {
			break;
		}
		referencedVariables.add(currentVariable);
		sideEffectModules.add(importingModule);
		const originalSideEffects =
			importingModule.sideEffectDependenciesByVariable.get(currentVariable);
		if (originalSideEffects) {
			for (const module of originalSideEffects) {
				sideEffectModules.add(module);
			}
		}
	}
	return sideEffectModules;
}

// implicitlyLoadedBefore 是什么
// 插件行为

export default class Module {
	readonly alternativeReexportModules = new Map<Variable, Module>();
	readonly chunkFileNames = new Set<string>();
	chunkNames: {
		isUserDefined: boolean;
		name: string;
		priority: number;
	}[] = [];
	readonly cycles = new Set<symbol>();
	// 在module loader 的 fetchModule之后， fetchStaticDependencies函数内赋值
	// 这个字段是当前module的所有静态导入的module集合
	readonly dependencies = new Set<Module | ExternalModule>();
	// 在module loader 的 fetchModule之后， fetchDynamicDependencies函数内赋值
	// 这个字段是当前module的所有动态导入的module集合
	readonly dynamicDependencies = new Set<Module | ExternalModule>();
	readonly dynamicImporters: string[] = [];
	// 在建立module的AST实例树的时候赋值的
	readonly dynamicImports: DynamicImport[] = [];
	excludeFromSourcemap: boolean;
	execIndex = Infinity;
	readonly implicitlyLoadedAfter = new Set<Module>();
	readonly implicitlyLoadedBefore = new Set<Module>();
	readonly importDescriptions = new Map<string, ImportDescription>();
	readonly importMetas: MetaProperty[] = [];
	importedFromNotTreeshaken = false;
	readonly importers: string[] = [];
	readonly includedDynamicImporters: Module[] = [];
	readonly includedImports = new Set<Variable>();
	readonly info: ModuleInfo;
	isExecuted = false;
	isUserDefinedEntryPoint = false;
	declare magicString: MagicString;
	declare namespace: NamespaceVariable;
	needsExportShim = false;
	declare originalCode: string;
	declare originalSourcemap: ExistingDecodedSourceMap | null;
	preserveSignature: PreserveEntrySignaturesOption;
	declare resolvedIds: ResolvedIdMap;
	declare scope: ModuleScope;
	readonly sideEffectDependenciesByVariable = new Map<Variable, Set<Module>>();
	declare sourcemapChain: DecodedSourceMapOrMissing[];
	// 当前模块引入的模块, 包含import的和reexport的
	readonly sourcesWithAssertions = new Map<string, Record<string, string>>();
	declare transformFiles?: EmittedFile[];

	private allExportNames: Set<string> | null = null;
	private ast: Program | null = null;
	private declare astContext: AstContext;
	private readonly context: string;
	private declare customTransformCache: boolean;
	private readonly exportAllModules: (Module | ExternalModule)[] = [];
	private readonly exportAllSources = new Set<string>();
	private exportNamesByVariable: Map<Variable, string[]> | null = null;
	private readonly exportShimVariable = new ExportShimVariable(this);
	private readonly exports = new Map<string, ExportDescription>();
	private readonly namespaceReexportsByName = new Map<
		string,
		[variable: Variable | null, indirectExternal?: boolean]
	>();
	private readonly reexportDescriptions = new Map<string, ReexportDescription>();
	private relevantDependencies: Set<Module | ExternalModule> | null = null;
	private readonly syntheticExports = new Map<string, SyntheticNamedExportVariable>();
	private syntheticNamespace: Variable | null | undefined = null;
	private transformDependencies: string[] = [];
	private transitiveReexports: string[] | null = null;

	constructor(
		private readonly graph: Graph,
		public readonly id: string,
		private readonly options: NormalizedInputOptions,
		isEntry: boolean,
		moduleSideEffects: boolean | 'no-treeshake',
		syntheticNamedExports: boolean | string,
		meta: CustomPluginOptions,
		assertions: Record<string, string>
	) {
		this.excludeFromSourcemap = /\0/.test(id);
		this.context = options.moduleContext(id);
		this.preserveSignature = this.options.preserveEntrySignatures;

		// eslint-disable-next-line @typescript-eslint/no-this-alias
		const module = this;
		const {
			dynamicImports,
			dynamicImporters,
			exportAllSources,
			exports,
			implicitlyLoadedAfter,
			implicitlyLoadedBefore,
			importers,
			reexportDescriptions,
			sourcesWithAssertions
		} = this;

		this.info = {
			assertions,
			ast: null,
			code: null,
			get dynamicallyImportedIdResolutions() {
				return dynamicImports
					.map(({ argument }) => typeof argument === 'string' && module.resolvedIds[argument])
					.filter(Boolean) as ResolvedId[];
			},
			get dynamicallyImportedIds() {
				// We cannot use this.dynamicDependencies because this is needed before
				// dynamicDependencies are populated
				return dynamicImports.map(({ id }) => id).filter((id): id is string => id != null);
			},
			get dynamicImporters() {
				return dynamicImporters.sort();
			},
			get exportedBindings() {
				const exportBindings: Record<string, string[]> = { '.': [...exports.keys()] };

				for (const [name, { source }] of reexportDescriptions) {
					(exportBindings[source] ??= []).push(name);
				}

				for (const source of exportAllSources) {
					(exportBindings[source] ??= []).push('*');
				}

				return exportBindings;
			},
			get exports() {
				return [
					...exports.keys(),
					...reexportDescriptions.keys(),
					...[...exportAllSources].map(() => '*')
				];
			},
			get hasDefaultExport() {
				// This information is only valid after parsing
				if (!module.ast) {
					return null;
				}
				return module.exports.has('default') || reexportDescriptions.has('default');
			},
			get hasModuleSideEffects() {
				warnDeprecation(
					'Accessing ModuleInfo.hasModuleSideEffects from plugins is deprecated. Please use ModuleInfo.moduleSideEffects instead.',
					URL_THIS_GETMODULEINFO,
					true,
					options
				);
				return this.moduleSideEffects;
			},
			id,
			get implicitlyLoadedAfterOneOf() {
				// eslint-disable-next-line unicorn/prefer-spread
				return Array.from(implicitlyLoadedAfter, getId).sort();
			},
			get implicitlyLoadedBefore() {
				// eslint-disable-next-line unicorn/prefer-spread
				return Array.from(implicitlyLoadedBefore, getId).sort();
			},
			get importedIdResolutions() {
				// eslint-disable-next-line unicorn/prefer-spread
				return Array.from(
					sourcesWithAssertions.keys(),
					source => module.resolvedIds[source]
				).filter(Boolean);
			},
			get importedIds() {
				// We cannot use this.dependencies because this is needed before
				// dependencies are populated
				// eslint-disable-next-line unicorn/prefer-spread
				return Array.from(
					sourcesWithAssertions.keys(),
					source => module.resolvedIds[source]?.id
				).filter(Boolean);
			},
			get importers() {
				return importers.sort();
			},
			isEntry,
			isExternal: false,
			get isIncluded() {
				if (graph.phase !== BuildPhase.GENERATE) {
					return null;
				}
				return module.isIncluded();
			},
			meta: { ...meta },
			moduleSideEffects,
			syntheticNamedExports
		};
		// Hide the deprecated key so that it only warns when accessed explicitly
		// eslint-disable-next-line unicorn/consistent-destructuring
		Object.defineProperty(this.info, 'hasModuleSideEffects', {
			enumerable: false
		});
	}

	basename(): string {
		const base = basename(this.id);
		const extension = extname(this.id);

		return makeLegal(extension ? base.slice(0, -extension.length) : base);
	}

	bindReferences(): void {
		this.ast!.bind();
	}

	error(properties: RollupError, pos: number): never {
		this.addLocationToLogProps(properties, pos);
		return error(properties);
	}

	// sum up the length of all ast nodes that are included
	estimateSize(): number {
		let size = 0;
		for (const node of this.ast!.body) {
			if (node.included) {
				size += node.end - node.start;
			}
		}
		return size;
	}

	// 返回当前模块的所有导出名
	getAllExportNames(): Set<string> {
		if (this.allExportNames) {
			return this.allExportNames;
		}
		// 普通的具名导出/reexport， 从其他模块导入， 再重新导出的
		this.allExportNames = new Set([...this.exports.keys(), ...this.reexportDescriptions.keys()]);
		// linkImports 函数内对this.exportAllModules进行了赋值
		for (const module of this.exportAllModules) {
			// 外部模块， 导入，但是没有包括在图中
			if (module instanceof ExternalModule) {
				this.allExportNames.add(`*${module.id}`);
				continue;
			}

			// 获取所有导出的模块的导出名
			for (const name of module.getAllExportNames()) {
				if (name !== 'default') this.allExportNames.add(name);
			}
		}
		// We do not count the synthetic namespace as a regular export to hide it
		// from entry signatures and namespace objects
		// 我们不将合成命名空间算作常规导出，以将其隐藏在条目签名和命名空间对象中
		if (typeof this.info.syntheticNamedExports === 'string') {
			this.allExportNames.delete(this.info.syntheticNamedExports);
		}
		return this.allExportNames;
	}

	getDependenciesToBeIncluded(): Set<Module | ExternalModule> {
		// 防止重入
		if (this.relevantDependencies) return this.relevantDependencies;

		// 相关的依赖
		this.relevantDependencies = new Set<Module | ExternalModule>();

		// 下面主要是为了得到 necessaryDependencies / alwaysCheckedDependencies 这两个东西
		// 然后这两个东西主要是为了tree shaking
		const necessaryDependencies = new Set<Module | ExternalModule>();
		const alwaysCheckedDependencies = new Set<Module>();
		// 初始化为所有经过tree shaking的imports
		const dependencyVariables = new Set(this.includedImports);
		// 如果是入口模块，或者有动态导入，或者有导出，或者有隐式加载的模块
		// 处理导出， 为啥？
		if (
			this.info.isEntry ||
			this.includedDynamicImporters.length > 0 ||
			this.namespace.included ||
			this.implicitlyLoadedAfter.size > 0
		) {
			// 遍历所有导出名
			// 遍历导出干嘛...
			for (const exportName of [...this.getReexports(), ...this.getExports()]) {
				const [exportedVariable] = this.getVariableForExportName(exportName);
				if (exportedVariable?.included) {
					dependencyVariables.add(exportedVariable);
				}
			}
		}

		// 处理 alwaysCheckedDependencies 和 necessaryDependencies
		// 暂时...不管了
		for (let variable of dependencyVariables) {
			const sideEffectDependencies = this.sideEffectDependenciesByVariable.get(variable);
			if (sideEffectDependencies) {
				for (const module of sideEffectDependencies) {
					alwaysCheckedDependencies.add(module);
				}
			}
			if (variable instanceof SyntheticNamedExportVariable) {
				variable = variable.getBaseVariable();
			} else if (variable instanceof ExportDefaultVariable) {
				variable = variable.getOriginalVariable();
			}
			necessaryDependencies.add(variable.module!);
		}

		// 不做tree shaking的话， 上面俩IF就不用执行了吧
		// 这里也没管 dependencyVariables / necessaryDependencies / alwaysCheckedDependencies 啥的呀
		if (!this.options.treeshake || this.info.moduleSideEffects === 'no-treeshake') {
			for (const dependency of this.dependencies) {
				this.relevantDependencies.add(dependency);
			}
		} else {
			this.addRelevantSideEffectDependencies(
				this.relevantDependencies,
				necessaryDependencies,
				alwaysCheckedDependencies
			);
		}

		for (const dependency of necessaryDependencies) {
			this.relevantDependencies.add(dependency);
		}

		return this.relevantDependencies;
	}

	// 拿模块的导出名, variable是AST领域的东西， 暂时当作是一个实例
	getExportNamesByVariable(): Map<Variable, string[]> {
		// 已经执行过， 直接返回结果
		if (this.exportNamesByVariable) {
			return this.exportNamesByVariable;
		}
		const exportNamesByVariable = new Map<Variable, string[]>();

		for (const exportName of this.getAllExportNames()) {
			let [tracedVariable] = this.getVariableForExportName(exportName);
			if (tracedVariable instanceof ExportDefaultVariable) {
				tracedVariable = tracedVariable.getOriginalVariable();
			}
			if (
				!tracedVariable ||
				!(tracedVariable.included || tracedVariable instanceof ExternalVariable)
			) {
				continue;
			}
			const existingExportNames = exportNamesByVariable.get(tracedVariable);
			if (existingExportNames) {
				existingExportNames.push(exportName);
			} else {
				exportNamesByVariable.set(tracedVariable, [exportName]);
			}
		}
		return (this.exportNamesByVariable = exportNamesByVariable);
	}

	getExports(): string[] {
		return [...this.exports.keys()];
	}

	getReexports(): string[] {
		if (this.transitiveReexports) {
			return this.transitiveReexports;
		}
		// to avoid infinite recursion when using circular `export * from X`
		this.transitiveReexports = [];

		const reexports = new Set(this.reexportDescriptions.keys());

		for (const module of this.exportAllModules) {
			if (module instanceof ExternalModule) {
				reexports.add(`*${module.id}`);
			} else {
				for (const name of [...module.getReexports(), ...module.getExports()]) {
					if (name !== 'default') reexports.add(name);
				}
			}
		}
		return (this.transitiveReexports = [...reexports]);
	}

	getRenderedExports(): { removedExports: string[]; renderedExports: string[] } {
		// only direct exports are counted here, not reexports at all
		const renderedExports: string[] = [];
		const removedExports: string[] = [];
		for (const exportName of this.exports.keys()) {
			const [variable] = this.getVariableForExportName(exportName);
			(variable && variable.included ? renderedExports : removedExports).push(exportName);
		}
		return { removedExports, renderedExports };
	}

	getSyntheticNamespace(): Variable {
		if (this.syntheticNamespace === null) {
			this.syntheticNamespace = undefined;
			[this.syntheticNamespace] = this.getVariableForExportName(
				typeof this.info.syntheticNamedExports === 'string'
					? this.info.syntheticNamedExports
					: 'default',
				{ onlyExplicit: true }
			);
		}
		if (!this.syntheticNamespace) {
			return error(
				logSyntheticNamedExportsNeedNamespaceExport(this.id, this.info.syntheticNamedExports)
			);
		}
		return this.syntheticNamespace;
	}

	getVariableForExportName(
		name: string,
		{
			importerForSideEffects,
			isExportAllSearch,
			onlyExplicit,
			searchedNamesAndModules
		}: {
			importerForSideEffects?: Module;
			isExportAllSearch?: boolean;
			onlyExplicit?: boolean;
			searchedNamesAndModules?: Map<string, Set<Module | ExternalModule>>;
		} = EMPTY_OBJECT
	): [variable: Variable | null, indirectExternal?: boolean] {
		// 两种reexport的情况
		if (name[0] === '*') {
			if (name.length === 1) {
				// export * from './other'
				return [this.namespace];
			}
			// 这种时候, export name是 *external
			// export * from 'external'
			// external module也会出现在图内...
			const module = this.graph.modulesById.get(name.slice(1)) as ExternalModule;
			return module.getVariableForExportName('*');
		}

		// export { foo } from './other'
		const reexportDeclaration = this.reexportDescriptions.get(name);
		if (reexportDeclaration) {
			const [variable] = getVariableForExportNameRecursive(
				reexportDeclaration.module,
				reexportDeclaration.localName,
				importerForSideEffects,
				false,
				searchedNamesAndModules
			);
			if (!variable) {
				return this.error(
					logMissingExport(reexportDeclaration.localName, this.id, reexportDeclaration.module.id),
					reexportDeclaration.start
				);
			}

			// 副作用导入应该是 import from 'xxx' 这种吧
			if (importerForSideEffects) {
				setAlternativeExporterIfCyclic(variable, importerForSideEffects, this);
				if (this.info.moduleSideEffects) {
					getOrCreate(
						importerForSideEffects.sideEffectDependenciesByVariable,
						variable,
						getNewSet<Module>
					).add(this);
				}
			}
			return [variable];
		}

		const exportDeclaration = this.exports.get(name);
		if (exportDeclaration) {
			if (exportDeclaration === MISSING_EXPORT_SHIM_DESCRIPTION) {
				return [this.exportShimVariable];
			}
			const name = exportDeclaration.localName;
			const variable = this.traceVariable(name, {
				importerForSideEffects,
				searchedNamesAndModules
			})!;
			if (importerForSideEffects) {
				setAlternativeExporterIfCyclic(variable, importerForSideEffects, this);
				getOrCreate(
					importerForSideEffects.sideEffectDependenciesByVariable,
					variable,
					getNewSet<Module>
				).add(this);
			}
			return [variable];
		}

		if (onlyExplicit) {
			return [null];
		}

		if (name !== 'default') {
			const foundNamespaceReexport =
				this.namespaceReexportsByName.get(name) ??
				this.getVariableFromNamespaceReexports(
					name,
					importerForSideEffects,
					searchedNamesAndModules
				);
			this.namespaceReexportsByName.set(name, foundNamespaceReexport);
			if (foundNamespaceReexport[0]) {
				return foundNamespaceReexport;
			}
		}

		if (this.info.syntheticNamedExports) {
			return [
				getOrCreate(
					this.syntheticExports,
					name,
					() =>
						new SyntheticNamedExportVariable(this.astContext, name, this.getSyntheticNamespace())
				)
			];
		}

		// we don't want to create shims when we are just
		// probing export * modules for exports
		if (!isExportAllSearch && this.options.shimMissingExports) {
			this.shimMissingExport(name);
			return [this.exportShimVariable];
		}
		return [null];
	}

	hasEffects(): boolean {
		return this.info.moduleSideEffects === 'no-treeshake' || this.ast!.hasCachedEffects();
	}

	include(): void {
		const context = createInclusionContext();
		if (this.ast!.shouldBeIncluded(context)) this.ast!.include(context, false);
	}

	includeAllExports(includeNamespaceMembers: boolean): void {
		if (!this.isExecuted) {
			markModuleAndImpureDependenciesAsExecuted(this);
			this.graph.needsTreeshakingPass = true;
		}

		for (const exportName of this.exports.keys()) {
			if (includeNamespaceMembers || exportName !== this.info.syntheticNamedExports) {
				const variable = this.getVariableForExportName(exportName)[0]!;
				variable.deoptimizePath(UNKNOWN_PATH);
				if (!variable.included) {
					this.includeVariable(variable);
				}
			}
		}

		for (const name of this.getReexports()) {
			const [variable] = this.getVariableForExportName(name);
			if (variable) {
				variable.deoptimizePath(UNKNOWN_PATH);
				if (!variable.included) {
					this.includeVariable(variable);
				}
				if (variable instanceof ExternalVariable) {
					variable.module.reexported = true;
				}
			}
		}

		if (includeNamespaceMembers) {
			this.namespace.setMergedNamespaces(this.includeAndGetAdditionalMergedNamespaces());
		}
	}

	includeAllInBundle(): void {
		this.ast!.include(createInclusionContext(), true);
		this.includeAllExports(false);
	}

	includeExportsByNames(names: readonly string[]): void {
		if (!this.isExecuted) {
			markModuleAndImpureDependenciesAsExecuted(this);
			this.graph.needsTreeshakingPass = true;
		}

		let includeNamespaceMembers = false;

		for (const name of names) {
			const variable = this.getVariableForExportName(name)[0];
			if (variable) {
				variable.deoptimizePath(UNKNOWN_PATH);
				if (!variable.included) {
					this.includeVariable(variable);
				}
			}

			if (!this.exports.has(name) && !this.reexportDescriptions.has(name)) {
				includeNamespaceMembers = true;
			}
		}

		if (includeNamespaceMembers) {
			this.namespace.setMergedNamespaces(this.includeAndGetAdditionalMergedNamespaces());
		}
	}

	isIncluded(): boolean | null {
		// Modules where this.ast is missing have been loaded via this.load and are
		// not yet fully processed, hence they cannot be included.
		return (
			this.ast &&
			(this.ast.included ||
				this.namespace.included ||
				this.importedFromNotTreeshaken ||
				this.exportShimVariable.included)
		);
	}

	// 做了两件事
	// 一是给所有 importDescriptions/reexportDescriptions 赋值 module 属性
	// 二是根据 this.exportAllSources 找到对应的 module, 填充 this.exportAllModules
	// 符合 "link" 这个动作, 但名字改为 linkImportsAndExports 更明确
	linkImports(): void {
		// 遍历 importDescriptions, 每个 importDescription 找到对应的 module, 写入对应 importDescriptions
		this.addModulesToImportDescriptions(this.importDescriptions);
		// 遍历 reexportDescriptions, 每个 reexportDescription 找到对应的 module, 写入对应 reexportDescriptions
		this.addModulesToImportDescriptions(this.reexportDescriptions);

		// 遍历exportAllSources, 每个source找到对应的module， 区别是internal还是external
		// 都push到 this.exportAllModules
		const externalExportAllModules: ExternalModule[] = [];
		for (const source of this.exportAllSources) {
			const module = this.graph.modulesById.get(this.resolvedIds[source].id)!;
			if (module instanceof ExternalModule) {
				externalExportAllModules.push(module);
				continue;
			}
			this.exportAllModules.push(module);
		}
		this.exportAllModules.push(...externalExportAllModules);
	}

	log(level: LogLevel, properties: RollupLog, pos: number): void {
		this.addLocationToLogProps(properties, pos);
		this.options.onLog(level, properties);
	}

	render(options: RenderOptions): { source: MagicString; usesTopLevelAwait: boolean } {
		const source = this.magicString.clone();
		this.ast!.render(source, options);
		source.trim();
		const { usesTopLevelAwait } = this.astContext;
		if (usesTopLevelAwait && options.format !== 'es' && options.format !== 'system') {
			return error(logInvalidFormatForTopLevelAwait(this.id, options.format));
		}
		return { source, usesTopLevelAwait };
	}

	// 处理AST
	setSource({
		ast,
		code,
		customTransformCache,
		originalCode,
		originalSourcemap,
		resolvedIds,
		sourcemapChain,
		transformDependencies,
		transformFiles,
		...moduleOptions
	}: TransformModuleJSON & {
		resolvedIds?: ResolvedIdMap;
		transformFiles?: EmittedFile[] | undefined;
	}): void {
		timeStart('generate ast', 3);
		// 下面处理ast时会使用this.info.code
		this.info.code = code;
		this.originalCode = originalCode;
		this.originalSourcemap = originalSourcemap;
		this.sourcemapChain = sourcemapChain;
		if (transformFiles) {
			this.transformFiles = transformFiles;
		}
		this.transformDependencies = transformDependencies;
		this.customTransformCache = customTransformCache;
		this.updateOptions(moduleOptions);
		const moduleAst = ast ?? this.tryParse();

		timeEnd('generate ast', 3);
		timeStart('analyze ast', 3);

		this.resolvedIds = resolvedIds ?? Object.create(null);

		// By default, `id` is the file name. Custom resolvers and loaders
		// can change that, but it makes sense to use it for the source file name
		const fileName = this.id;

		this.magicString = new MagicString(code, {
			filename: (this.excludeFromSourcemap ? null : fileName)!, // don't include plugin helpers in sourcemap
			indentExclusionRanges: []
		});

		this.astContext = {
			addDynamicImport: this.addDynamicImport.bind(this),
			addExport: this.addExport.bind(this),
			addImport: this.addImport.bind(this),
			addImportMeta: this.addImportMeta.bind(this),
			code, // Only needed for debugging
			deoptimizationTracker: this.graph.deoptimizationTracker,
			error: this.error.bind(this),
			fileName, // Needed for warnings
			getExports: this.getExports.bind(this),
			getModuleExecIndex: () => this.execIndex,
			getModuleName: this.basename.bind(this),
			getNodeConstructor: (name: string) => nodeConstructors[name] || nodeConstructors.UnknownNode,
			getReexports: this.getReexports.bind(this),
			importDescriptions: this.importDescriptions,
			includeAllExports: () => this.includeAllExports(true),
			includeDynamicImport: this.includeDynamicImport.bind(this),
			includeVariableInModule: this.includeVariableInModule.bind(this),
			log: this.log.bind(this),
			magicString: this.magicString,
			manualPureFunctions: this.graph.pureFunctions,
			module: this,
			moduleContext: this.context,
			options: this.options,
			requestTreeshakingPass: () => (this.graph.needsTreeshakingPass = true),
			traceExport: (name: string) => this.getVariableForExportName(name)[0],
			traceVariable: this.traceVariable.bind(this),
			usesTopLevelAwait: false
		};

		// 模块作用域， 第一个参数是全局作用域， 也就是图的作用域
		this.scope = new ModuleScope(this.graph.scope, this.astContext);

		// 命名空间， 这里只是声明了一个实例， 并且保存当前的module
		// 后续可能会有进一步的处理
		this.namespace = new NamespaceVariable(this.astContext);
		// 主要处理模块, 根据ast, 填充module的各个字段, 比如Imports/Exports/dynamicImports/ImportMeta等
		this.ast = new Program(moduleAst, { context: this.astContext, type: 'Module' }, this.scope);

		// Assign AST directly if has existing one as there's no way to drop it from memory.
		// If cache is enabled, also assign directly as otherwise it takes more CPU and memory to re-compute.
		if (ast || this.options.cache !== false) {
			this.info.ast = moduleAst;
		} else {
			// Make lazy and apply LRU cache to not hog the memory
			Object.defineProperty(this.info, 'ast', {
				get: () => {
					if (this.graph.astLru.has(fileName)) {
						return this.graph.astLru.get(fileName)!;
					} else {
						const parsedAst = this.tryParse();
						this.graph.astLru.set(fileName, parsedAst);
						return parsedAst;
					}
				}
			});
		}

		timeEnd('analyze ast', 3);
	}

	toJSON(): ModuleJSON {
		return {
			assertions: this.info.assertions,
			ast: this.info.ast!,
			code: this.info.code!,
			customTransformCache: this.customTransformCache,
			// eslint-disable-next-line unicorn/prefer-spread
			dependencies: Array.from(this.dependencies, getId),
			id: this.id,
			meta: this.info.meta,
			moduleSideEffects: this.info.moduleSideEffects,
			originalCode: this.originalCode,
			originalSourcemap: this.originalSourcemap,
			resolvedIds: this.resolvedIds,
			sourcemapChain: this.sourcemapChain,
			syntheticNamedExports: this.info.syntheticNamedExports,
			transformDependencies: this.transformDependencies,
			transformFiles: this.transformFiles
		};
	}

	traceVariable(
		name: string,
		{
			importerForSideEffects,
			isExportAllSearch,
			searchedNamesAndModules
		}: {
			importerForSideEffects?: Module;
			isExportAllSearch?: boolean;
			searchedNamesAndModules?: Map<string, Set<Module | ExternalModule>>;
		} = EMPTY_OBJECT
	): Variable | null {
		const localVariable = this.scope.variables.get(name);
		if (localVariable) {
			return localVariable;
		}

		const importDescription = this.importDescriptions.get(name);
		if (importDescription) {
			const otherModule = importDescription.module;

			if (otherModule instanceof Module && importDescription.name === '*') {
				return otherModule.namespace;
			}

			const [declaration] = getVariableForExportNameRecursive(
				otherModule,
				importDescription.name,
				importerForSideEffects || this,
				isExportAllSearch,
				searchedNamesAndModules
			);

			if (!declaration) {
				return this.error(
					logMissingExport(importDescription.name, this.id, otherModule.id),
					importDescription.start
				);
			}

			return declaration;
		}

		return null;
	}

	updateOptions({
		meta,
		moduleSideEffects,
		syntheticNamedExports
	}: Partial<PartialNull<ModuleOptions>>): void {
		if (moduleSideEffects != null) {
			this.info.moduleSideEffects = moduleSideEffects;
		}
		if (syntheticNamedExports != null) {
			this.info.syntheticNamedExports = syntheticNamedExports;
		}
		if (meta != null) {
			Object.assign(this.info.meta, meta);
		}
	}

	private addDynamicImport(node: ImportExpression) {
		let argument: ExpressionNode | string = node.source;
		if (argument instanceof TemplateLiteral) {
			if (argument.quasis.length === 1 && argument.quasis[0].value.cooked) {
				argument = argument.quasis[0].value.cooked;
			}
		} else if (argument instanceof Literal && typeof argument.value === 'string') {
			// 类似 import('./c'); 这样的语句, 形成的AST ImportExpression 节点会有一个source属性, 类型为Literal
			// 大概是这样
			// "source": {
			// 	"type": "Literal",
			// 	"start": 28,
			// 	"end": 33,
			// 	"value": "./c",
			// 	"raw": "'./c'"
			// }
			// 所以这里的argument.value也就是 './c'
			argument = argument.value;
		}

		// 加入 dynamicImports
		this.dynamicImports.push({ argument, id: null, node, resolution: null });
	}

	private addExport(
		node: ExportAllDeclaration | ExportNamedDeclaration | ExportDefaultDeclaration
	): void {
		if (node instanceof ExportDefaultDeclaration) {
			// export default foo;

			this.exports.set('default', {
				identifier: node.variable.getAssignedVariableName(),
				localName: 'default'
			});
		} else if (node instanceof ExportAllDeclaration) {
			const source = node.source.value;
			this.addSource(source, node);
			if (node.exported) {
				// export * as name from './other'

				const name = node.exported.name;
				this.reexportDescriptions.set(name, {
					localName: '*',
					module: null as never, // filled in later,
					source,
					start: node.start
				});
			} else {
				// export * from './other'

				this.exportAllSources.add(source);
			}
		} else if (node.source instanceof Literal) {
			// export { name } from './other'

			const source = node.source.value;
			this.addSource(source, node);
			for (const { exported, local, start } of node.specifiers) {
				const name = exported instanceof Literal ? exported.value : exported.name;
				this.reexportDescriptions.set(name, {
					localName: local instanceof Literal ? local.value : local.name,
					module: null as never, // filled in later,
					source,
					start
				});
			}
		} else if (node.declaration) {
			const declaration = node.declaration;
			if (declaration instanceof VariableDeclaration) {
				// export var { foo, bar } = ...
				// export var foo = 1, bar = 2;

				for (const declarator of declaration.declarations) {
					for (const localName of extractAssignedNames(declarator.id)) {
						this.exports.set(localName, { identifier: null, localName });
					}
				}
			} else {
				// export function foo () {}

				const localName = (declaration.id as Identifier).name;
				this.exports.set(localName, { identifier: null, localName });
			}
		} else {
			// export { foo, bar, baz }

			for (const { local, exported } of node.specifiers) {
				// except for reexports, local must be an Identifier
				const localName = (local as Identifier).name;
				const exportedName = exported instanceof Identifier ? exported.name : exported.value;
				this.exports.set(exportedName, { identifier: null, localName });
			}
		}
	}

	private addImport(node: ImportDeclaration): void {
		const source = node.source.value;
		this.addSource(source, node);
		for (const specifier of node.specifiers) {
			const name =
				specifier instanceof ImportDefaultSpecifier
					? 'default'
					: specifier instanceof ImportNamespaceSpecifier
					? '*'
					: specifier.imported instanceof Identifier
					? specifier.imported.name
					: specifier.imported.value;
			this.importDescriptions.set(specifier.local.name, {
				module: null as never, // filled in later
				name,
				source,
				start: specifier.start
			});
		}
	}

	private addImportMeta(node: MetaProperty): void {
		this.importMetas.push(node);
	}

	private addLocationToLogProps(properties: RollupLog, pos: number): void {
		properties.id = this.id;
		properties.pos = pos;
		let code = this.info.code;
		const location = locate(code!, pos, { offsetLine: 1 });
		if (location) {
			let { column, line } = location;
			try {
				({ column, line } = getOriginalLocation(this.sourcemapChain, { column, line }));
				code = this.originalCode;
			} catch (error_: any) {
				this.options.onLog(
					LOGLEVEL_WARN,
					logInvalidSourcemapForError(error_, this.id, column, line, pos)
				);
			}
			augmentCodeLocation(properties, { column, line }, code!, this.id);
		}
	}

	private addModulesToImportDescriptions(
		importDescription: ReadonlyMap<string, ImportDescription | ReexportDescription>
	): void {
		for (const specifier of importDescription.values()) {
			const { id } = this.resolvedIds[specifier.source];
			specifier.module = this.graph.modulesById.get(id)!;
		}
	}

	private addRelevantSideEffectDependencies(
		relevantDependencies: Set<Module | ExternalModule>,
		necessaryDependencies: ReadonlySet<Module | ExternalModule>,
		alwaysCheckedDependencies: ReadonlySet<Module | ExternalModule>
	): void {
		const handledDependencies = new Set<Module | ExternalModule>();

		const addSideEffectDependencies = (
			possibleDependencies: ReadonlySet<Module | ExternalModule>
		) => {
			for (const dependency of possibleDependencies) {
				if (handledDependencies.has(dependency)) {
					continue;
				}
				handledDependencies.add(dependency);
				if (necessaryDependencies.has(dependency)) {
					relevantDependencies.add(dependency);
					continue;
				}
				if (!(dependency.info.moduleSideEffects || alwaysCheckedDependencies.has(dependency))) {
					continue;
				}
				if (dependency instanceof ExternalModule || dependency.hasEffects()) {
					relevantDependencies.add(dependency);
					continue;
				}
				addSideEffectDependencies(dependency.dependencies);
			}
		};

		addSideEffectDependencies(this.dependencies);
		addSideEffectDependencies(alwaysCheckedDependencies);
	}

	private addSource(
		source: string,
		declaration: ImportDeclaration | ExportNamedDeclaration | ExportAllDeclaration
	) {
		const parsedAssertions = getAssertionsFromImportExportDeclaration(declaration.assertions);
		const existingAssertions = this.sourcesWithAssertions.get(source);
		if (existingAssertions) {
			if (doAssertionsDiffer(existingAssertions, parsedAssertions)) {
				this.log(
					LOGLEVEL_WARN,
					logInconsistentImportAssertions(existingAssertions, parsedAssertions, source, this.id),
					declaration.start
				);
			}
		} else {
			this.sourcesWithAssertions.set(source, parsedAssertions);
		}
	}

	private getVariableFromNamespaceReexports(
		name: string,
		importerForSideEffects?: Module,
		searchedNamesAndModules?: Map<string, Set<Module | ExternalModule>>
	): [variable: Variable | null, indirectExternal?: boolean] {
		let foundSyntheticDeclaration: SyntheticNamedExportVariable | null = null;
		const foundInternalDeclarations = new Map<Variable, Module>();
		const foundExternalDeclarations = new Set<ExternalVariable>();
		for (const module of this.exportAllModules) {
			// Synthetic namespaces should not hide "regular" exports of the same name
			if (module.info.syntheticNamedExports === name) {
				continue;
			}
			const [variable, indirectExternal] = getVariableForExportNameRecursive(
				module,
				name,
				importerForSideEffects,
				true,
				// We are creating a copy to handle the case where the same binding is
				// imported through different namespace reexports gracefully
				copyNameToModulesMap(searchedNamesAndModules)
			);

			if (module instanceof ExternalModule || indirectExternal) {
				foundExternalDeclarations.add(variable as ExternalVariable);
			} else if (variable instanceof SyntheticNamedExportVariable) {
				if (!foundSyntheticDeclaration) {
					foundSyntheticDeclaration = variable;
				}
			} else if (variable) {
				foundInternalDeclarations.set(variable, module);
			}
		}
		if (foundInternalDeclarations.size > 0) {
			const foundDeclarationList = [...foundInternalDeclarations];
			const usedDeclaration = foundDeclarationList[0][0];
			if (foundDeclarationList.length === 1) {
				return [usedDeclaration];
			}
			this.options.onLog(
				LOGLEVEL_WARN,
				logNamespaceConflict(
					name,
					this.id,
					foundDeclarationList.map(([, module]) => module.id)
				)
			);
			// TODO we are pretending it was not found while it should behave like "undefined"
			return [null];
		}
		if (foundExternalDeclarations.size > 0) {
			const foundDeclarationList = [...foundExternalDeclarations];
			const usedDeclaration = foundDeclarationList[0];
			if (foundDeclarationList.length > 1) {
				this.options.onLog(
					LOGLEVEL_WARN,
					logAmbiguousExternalNamespaces(
						name,
						this.id,
						usedDeclaration.module.id,
						foundDeclarationList.map(declaration => declaration.module.id)
					)
				);
			}
			return [usedDeclaration, true];
		}
		if (foundSyntheticDeclaration) {
			return [foundSyntheticDeclaration];
		}
		return [null];
	}

	private includeAndGetAdditionalMergedNamespaces(): Variable[] {
		const externalNamespaces = new Set<Variable>();
		const syntheticNamespaces = new Set<Variable>();
		for (const module of [this, ...this.exportAllModules]) {
			if (module instanceof ExternalModule) {
				const [externalVariable] = module.getVariableForExportName('*');
				externalVariable.include();
				this.includedImports.add(externalVariable);
				externalNamespaces.add(externalVariable);
			} else if (module.info.syntheticNamedExports) {
				const syntheticNamespace = module.getSyntheticNamespace();
				syntheticNamespace.include();
				this.includedImports.add(syntheticNamespace);
				syntheticNamespaces.add(syntheticNamespace);
			}
		}
		return [...syntheticNamespaces, ...externalNamespaces];
	}

	// 在Graph建立的最后阶段， includeStatements， 会进行tree-shaking
	// 调用每个module的include方法， 然后是this.ast.include, 接着是Program.include(this.ast是一个Program node 实例)
	// Program.include内会遍历AST实例树， 调用每一个节点的include方法
	// 遇到了ImportExpression时会调用下面的函数

	private includeDynamicImport(node: ImportExpression): void {
		const resolution = (
			this.dynamicImports.find(dynamicImport => dynamicImport.node === node) as {
				resolution: string | Module | ExternalModule | undefined;
			}
		).resolution;

		if (resolution instanceof Module) {
			// 将自身添加到 【被动态导入的module】的 includedDynamicImporters 内
			resolution.includedDynamicImporters.push(this);

			const importedNames = this.options.treeshake
				? node.getDeterministicImportedNames()
				: undefined;

			if (importedNames) {
				resolution.includeExportsByNames(importedNames);
			} else {
				resolution.includeAllExports(true);
			}
		}
	}

	private includeVariable(variable: Variable): void {
		const variableModule = variable.module;
		if (variable.included) {
			if (variableModule instanceof Module && variableModule !== this) {
				getAndExtendSideEffectModules(variable, this);
			}
		} else {
			variable.include();
			this.graph.needsTreeshakingPass = true;
			if (variableModule instanceof Module) {
				if (!variableModule.isExecuted) {
					markModuleAndImpureDependenciesAsExecuted(variableModule);
				}
				if (variableModule !== this) {
					const sideEffectModules = getAndExtendSideEffectModules(variable, this);
					for (const module of sideEffectModules) {
						if (!module.isExecuted) {
							markModuleAndImpureDependenciesAsExecuted(module);
						}
					}
				}
			}
		}
	}

	private includeVariableInModule(variable: Variable): void {
		this.includeVariable(variable);
		const variableModule = variable.module;
		if (variableModule && variableModule !== this) {
			this.includedImports.add(variable);
		}
	}

	private shimMissingExport(name: string): void {
		this.options.onLog(LOGLEVEL_WARN, logShimmedExport(this.id, name));
		this.exports.set(name, MISSING_EXPORT_SHIM_DESCRIPTION);
	}

	private tryParse(): acorn.Node {
		try {
			return this.graph.contextParse(this.info.code!);
		} catch (error_: any) {
			return this.error(logParseError(error_, this.id), error_.pos);
		}
	}
}

// if there is a cyclic import in the reexport chain, we should not
// import from the original module but from the cyclic module to not
// mess up execution order.
function setAlternativeExporterIfCyclic(
	variable: Variable,
	importer: Module,
	reexporter: Module
): void {
	if (variable.module instanceof Module && variable.module !== reexporter) {
		const exporterCycles = variable.module.cycles;
		if (exporterCycles.size > 0) {
			const importerCycles = reexporter.cycles;
			for (const cycleSymbol of importerCycles) {
				if (exporterCycles.has(cycleSymbol)) {
					importer.alternativeReexportModules.set(variable, reexporter);
					break;
				}
			}
		}
	}
}

const copyNameToModulesMap = (
	searchedNamesAndModules?: Map<string, Set<Module | ExternalModule>>
): Map<string, Set<Module | ExternalModule>> | undefined =>
	searchedNamesAndModules &&
	// eslint-disable-next-line unicorn/prefer-spread
	new Map(Array.from(searchedNamesAndModules, ([name, modules]) => [name, new Set(modules)]));
