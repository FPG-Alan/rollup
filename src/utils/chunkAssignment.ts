import ExternalModule from '../ExternalModule';
import Module from '../Module';
import type { LogHandler } from '../rollup/types';
import { getNewSet, getOrCreate } from './getOrCreate';
import { concatLazy } from './iterators';
import { logOptimizeChunkStatus } from './logs';
import { timeEnd, timeStart } from './timers';

type ChunkDefinitions = { alias: string | null; modules: Module[] }[];

interface ModulesWithDependentEntries {
	dependentEntries: Set<number>;
	modules: Module[];
}

/**
 * At its core, the algorithm first starts from each static or dynamic entry
 * point and then assigns that entry point to all modules than can be reached
 * via static imports. We call this the *dependent entry points* of that
 * module.
 * 从本质上讲，该算法首先从每个静态或动态入口点开始，然后将该入口点分配给通过静态导入
 * 可以到达的所有模块。 我们称之为该模块的*依赖入口点*
 *
 * 所谓的依赖入口点， 我理解是，可以到达当前模块的所有路径
 *
 *
 * Then we group all modules with the same dependent entry points into chunks
 * as those modules will always be loaded together.
 *
 * 然后，我们将具有相同依赖入口点的所有模块分组为块，因为这些模块将始终一起加载。
 *
 * One non-trivial optimization we can apply is that dynamic entries are
 * different from static entries in so far as when a dynamic import occurs,
 * some
 * modules are already in memory. If some of these modules are also
 * dependencies
 * of the dynamic entry, then it does not make sense to create a separate chunk
 * for them. Instead, the dynamic import target can load them from the
 * importing
 * chunk.
 *
 * 我们可以应用的一项重要优化是动态条目，与静态条目不同的是，当发生动态导入时，
 * 某些模块已经在内存中。 如果其中一些模块也是动态条目的依赖项，
 * 那么为它们创建单独的块就没有意义。相反，动态导入目标可以从导入块加载它们。
 *
 * With regard to chunking, if B is implicitly loaded after A, then this can be
 * handled the same way as if there was a dynamic import A => B.
 *
 * 关于分块，如果 B 在 A 之后隐式加载，则可以按照与动态导入 A => B 相同的方式进行处理。
 *
 * Example:
 * Assume A -> B (A imports B), A => C (A dynamically imports C) and C -> B.
 * Then the initial algorithm would assign A into the A chunk, C into the C
 * chunk and B into the AC chunk, i.e. the chunk with the dependent entry
 * points
 * A and C.
 * However we know that C can only be loaded from A, so A and its dependency B
 * must already be in memory when C is loaded. So it is enough to create only
 * two chunks A containing [AB] and C containing [C].
 *
 * So we do not assign the dynamic entry C as dependent entry point to modules
 * that are already loaded.
 * 例子：
 * 假设 A -> B（A 导入 B）、A => C（A 动态导入 C）且 C -> B。
 * 然后初始算法会将 A 分配到 A chunk中，将 C 分配到 C chunk 中
 * B则 进入 AC chunk（即所有具有A和C两个依赖入口点的modules形成的chunk）
 * 然而我们知道C只能从A加载，因此当C加载时A及其依赖项B必须已经在内存中。 因此，
 * 只创建两个包含 [AB] 的块 A 和包含 [C] 的 C 就足够了。
 * 因此，我们不会将动态入口 C 作为依赖入口点分配给已加载的模块。
 *
 * 我的问题是， 这里的 "already loaded" 是如何判断的？ 这里的loaded， 是指在网络上已经
 * "加载的"， 还是在rollup处理chunk时， 在内存中已经"加载的"？
 * 如果是前者， 是不是说， 在处理B时， 他的依赖入口点里面会存在某些模块本身时动态入口点
 * 对于这些动态入口点， 我们需要考虑B在这些入口点加载时，是否已经在内存中了， 如果是的，
 * 那么这些动态入口点不需要被加入到B上。
 *
 * In a more complex example, let us assume that we have entry points X and Y.
 * Further, let us assume
 * X -> A, X -> B, X -> C,
 * Y -> A, Y -> B,
 * A => D,
 * D -> B, D -> C
 * So without dynamic import optimization, the dependent entry points are
 * A: XY, B: DXY, C: DX, D: D, X: X, Y: Y,
 * so we would for now create six chunks.
 * 考虑这种复杂情况， 没有动态导入优化的话， 依赖入口点是
 * A: XY, B: DXY, C: DX, D: D, X: X, Y: Y,
 * 所以我们现在会创建六个chunk。
 *
 * Now D is loaded only after A is loaded. But A is loaded if either X is
 * loaded
 * or Y is loaded. So the modules that are already in memory when D is loaded
 * are the intersection of all modules that X depends on with all modules that
 * Y
 * depends on, which in this case are the modules A and B.
 * We could also say they are all modules that have both X and Y as dependent
 * entry points.
 * D只会在A加载后加载， 但A会在X或Y加载后加载， 因此，加载 D 时已经在内存中的模块是 X
 * 依赖的所有模块与 Y 依赖的所有模块的交集，在本例中是模块 A 和 B。
 * 我们也可以说它们都是 将 X 和 Y 作为依赖入口点的模块。
 *
 * So we can remove D as dependent entry point from A and B, which means they
 * both now have only XY as dependent entry points and can be merged into the
 * same chunk.
 * 因此，我们可以从 A 和 B 的依赖入口点中删除D，这意味着它们现在都只有 XY 作为
 * 依赖入口点，并且可以合并到同一个chunk中。
 *
 * 我的理解
 * 处理动态加载的模块D时， 他有两个静态import， B和C， 按照一般算法， 那
 * B和C两个module就要添加C作为他们的依赖入口点， 但此时
 * 1. D的动态导入者A的依赖入口点是X, Y
 * 2. B的依赖入口点也包括X， Y
 *
 * 因此：
 * 他们的依赖入口点的交集存在， 即为X, Y, 可以推导出， 当D加载时， B一定在内存
 * 中了
 * 所以：
 * D可以不用添加到B的依赖入口点中去。
 *
 * 结果就是， B的依赖入口点去除D后， 只有【X, Y】， 和A的依赖入口点一致， 可以打到
 * 同一个chunk中， 相比之前就少了一个chunk
 *
 * Now let us extend this to the most general case where we have several
 * dynamic
 * importers for one dynamic entry point.
 * 让我们将这个例子拓展到更普遍的情况：一个动态入口点有多个 dynamic importers。
 * 也就是说， 比如上面的例子， 除了A还会有其他的模块E, F，G... 等也会动态加载D
 *
 * In the most general form, it works like this:
 * For each dynamic entry point, we have a number of dynamic importers, which
 * are the modules importing it. Using the previous ideas, we can determine
 * the modules already in memory for each dynamic importer by looking for all
 * modules that have all the dependent entry points of the dynamic importer as
 * dependent entry points.
 * 以上面的例子来说，A或者E, F， G...是一个个"dynamic importer", 我们要寻找这样
 * 一些modules， 他们的依赖入口点**包含**A的所有的依赖入口点。
 *
 * So the modules that are guaranteed to be in memory when the dynamic entry
 * point is loaded are the intersection of the modules already in memory for
 * each dynamic importer.
 * 也就是说， 一个动态入口点D加载时， 能确保在内存中的模块就是每一个动态加载D的模块
 * 依赖的模块的交集。
 *
 * Assuming that A => D and B => D and A has dependent entry points XY and B
 * has
 * dependent entry points YZ, then the modules guaranteed to be in memory are
 * all modules that have at least XYZ as dependent entry points.
 * We call XYZ the *dynamically dependent entry points* of D.
 *
 * A动态导入D，B动态导入D，A的依赖入口点是X, Y， B的依赖入口点是Y,Z
 * 那么D加载时， 能保证在内存中的模块的依赖入口点中应该至少拥有X, Y， Z
 * 我们就把X, Y， Z成为D的 "动态依赖入口点"
 *
 * Now there is one last case to consider: If one of the dynamically dependent
 * entries is itself a dynamic entry, then any module is in memory that either
 * is a dependency of that dynamic entry or again has the dynamic dependent
 * entries of that dynamic entry as dependent entry points.
 * 就是说， 比如上面， A有依赖入口点X, Y， 那如果X也是一个动态入口点， 那么这个时候
 * 在内存里的模块就应该是
 * - 要么是X自己的依赖
 * - 要么跟D一样， 是X的 "动态依赖入口点"
 * 就是递归X， 像考虑D那样考虑X
 *
 * A naive algorithm for this proved to be costly as it contained an O(n^3)
 * complexity with regard to dynamic entries that blew up for very large
 * projects.
 * 事实证明，这种朴素的算法成本高昂，因为它包含关于dynamic entrie 的O(n^3)的复杂度，
 * 涉及到非常大的项目会爆炸。
 *
 * If we have an efficient way to do Set operations, an alternative approach
 * would be to instead collect already loaded modules per dynamic entry. And as
 * all chunks from the initial grouping would behave the same, we can instead
 * collect already loaded chunks for a performance improvement.
 *
 * 如果我们有一种有效的方法来执行 Set 操作，另一种方法是针对每个动态入口， 收集已
 * 加载的模块。
 * 由于初始分组中的所有块的行为都是相同的，因此我们可以收集已加载的块以提高性能。
 *
 * 问题是， 初始分组时什么？ 所有chunk的相同行为时什么？
 *
 *
 * To do that efficiently, need
 * - a Map of dynamic imports per dynamic entry, which contains all dynamic
 *   imports that can be triggered by a dynamic entry
 * 	 动态入口内的所有动态imports map
 * - a Map of static dependencies per entry
 * 	 每个入口的静态依赖 map
 * - a Map of already loaded chunks per entry that we initially populate with
 *   empty Sets for static entries and Sets containing all entries for dynamic
 *   entries
 * 	 每个入口的已加载的chunks map
 *
 * For efficient operations, we assign each entry a numerical index and
 * represent Sets of Chunks as BigInt values where each chunk corresponds to a
 * bit index. Then thw last two maps can be represented as arrays of BigInt
 * values.
 *
 * 为了高效操作，我们为每个entry分配一个数字索引，并将chunk set表示为 BigInt 值，
 * 其中每个块对应于一个位索引。 然后最后两个映射可以表示为 BigInt 值的数组。
 *
 * Then we iterate through each dynamic entry. We set the already loaded modules
 * to the intersection of the previously already loaded modules with the union
 * of the already loaded modules of that chunk with its static dependencies.
 *
 * 然后我们迭代每个动态enty。 我们将已加载的模块设置为先前已加载的模块
 * 与该块的已加载模块及其静态依赖项的并集的交集。
 *
 * If the already loaded modules changed, then we use the Map of dynamic imports
 * per dynamic entry to marks all dynamic entry dependencies as "dirty" and put
 * them back into the iteration. As an additional optimization, we note for
 * each dynamic entry which dynamic dependent entries have changed and only
 * intersect those entries again on subsequent interations.
 *
 * 如果已经加载的模块发生了变化，那么我们使用每个动态条目的动态导入映射将所有动态条目
 * 依赖项标记为“脏”并将它们放回迭代中。 作为一项额外的优化，我们为每个动态条目记录哪些
 * 动态相关条目已更改，并且仅在后续交互中再次与这些条目相交。
 *
 * Then we remove the dynamic entries from the list of dependent entries for
 * those chunks that are already loaded for that dynamic entry and create
 * another round of chunks.
 */
export function getChunkAssignments(
	entries: ReadonlyArray<Module>,
	manualChunkAliasByEntry: ReadonlyMap<Module, string>,
	minChunkSize: number,
	log: LogHandler
): ChunkDefinitions {
	// 暂时不考虑manualChunks的情况, 这俩变量都是空的
	const { chunkDefinitions, modulesInManualChunks } =
		getChunkDefinitionsFromManualChunks(manualChunkAliasByEntry);

	const {
		allEntries,
		dependentEntriesByModule,
		dynamicallyDependentEntriesByDynamicEntry,
		dynamicImportsByEntry
	} = analyzeModuleGraph(entries);

	// Each chunk is identified by its position in this array
	// 这里拿到了最初的chunks， 就是同一组依赖入口点的所有模块
	const initialChunks = getChunksFromDependentEntries(
		getModulesWithDependentEntries(dependentEntriesByModule, modulesInManualChunks)
	);

	// [
	// 	{ dependentEntries: Set(1) { 0 }, modules: [ [Module] ] },
	// 	{ dependentEntries: Set(1) { 1 }, modules: [ [Module] ] },
	// 	{ dependentEntries: Set(2) { 0, 1 }, modules: [ [Module] ] }
	// ]

	console.log(initialChunks);
	// This mutates initialChunks but also clears
	// dynamicallyDependentEntriesByDynamicEntry as side effect
	// 这个函数修改了 initialChunks， 同时也清除了 dynamicallyDependentEntriesByDynamicEntry （作为副作用）
	removeUnnecessaryDependentEntries(
		initialChunks,
		dynamicallyDependentEntriesByDynamicEntry,
		dynamicImportsByEntry,
		allEntries
	);

	chunkDefinitions.push(
		...getOptimizedChunks(
			getChunksFromDependentEntries(initialChunks),
			allEntries.length,
			minChunkSize,
			log
		).map(({ modules }) => ({
			alias: null,
			modules
		}))
	);

	// 返回chunk definitions
	return chunkDefinitions;
}

function getChunkDefinitionsFromManualChunks(
	manualChunkAliasByEntry: ReadonlyMap<Module, string>
): { chunkDefinitions: ChunkDefinitions; modulesInManualChunks: Set<Module> } {
	const chunkDefinitions: ChunkDefinitions = [];
	const modulesInManualChunks = new Set(manualChunkAliasByEntry.keys());
	const manualChunkModulesByAlias: Record<string, Module[]> = Object.create(null);
	for (const [entry, alias] of manualChunkAliasByEntry) {
		addStaticDependenciesToManualChunk(
			entry,
			(manualChunkModulesByAlias[alias] ||= []),
			modulesInManualChunks
		);
	}
	for (const [alias, modules] of Object.entries(manualChunkModulesByAlias)) {
		chunkDefinitions.push({ alias, modules });
	}
	return { chunkDefinitions, modulesInManualChunks };
}

function addStaticDependenciesToManualChunk(
	entry: Module,
	manualChunkModules: Module[],
	modulesInManualChunks: Set<Module>
): void {
	const modulesToHandle = new Set([entry]);
	for (const module of modulesToHandle) {
		modulesInManualChunks.add(module);
		manualChunkModules.push(module);
		for (const dependency of module.dependencies) {
			if (!(dependency instanceof ExternalModule || modulesInManualChunks.has(dependency))) {
				modulesToHandle.add(dependency);
			}
		}
	}
}

/**
 * entries第一层入口点 大部分情况下就一个
 * 这个函数不是递归的
 */
function analyzeModuleGraph(entries: Iterable<Module>): {
	allEntries: ReadonlyArray<Module>;
	dependentEntriesByModule: Map<Module, Set<number>>;
	dynamicImportsByEntry: ReadonlyArray<ReadonlySet<number>>;
	dynamicallyDependentEntriesByDynamicEntry: Map<number, Set<number>>;
} {
	const dynamicEntryModules = new Set<Module>();
	// 每个模块的 [依赖入口点]
	const dependentEntriesByModule: Map<Module, Set<number>> = new Map();
	// 每个入口点内拥有的动态导入模块的集合的数组， 每个模块的动态导入模块形成一个集合， 入口点内所有的模块的动态导入模块形成数组
	const dynamicImportModulesByEntry: Set<Module>[] = [];
	// 所有入口点
	const allEntriesSet = new Set(entries);

	// 入口递增索引
	let entryIndex = 0;

	// 遍历所有入口点
	// 这是一个双循环,
	// 1. 首先每个模块都会经历广度优先搜索, 遍历自己的每一个静态导入,
	// 		对于每个模块, 主要是把当前的入口点的索引放入 dependentEntriesByModule 中
	// 		这个Map的key是模块, value是一个Set, 里面放入了当前模块的所有入口点的索引, 就是注释里的 "依赖入口点"
	// 		还有就是处理动态导入, [具体如何处理动态导入的]
	//
	// 2. 在循环体内, 某个module如果存在动态导入, 导入的模块就会被压入 allEntriesSet 中, 作为一个入口点进入后面的外层循环
	for (const currentEntry of allEntriesSet) {
		// 当前入口点的动态导入模块
		const dynamicImportsForCurrentEntry = new Set<Module>();

		dynamicImportModulesByEntry.push(dynamicImportsForCurrentEntry);

		// 初始化循环集合, 入口点就是内层循环的第一个被处理的模块
		const modulesToHandle = new Set([currentEntry]);
		// 这个循环中, 遇到静态导入的都会被压入modulesToHandle进行下一次循环
		for (const module of modulesToHandle) {
			// 从 dependentEntriesByModule 中拿到 module 的依赖项集合, 如果没有就通过 getNewSet 初始化一个新的
			// getNewSet 就是返回一个空的, 包含数字的集合 (Set<number>)
			// 那么这行代码就是给 [[当前的module的][依赖项集合]] 加上 [当前的入口索引]
			getOrCreate(dependentEntriesByModule, module, getNewSet<number>).add(entryIndex);

			// 遍历当前模块的所有静态导入的module, 加入到待处理队列
			for (const dependency of module.getDependenciesToBeIncluded()) {
				// 如果不是 ExternalModule 就加入 modulesToHandle
				// 等后面的循环内处理
				if (!(dependency instanceof ExternalModule)) {
					modulesToHandle.add(dependency);
				}
			}

			// 遍历动态导入, 为何这里不用 dynamicDependencies ?
			for (const { resolution } of module.dynamicImports) {
				if (
					// 是模块(而非外部模块,字符串, null)...
					// import()能导入字符串这些玩意么...
					resolution instanceof Module &&
					// 动态导入的模块的 includedDynamicImporters 长度大于0
					// 也就是 [有至少一个模块动态导入了这个模块]， 这个是为了健壮性考虑， 这里可以不管
					resolution.includedDynamicImporters.length > 0 &&
					// 动态导入的模块不在 allEntriesSet 中
					!allEntriesSet.has(resolution)
				) {
					// 压入当前入口点的动态导入模块集合
					dynamicEntryModules.add(resolution);
					// 压入 allEntriesSet, 作为入口点进入后续的外层循环
					allEntriesSet.add(resolution);
					// 压入当前入口点的所有动态引入模块
					dynamicImportsForCurrentEntry.add(resolution);
				}
			}
			// implicitlyLoadedBefore 应该是插件行为设置的
			// 插件上下文内有个函数 emitFile, 如果产出了type为chunk的file, 会需要设置implicitlyLoadedBefore
			// blabla的, 我们这里暂时先不管
			for (const dependency of module.implicitlyLoadedBefore) {
				if (!allEntriesSet.has(dependency)) {
					dynamicEntryModules.add(dependency);
					allEntriesSet.add(dependency);
				}
			}
		}
		entryIndex++;
	}

	// 基本上就是除了一开始的入口点， 遇到动态导入的模块就生成一个新的入口点
	const allEntries = [...allEntriesSet];
	const { dynamicEntries, dynamicImportsByEntry } = getDynamicEntries(
		allEntries,
		dynamicEntryModules,
		dynamicImportModulesByEntry
	);
	return {
		allEntries,
		dependentEntriesByModule,

		// 估计是为了后续优化， 收集了动态入口点的导入者的依赖入口点的并集
		dynamicallyDependentEntriesByDynamicEntry: getDynamicallyDependentEntriesByDynamicEntry(
			dependentEntriesByModule,
			dynamicEntries,
			allEntries
		),
		dynamicImportsByEntry
	};
}

function getDynamicEntries(
	allEntries: Module[],
	dynamicEntryModules: Set<Module>,
	dynamicImportModulesByEntry: Set<Module>[]
) {
	const entryIndexByModule = new Map<Module, number>();
	const dynamicEntries = new Set<number>();
	for (const [entryIndex, entry] of allEntries.entries()) {
		entryIndexByModule.set(entry, entryIndex);
		if (dynamicEntryModules.has(entry)) {
			dynamicEntries.add(entryIndex);
		}
	}
	const dynamicImportsByEntry: Set<number>[] = [];
	for (const dynamicImportModules of dynamicImportModulesByEntry) {
		const dynamicImports = new Set<number>();
		for (const dynamicEntry of dynamicImportModules) {
			dynamicImports.add(entryIndexByModule.get(dynamicEntry)!);
		}
		dynamicImportsByEntry.push(dynamicImports);
	}
	return { dynamicEntries, dynamicImportsByEntry };
}

function getDynamicallyDependentEntriesByDynamicEntry(
	dependentEntriesByModule: ReadonlyMap<Module, ReadonlySet<number>>,
	dynamicEntries: ReadonlySet<number>,
	allEntries: ReadonlyArray<Module>
): Map<number, Set<number>> {
	// 每个 动态入口点 的动态加载者的依赖入口点的 [交or并?] 集
	// 这个动态入口点进来的时候， 有哪些模块是确定在内存中了？
	// 是不是所有动态加载这个入口点的模块的依赖入口点的交集？
	const dynamicallyDependentEntriesByDynamicEntry: Map<number, Set<number>> = new Map();

	for (const dynamicEntryIndex of dynamicEntries) {
		const dynamicallyDependentEntries = getOrCreate(
			dynamicallyDependentEntriesByDynamicEntry,
			dynamicEntryIndex,
			getNewSet<number>
		);
		const dynamicEntry = allEntries[dynamicEntryIndex];
		// for in 直接创建好了所有的迭代函数
		// concat lazy内部使用了生成器， 来懒创建迭代器
		for (const importer of concatLazy([
			dynamicEntry.includedDynamicImporters,
			dynamicEntry.implicitlyLoadedAfter
		])) {
			// 遍历某个 importer 的依赖入口点， 一个个的加入到这个set中去
			// 那看来是并集
			for (const entry of dependentEntriesByModule.get(importer)!) {
				dynamicallyDependentEntries.add(entry);
			}
		}
	}
	return dynamicallyDependentEntriesByDynamicEntry;
}

function getChunksFromDependentEntries(
	modulesWithDependentEntries: Iterable<ModulesWithDependentEntries>
): ModulesWithDependentEntries[] {
	const chunkModules: {
		[signature: string]: ModulesWithDependentEntries;
	} = Object.create(null);
	for (const { dependentEntries, modules } of modulesWithDependentEntries) {
		let chunkSignature = 0n;
		for (const entryIndex of dependentEntries) {
			chunkSignature |= 1n << BigInt(entryIndex);
		}
		(chunkModules[String(chunkSignature)] ||= {
			dependentEntries: new Set(dependentEntries),
			modules: []
		}).modules.push(...modules);
	}
	return Object.values(chunkModules);
}

function* getModulesWithDependentEntries(
	dependentEntriesByModule: Map<Module, Set<number>>,
	modulesInManualChunks: Set<Module>
) {
	for (const [module, dependentEntries] of dependentEntriesByModule) {
		if (!modulesInManualChunks.has(module)) {
			yield { dependentEntries, modules: [module] };
		}
	}
}

/**
 * This removes all unnecessary dynamic entries from the dependenEntries in its
 * first argument. It will also consume its second argument, so if
 * dynamicallyDependentEntriesByDynamicEntry is ever needed after this, we
 * should make a copy.
 * 这个函数移除了chunks中的不必要的动态入口点
 * 也会消费第二个参数， 所以后面如果还需要 dynamicallyDependentEntriesByDynamicEntry
 * 我们应该复制一份
 */
function removeUnnecessaryDependentEntries(
	chunks: ModulesWithDependentEntries[],
	dynamicallyDependentEntriesByDynamicEntry: Map<number, Set<number>>,
	dynamicImportsByEntry: ReadonlyArray<ReadonlySet<number>>,
	allEntries: ReadonlyArray<Module>
) {
	// The indices correspond to the indices in allEntries. The chunks correspond
	// to bits in the bigint values where chunk 0 is the lowest bit.

	// 用一个二进制的bigint来表示所有的chunk， chunk0在最低位
	// 先初始化为0
	const staticDependenciesPerEntry: bigint[] = allEntries.map(() => 0n);

	// 每个入口点的， 已经加载的chunk...为什么是chunk？是否等同于module？
	const alreadyLoadedChunksPerEntry: bigint[] = allEntries.map((_entry, entryIndex) =>
		// 如果在动态入口里， 就是-1， 否则就是0
		// -1的二进制是每一位都是1， 为什么要这么初始化， 具体意思是什么
		// 如果不是动态入口点， 比如a， 他的已经加载的chunk就是0， 意思是没有加载任何chunk？
		// 那么动态入口点的-1是指加载了任何模块？？？
		dynamicallyDependentEntriesByDynamicEntry.has(entryIndex) ? -1n : 0n
	);

	// This toggles the bits for each chunk that is a dependency of an entry
	// staticDependenciesPerEntry 的初始值都是0， 所以这一趟下来， 就是都变成掩码
	// 掩码随着遍历所有chunks， 依次左移
	// 那么 staticDependenciesPerEntry[entryIndex] 也随着chunk依次左移
	let chunkMask = 1n;
	// 00000000001
	// 下面这段循环的意义在于， 对每个入口来说， 自己是哪几个chunk的依赖入口点
	// 已 a->b, a=>c, c->b的例子来说，
	// 入口点是a, c,
	// initialChunk, 也就是chunks是
	// 	chunk 0 包含 a, 依赖入口点是 a
	//  chunk 1 包含 c, 依赖入口点是 c
	//  chunk 2 包含 b, 依赖入口点是 a, c

	// 那么 staticDependenciesPerEntry[0] 应该表述为， 入口点a会出现在 chunk 0, chunk 2上， 也就是 000 101 = 5
	// staticDependenciesPerEntry[1] 应该表述为， 入口点c会出现在 chunk 1, chunk 2上， 也就是 000 110 = 6
	for (const { dependentEntries } of chunks) {
		for (const entryIndex of dependentEntries) {
			// 初始值都是0，按位或等同于赋值
			staticDependenciesPerEntry[entryIndex] |= chunkMask;
		}
		// 左移一位之后， 就是
		// 00000000010
		chunkMask <<= 1n;
	}

	// Warning: This will consume dynamicallyDependentEntriesByDynamicEntry.
	// If we no longer want this, we should make a copy here.
	const updatedDynamicallyDependentEntriesByDynamicEntry =
		dynamicallyDependentEntriesByDynamicEntry;

	for (const [
		// 动态入口点的索引
		dynamicEntryIndex,
		// 加载这个动态入口点的模块的依赖入口点的并集
		updatedDynamicallyDependentEntries
	] of updatedDynamicallyDependentEntriesByDynamicEntry) {
		// 消耗掉
		updatedDynamicallyDependentEntriesByDynamicEntry.delete(dynamicEntryIndex);
		// 按照上面初始化， 这里 previousLoadedModules 应该是-1
		const previousLoadedModules = alreadyLoadedChunksPerEntry[dynamicEntryIndex];
		let newLoadedModules = previousLoadedModules;

		// 遍历加载这个动态入口点的模块的依赖入口点并集
		// 最终得到加载这个动态入口点的模块的依赖入口点所在的chunk的交集
		for (const entryIndex of updatedDynamicallyDependentEntries) {
			// newLoadedModules 初始-1， 也就是每个二进制位都是1， 和任何数按位与都是那个数本身
			// 如果有第二轮循环， 就应该两轮循环的交集
			newLoadedModules &=
				// 当前入口出现在哪些chunk里面 和 当前入口已经加载了哪些chunk 按位或
				// 就应该能得到当前入口已经加载了哪些chunk
				staticDependenciesPerEntry[entryIndex] | alreadyLoadedChunksPerEntry[entryIndex];
		}

		// 上面的例子来说的话， newLoadedModules现在应该是 000 101
		// 而 previousLoadedModules 是初始化的 -1， 111 111
		// 两者不等， 进入条件语句块
		console.log(newLoadedModules);
		if (newLoadedModules !== previousLoadedModules) {
			// 当前动态入口被加进来时 已经在内存中的chunk
			alreadyLoadedChunksPerEntry[dynamicEntryIndex] = newLoadedModules;

			// 这里我暂时不明白
			console.log(dynamicImportsByEntry[dynamicEntryIndex]);
			for (const dynamicImport of dynamicImportsByEntry[dynamicEntryIndex]) {
				getOrCreate(
					updatedDynamicallyDependentEntriesByDynamicEntry,
					dynamicImport,
					getNewSet<number>
				).add(dynamicEntryIndex);
			}
		}
	}

	// Remove entries from dependent entries if a chunk is already loaded without
	// that entry.
	chunkMask = 1n;
	for (const { dependentEntries } of chunks) {
		for (const entryIndex of dependentEntries) {
			if ((alreadyLoadedChunksPerEntry[entryIndex] & chunkMask) === chunkMask) {
				dependentEntries.delete(entryIndex);
			}
		}
		chunkMask <<= 1n;
	}
}

interface ChunkDescription {
	/**
	 * These are the atoms (=initial chunks) that are contained in this chunk
	 */
	containedAtoms: bigint;
	/**
	 * The signatures of all atoms that are included in or loaded with this
	 * chunk. This is the intersection of all dependent entry modules. As chunks
	 * are merged, these sets are intersected.
	 */
	correlatedAtoms: bigint;
	dependencies: Set<ChunkDescription>;
	dependentChunks: Set<ChunkDescription>;
	/**
	 * The indices of the entries depending on this chunk
	 */
	dependentEntries: Set<number>;
	modules: Module[];
	pure: boolean;
	size: number;
}

interface ChunkPartition {
	big: Set<ChunkDescription>;
	sideEffectAtoms: bigint;
	sizeByAtom: number[];
	small: Set<ChunkDescription>;
}

/**
 * This function tries to get rid of small chunks by merging them with other
 * chunks.
 *
 * We can only merge chunks safely if after the merge, loading any entry point
 * in any allowed order will not trigger side effects that should not have been
 * triggered. While side effects are usually things like global function calls,
 * global variable mutations or potentially thrown errors, details do not
 * matter here, and we just discern chunks without side effects (pure chunks)
 * from other chunks.
 *
 * As a first step, we assign each pre-generated chunk with side effects a
 * label. I.e. we have side effect "A" if the non-pure chunk "A" is loaded.
 *
 * Now to determine the side effects of loading a chunk, one also has to take
 * the side effects of its dependencies into account. So if A depends on B
 * (A -> B) and both have side effects, loading A triggers effects AB.
 *
 * Now from the previous step we know that each chunk is uniquely determine by
 * the entry points that depend on it and cause it to load, which we will call
 * its dependent entry points.
 *
 * E.g. if X -> A and Y -> A, then the dependent entry points of A are XY.
 * Starting from that idea, we can determine a set of chunks—and thus a set
 * of side effects—that must have been triggered if a certain chunk has been
 * loaded. Basically, it is the intersection of all chunks loaded by the
 * dependent entry points of a given chunk. We call the corresponding side
 * effects the correlated side effects of that chunk.
 *
 * Example:
 * X -> ABC, Y -> ADE, A-> F, B -> D
 * Then taking dependencies into account, X -> ABCDF, Y -> ADEF
 * The intersection is ADF. So we know that when A is loaded, D and F must also
 * be in memory even though neither D nor A is a dependency of the other.
 * If all have side effects, we call ADF the correlated side effects of A. The
 * correlated side effects need to remain constant when merging chunks.
 *
 * In contrast, we have the dependency side effects of A, which represents
 * the side effects we trigger if we directly load A. In this example, the
 * dependency side effects are AF.
 * For entry chunks, dependency and correlated side effects are the same.
 *
 * With these concepts, merging chunks is allowed if the correlated side
 * effects of each entry do not change. Thus, we are allowed to merge two
 * chunks if
 *
 * a) the dependency side effects of each chunk are a subset of the correlated
 *    side effects of the other chunk, so no additional side effects are
 *    triggered for any entry, or
 * b) The dependent entry points of chunk A are a subset of the dependent entry
 *    points of chunk B while the dependency side effects of A are a subset of
 *    the correlated side effects of B. Because in that scenario, whenever A is
 *    loaded, B is loaded as well. But there are cases when B is loaded where A
 *    is not loaded. So if we merge the chunks, all dependency side effects of
 *    A will be added to the correlated side effects of B, and as the latter is
 *    not allowed to change, the former need to be a subset of the latter.
 *
 * Another consideration when merging small chunks into other chunks is to
 * avoid
 * that too much additional code is loaded. This is achieved when the dependent
 * entries of the small chunk are a subset of the dependent entries of the
 * other
 * chunk. Because then when the small chunk is loaded, the other chunk was
 * loaded/in memory anyway, so at most when the other chunk is loaded, the
 * additional size of the small chunk is loaded unnecessarily.
 *
 * So the algorithm performs merges in two passes:
 *
 * 1. First we try to merge small chunks A only into other chunks B if the
 *    dependent entries of A are a subset of the dependent entries of B and the
 *    dependency side effects of A are a subset of the correlated side effects
 *    of B.
 * 2. Only then for all remaining small chunks, we look for arbitrary merges
 *    following the rule (a), starting with the smallest chunks to look for
 *    possible merge targets.
 */
function getOptimizedChunks(
	initialChunks: ModulesWithDependentEntries[],
	numberOfEntries: number,
	minChunkSize: number,
	log: LogHandler
): { modules: Module[] }[] {
	timeStart('optimize chunks', 3);
	const chunkPartition = getPartitionedChunks(initialChunks, numberOfEntries, minChunkSize);
	if (!chunkPartition) {
		timeEnd('optimize chunks', 3);
		return initialChunks; // the actual modules
	}
	minChunkSize > 1 &&
		log(
			'info',
			logOptimizeChunkStatus(initialChunks.length, chunkPartition.small.size, 'Initially')
		);
	mergeChunks(chunkPartition, minChunkSize);
	minChunkSize > 1 &&
		log(
			'info',
			logOptimizeChunkStatus(
				chunkPartition.small.size + chunkPartition.big.size,
				chunkPartition.small.size,
				'After merging chunks'
			)
		);
	timeEnd('optimize chunks', 3);
	return [...chunkPartition.small, ...chunkPartition.big];
}

function getPartitionedChunks(
	initialChunks: ModulesWithDependentEntries[],
	numberOfEntries: number,
	minChunkSize: number
): ChunkPartition | null {
	const smallChunks: ChunkDescription[] = [];
	const bigChunks: ChunkDescription[] = [];
	const chunkByModule = new Map<Module, ChunkDescription>();
	const sizeByAtom: number[] = [];
	let sideEffectAtoms = 0n;
	let containedAtoms = 1n;
	for (const { dependentEntries, modules } of initialChunks) {
		const chunkDescription: ChunkDescription = {
			containedAtoms,
			correlatedAtoms: 0n,
			dependencies: new Set(),
			dependentChunks: new Set(),
			dependentEntries,
			modules,
			pure: true,
			size: 0
		};
		let size = 0;
		let pure = true;
		for (const module of modules) {
			chunkByModule.set(module, chunkDescription);
			// Unfortunately, we cannot take tree-shaking into account here because
			// rendering did not happen yet, but we can detect empty modules
			if (module.isIncluded()) {
				pure &&= !module.hasEffects();
				// we use a trivial size for the default minChunkSize to improve
				// performance
				size += minChunkSize > 1 ? module.estimateSize() : 1;
			}
		}
		chunkDescription.pure = pure;
		chunkDescription.size = size;
		sizeByAtom.push(size);
		if (!pure) {
			sideEffectAtoms |= containedAtoms;
		}
		(size < minChunkSize ? smallChunks : bigChunks).push(chunkDescription);
		containedAtoms <<= 1n;
	}
	// If there are no small chunks, we will not optimize
	if (smallChunks.length === 0) {
		return null;
	}
	sideEffectAtoms |= addChunkDependenciesAndAtomsAndGetSideEffectAtoms(
		[bigChunks, smallChunks],
		chunkByModule,
		numberOfEntries,
		containedAtoms
	);
	return {
		big: new Set(bigChunks),
		sideEffectAtoms,
		sizeByAtom,
		small: new Set(smallChunks)
	};
}

function mergeChunks(chunkPartition: ChunkPartition, minChunkSize: number) {
	const { small } = chunkPartition;
	for (const mergedChunk of small) {
		const bestTargetChunk = findBestMergeTarget(
			mergedChunk,
			chunkPartition,
			// In the default case, we do not accept size increases
			minChunkSize <= 1 ? 1 : Infinity
		);
		if (bestTargetChunk) {
			const { containedAtoms, correlatedAtoms, modules, pure, size } = mergedChunk;
			small.delete(mergedChunk);
			getChunksInPartition(bestTargetChunk, minChunkSize, chunkPartition).delete(bestTargetChunk);
			bestTargetChunk.modules.push(...modules);
			bestTargetChunk.size += size;
			bestTargetChunk.pure &&= pure;
			const { dependencies, dependentChunks, dependentEntries } = bestTargetChunk;
			bestTargetChunk.correlatedAtoms &= correlatedAtoms;
			bestTargetChunk.containedAtoms |= containedAtoms;
			for (const entry of mergedChunk.dependentEntries) {
				dependentEntries.add(entry);
			}
			for (const dependency of mergedChunk.dependencies) {
				dependencies.add(dependency);
				dependency.dependentChunks.delete(mergedChunk);
				dependency.dependentChunks.add(bestTargetChunk);
			}
			for (const dependentChunk of mergedChunk.dependentChunks) {
				dependentChunks.add(dependentChunk);
				dependentChunk.dependencies.delete(mergedChunk);
				dependentChunk.dependencies.add(bestTargetChunk);
			}
			dependencies.delete(bestTargetChunk);
			dependentChunks.delete(bestTargetChunk);
			getChunksInPartition(bestTargetChunk, minChunkSize, chunkPartition).add(bestTargetChunk);
		}
	}
}

function addChunkDependenciesAndAtomsAndGetSideEffectAtoms(
	chunkLists: ChunkDescription[][],
	chunkByModule: Map<Module, ChunkDescription>,
	numberOfEntries: number,
	nextAtomSignature: bigint
): bigint {
	const signatureByExternalModule = new Map<ExternalModule, bigint>();
	let sideEffectAtoms = 0n;
	const atomsByEntry: bigint[] = [];
	for (let index = 0; index < numberOfEntries; index++) {
		atomsByEntry.push(0n);
	}
	for (const chunks of chunkLists) {
		chunks.sort(compareChunkSize);
		for (const chunk of chunks) {
			const { dependencies, dependentEntries, modules } = chunk;
			for (const module of modules) {
				for (const dependency of module.getDependenciesToBeIncluded()) {
					if (dependency instanceof ExternalModule) {
						if (dependency.info.moduleSideEffects) {
							chunk.containedAtoms |= getOrCreate(signatureByExternalModule, dependency, () => {
								const signature = nextAtomSignature;
								nextAtomSignature <<= 1n;
								sideEffectAtoms |= signature;
								return signature;
							});
						}
					} else {
						const dependencyChunk = chunkByModule.get(dependency);
						if (dependencyChunk && dependencyChunk !== chunk) {
							dependencies.add(dependencyChunk);
							dependencyChunk.dependentChunks.add(chunk);
						}
					}
				}
			}
			const { containedAtoms } = chunk;
			for (const entryIndex of dependentEntries) {
				atomsByEntry[entryIndex] |= containedAtoms;
			}
		}
	}
	for (const chunks of chunkLists) {
		for (const chunk of chunks) {
			const { dependentEntries } = chunk;
			// Correlated atoms are the intersection of all entry atoms
			chunk.correlatedAtoms = -1n;
			for (const entryIndex of dependentEntries) {
				chunk.correlatedAtoms &= atomsByEntry[entryIndex];
			}
		}
	}
	return sideEffectAtoms;
}

function findBestMergeTarget(
	mergedChunk: ChunkDescription,
	{ big, sideEffectAtoms, sizeByAtom, small }: ChunkPartition,
	smallestAdditionalSize: number
): ChunkDescription | null {
	let bestTargetChunk: ChunkDescription | null = null;
	// In the default case, we do not accept size increases
	for (const targetChunk of concatLazy([small, big])) {
		if (mergedChunk === targetChunk) continue;
		const additionalSizeAfterMerge = getAdditionalSizeAfterMerge(
			mergedChunk,
			targetChunk,
			smallestAdditionalSize,
			sideEffectAtoms,
			sizeByAtom
		);
		if (additionalSizeAfterMerge < smallestAdditionalSize) {
			bestTargetChunk = targetChunk;
			if (additionalSizeAfterMerge === 0) break;
			smallestAdditionalSize = additionalSizeAfterMerge;
		}
	}
	return bestTargetChunk;
}

function getChunksInPartition(
	chunk: ChunkDescription,
	minChunkSize: number,
	chunkPartition: ChunkPartition
): Set<ChunkDescription> {
	return chunk.size < minChunkSize ? chunkPartition.small : chunkPartition.big;
}

function compareChunkSize(
	{ size: sizeA }: ChunkDescription,
	{ size: sizeB }: ChunkDescription
): number {
	return sizeA - sizeB;
}

/**
 * Determine the additional unused code size that would be added by merging the
 * two chunks. This is not an exact measurement but rather an upper bound. If
 * the merge produces cycles or adds non-correlated side effects, `Infinity`
 * is returned.
 * Merging will not produce cycles if none of the direct non-merged
 * dependencies of a chunk have the other chunk as a transitive dependency.
 */
function getAdditionalSizeAfterMerge(
	mergedChunk: ChunkDescription,
	targetChunk: ChunkDescription,
	// The maximum additional unused code size allowed to be added by the merge,
	// taking dependencies into account, needs to be below this number
	currentAdditionalSize: number,
	sideEffectAtoms: bigint,
	sizeByAtom: number[]
): number {
	const firstSize = getAdditionalSizeIfNoTransitiveDependencyOrNonCorrelatedSideEffect(
		mergedChunk,
		targetChunk,
		currentAdditionalSize,
		sideEffectAtoms,
		sizeByAtom
	);
	return firstSize < currentAdditionalSize
		? firstSize +
				getAdditionalSizeIfNoTransitiveDependencyOrNonCorrelatedSideEffect(
					targetChunk,
					mergedChunk,
					currentAdditionalSize - firstSize,
					sideEffectAtoms,
					sizeByAtom
				)
		: Infinity;
}

function getAdditionalSizeIfNoTransitiveDependencyOrNonCorrelatedSideEffect(
	dependentChunk: ChunkDescription,
	dependencyChunk: ChunkDescription,
	currentAdditionalSize: number,
	sideEffectAtoms: bigint,
	sizeByAtom: number[]
): number {
	const { correlatedAtoms } = dependencyChunk;
	let dependencyAtoms = dependentChunk.containedAtoms;
	const dependentContainedSideEffects = dependencyAtoms & sideEffectAtoms;
	if ((correlatedAtoms & dependentContainedSideEffects) !== dependentContainedSideEffects) {
		return Infinity;
	}
	const chunksToCheck = new Set(dependentChunk.dependencies);
	for (const { dependencies, containedAtoms } of chunksToCheck) {
		dependencyAtoms |= containedAtoms;
		const containedSideEffects = containedAtoms & sideEffectAtoms;
		if ((correlatedAtoms & containedSideEffects) !== containedSideEffects) {
			return Infinity;
		}
		for (const dependency of dependencies) {
			if (dependency === dependencyChunk) {
				return Infinity;
			}
			chunksToCheck.add(dependency);
		}
	}
	return getAtomsSizeIfBelowLimit(
		dependencyAtoms & ~correlatedAtoms,
		currentAdditionalSize,
		sizeByAtom
	);
}

function getAtomsSizeIfBelowLimit(
	atoms: bigint,
	currentAdditionalSize: number,
	sizeByAtom: number[]
): number {
	let size = 0;
	let atomIndex = 0;
	let atomSignature = 1n;
	const { length } = sizeByAtom;
	for (; atomIndex < length; atomIndex++) {
		if ((atoms & atomSignature) === atomSignature) {
			size += sizeByAtom[atomIndex];
		}
		atomSignature <<= 1n;
		if (size >= currentAdditionalSize) {
			return Infinity;
		}
	}
	return size;
}
