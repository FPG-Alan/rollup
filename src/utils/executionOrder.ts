import type ExternalModule from '../ExternalModule';
import Module from '../Module';

interface OrderedExecutionUnit {
	execIndex: number;
}

const compareExecIndex = <T extends OrderedExecutionUnit>(unitA: T, unitB: T) =>
	unitA.execIndex > unitB.execIndex ? 1 : -1;

export function sortByExecutionOrder(units: OrderedExecutionUnit[]): void {
	units.sort(compareExecIndex);
}


// 应该是关键了吧
export function analyseModuleExecution(entryModules: readonly Module[]): {
	cyclePaths: string[][];
	orderedModules: Module[];
} {
	let nextExecIndex = 0;
	const cyclePaths: string[][] = [];
	const analysedModules = new Set<Module | ExternalModule>();
	const dynamicImports = new Set<Module>();
	const parents = new Map<Module | ExternalModule, Module | null>();
	const orderedModules: Module[] = [];

	const analyseModule = (module: Module | ExternalModule) => {
		// 模块，不是外部模块
		if (module instanceof Module) {
			for (const dependency of module.dependencies) {
				// 当前模块的依赖是他的父级
				if (parents.has(dependency)) {
					// 然而父级还没有被分析过
					if (!analysedModules.has(dependency)) {
						// 这就是一个循环引用
						cyclePaths.push(getCyclePath(dependency as Module, module, parents));
					}
					continue;
				}
				// 设置当前模块是这个依赖的父级（之一）
				parents.set(dependency, module);
				// 继续分析依赖
				analyseModule(dependency);
			}


			// 只有遇到没有依赖的module， 或者所有依赖都执行完后， 才会执行到这
			for (const dependency of module.implicitlyLoadedBefore) {
				dynamicImports.add(dependency);
			}
			for (const { resolution } of module.dynamicImports) {
				if (resolution instanceof Module) {
					dynamicImports.add(resolution);
				}
			}
			orderedModules.push(module);
		}

		module.execIndex = nextExecIndex++;
		analysedModules.add(module);
	};

	for (const currentEntry of entryModules) {
		if (!parents.has(currentEntry)) {
			parents.set(currentEntry, null);
			analyseModule(currentEntry);
		}
	}
	for (const currentEntry of dynamicImports) {
		if (!parents.has(currentEntry)) {
			parents.set(currentEntry, null);
			analyseModule(currentEntry);
		}
	}

	return { cyclePaths, orderedModules };
}

function getCyclePath(
	module: Module,
	parent: Module,
	parents: ReadonlyMap<Module | ExternalModule, Module | null>
): string[] {
	const cycleSymbol = Symbol(module.id);
	const path = [module.id];
	let nextModule = parent;
	module.cycles.add(cycleSymbol);
	while (nextModule !== module) {
		nextModule.cycles.add(cycleSymbol);
		path.push(nextModule.id);
		nextModule = parents.get(nextModule)!;
	}
	path.push(path[0]);
	path.reverse();
	return path;
}
