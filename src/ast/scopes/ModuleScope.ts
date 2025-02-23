import type { AstContext } from '../../Module';
import type { InternalModuleFormat } from '../../rollup/types';
import type ExportDefaultDeclaration from '../nodes/ExportDefaultDeclaration';
import { UNDEFINED_EXPRESSION } from '../values';
import ExportDefaultVariable from '../variables/ExportDefaultVariable';
import GlobalVariable from '../variables/GlobalVariable';
import LocalVariable from '../variables/LocalVariable';
import type Variable from '../variables/Variable';
import ChildScope from './ChildScope';
import type GlobalScope from './GlobalScope';

export default class ModuleScope extends ChildScope {
	readonly context: AstContext;
	declare parent: GlobalScope;

	constructor(parent: GlobalScope, context: AstContext) {
		super(parent);
		this.context = context;
		// module 作用域， 首先是this
		this.variables.set('this', new LocalVariable('this', null, UNDEFINED_EXPRESSION, context));
	}

	addExportDefaultDeclaration(
		name: string,
		exportDefaultDeclaration: ExportDefaultDeclaration,
		context: AstContext
	): ExportDefaultVariable {
		const variable = new ExportDefaultVariable(name, exportDefaultDeclaration, context);
		this.variables.set('default', variable);
		return variable;
	}

	addNamespaceMemberAccess(): void {}

	deconflict(
		format: InternalModuleFormat,
		exportNamesByVariable: ReadonlyMap<Variable, readonly string[]>,
		accessedGlobalsByScope: ReadonlyMap<ChildScope, ReadonlySet<string>>
	): void {
		// all module level variables are already deconflicted when deconflicting the chunk
		for (const scope of this.children)
			scope.deconflict(format, exportNamesByVariable, accessedGlobalsByScope);
	}

	findLexicalBoundary(): this {
		return this;
	}

	findVariable(name: string): Variable {
		const knownVariable = this.variables.get(name) || this.accessedOutsideVariables.get(name);
		if (knownVariable) {
			return knownVariable;
		}
		const variable = this.context.traceVariable(name) || this.parent.findVariable(name);
		if (variable instanceof GlobalVariable) {
			this.accessedOutsideVariables.set(name, variable);
		}
		return variable;
	}
}
