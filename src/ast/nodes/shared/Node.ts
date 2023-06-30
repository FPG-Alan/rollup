import * as acorn from 'acorn';
import { locate, type Location } from 'locate-character';
import type MagicString from 'magic-string';
import type { AstContext } from '../../../Module';
import { ANNOTATION_KEY, INVALID_COMMENT_KEY } from '../../../utils/pureComments';
import type { NodeRenderOptions, RenderOptions } from '../../../utils/renderHelpers';
import type { Entity } from '../../Entity';
import {
	createHasEffectsContext,
	type HasEffectsContext,
	type InclusionContext
} from '../../ExecutionContext';
import { getAndCreateKeys, keys } from '../../keys';
import type ChildScope from '../../scopes/ChildScope';
import type Variable from '../../variables/Variable';
import * as NodeType from '../NodeType';
import { ExpressionEntity } from './Expression';

export interface GenericEsTreeNode extends acorn.Node {
	[key: string]: any;
}

export const INCLUDE_PARAMETERS = 'variables' as const;
export type IncludeChildren = boolean | typeof INCLUDE_PARAMETERS;

export interface Node extends Entity {
	annotations?: acorn.Comment[];
	context: AstContext;
	end: number;
	esTreeNode: GenericEsTreeNode;
	included: boolean;
	keys: string[];
	needsBoundaries?: boolean;
	parent: Node | { type?: string };
	preventChildBlockScope?: boolean;
	start: number;
	type: string;
	variable?: Variable | null;

	addExportedVariables(
		variables: readonly Variable[],
		exportNamesByVariable: ReadonlyMap<Variable, readonly string[]>
	): void;

	/**
	 * Called once all nodes have been initialised and the scopes have been populated.
	 */
	bind(): void;

	/**
	 * Determine if this Node would have an effect on the bundle.
	 * This is usually true for already included nodes. Exceptions are e.g. break statements
	 * which only have an effect if their surrounding loop or switch statement is included.
	 * The options pass on information like this about the current execution path.
	 */
	hasEffects(context: HasEffectsContext): boolean;

	/**
	 * Includes the node in the bundle. If the flag is not set, children are usually included
	 * if they are necessary for this node (e.g. a function body) or if they have effects.
	 * Necessary variables need to be included as well.
	 */
	include(context: InclusionContext, includeChildrenRecursively: IncludeChildren): void;

	/**
	 * Alternative version of include to override the default behaviour of
	 * declarations to not include the id by default if the declarator has an effect.
	 */
	includeAsSingleStatement(
		context: InclusionContext,
		includeChildrenRecursively: IncludeChildren
	): void;

	render(code: MagicString, options: RenderOptions, nodeRenderOptions?: NodeRenderOptions): void;

	/**
	 * Start a new execution path to determine if this node has an effect on the bundle and
	 * should therefore be included. Included nodes should always be included again in subsequent
	 * visits as the inclusion of additional variables may require the inclusion of more child
	 * nodes in e.g. block statements.
	 */
	shouldBeIncluded(context: InclusionContext): boolean;
}

export type StatementNode = Node;

export interface ExpressionNode extends ExpressionEntity, Node {}

export class NodeBase extends ExpressionEntity implements ExpressionNode {
	declare annotations?: acorn.Comment[];
	context: AstContext;
	declare end: number;
	esTreeNode: acorn.Node;
	keys: string[];
	parent: Node | { context: AstContext; type: string };

	// decalre关键字, 告诉编译器这个属性将会在运行时被赋值
	declare scope: ChildScope;

	// this.start/end 是在parseNode时赋值的
	declare start: number;
	declare type: keyof typeof NodeType;
	// Nodes can apply custom deoptimizations once they become part of the
	// executed code. To do this, they must initialize this as false, implement
	// applyDeoptimizations and call this from include and hasEffects if they
	// have custom handlers
	protected deoptimized?: boolean;

	constructor(
		esTreeNode: GenericEsTreeNode,
		parent: Node | { context: AstContext; type: string },
		parentScope: ChildScope
	) {
		super();
		this.esTreeNode = esTreeNode;
		this.keys = keys[esTreeNode.type] || getAndCreateKeys(esTreeNode);
		this.parent = parent;
		this.context = parent.context;
		this.createScope(parentScope);


		this.parseNode(esTreeNode);

		// 这个函数由子类自行实现
		this.initialise();

		// sourceMap
		this.context.magicString.addSourcemapLocation(this.start);
		this.context.magicString.addSourcemapLocation(this.end);
	}

	addExportedVariables(
		_variables: readonly Variable[],
		_exportNamesByVariable: ReadonlyMap<Variable, readonly string[]>
	): void {}

	/**
	 * Override this to bind assignments to variables and do any initialisations that
	 * require the scopes to be populated with variables.
	 */
	bind(): void {
		for (const key of this.keys) {
			const value = (this as GenericEsTreeNode)[key];
			if (value === null) continue;
			if (Array.isArray(value)) {
				for (const child of value) {
					if (child !== null) child.bind();
				}
			} else {
				value.bind();
			}
		}
	}

	/**
	 * Override if this node should receive a different scope than the parent scope.
	 */
	createScope(parentScope: ChildScope): void {
		this.scope = parentScope;
	}

	hasEffects(context: HasEffectsContext): boolean {
		if (this.deoptimized === false) this.applyDeoptimizations();
		for (const key of this.keys) {
			const value = (this as GenericEsTreeNode)[key];
			if (value === null) continue;
			if (Array.isArray(value)) {
				for (const child of value) {
					if (child !== null && child.hasEffects(context)) return true;
				}
			} else if (value.hasEffects(context)) return true;
		}
		return false;
	}

	include(context: InclusionContext, includeChildrenRecursively: IncludeChildren): void {
		if (this.deoptimized === false) this.applyDeoptimizations();
		this.included = true;
		for (const key of this.keys) {
			const value = (this as GenericEsTreeNode)[key];
			if (value === null) continue;
			if (Array.isArray(value)) {
				for (const child of value) {
					if (child !== null) child.include(context, includeChildrenRecursively);
				}
			} else {
				value.include(context, includeChildrenRecursively);
			}
		}
	}

	includeAsSingleStatement(
		context: InclusionContext,
		includeChildrenRecursively: IncludeChildren
	): void {
		this.include(context, includeChildrenRecursively);
	}

	/**
	 * Override to perform special initialisation steps after the scope is initialised
	 */
	initialise(): void {}

	insertSemicolon(code: MagicString): void {
		if (code.original[this.end - 1] !== ';') {
			code.appendLeft(this.end, ';');
		}
	}

	// 处理[当前]节点
	// 根节点是Program, 递归, 子节点也都是派生自NodeBase, 实例化子节点后还是会执行这个函数
	parseNode(esTreeNode: GenericEsTreeNode): void {
		for (const [key, value] of Object.entries(esTreeNode)) {
			// That way, we can override this function to add custom initialisation and then call super.parseNode
			if (this.hasOwnProperty(key)) continue;

			// 下划线开头, 注释?
			if (key.charCodeAt(0) === 95 /* _ */) {
				if (key === ANNOTATION_KEY) {
					// 是rollup处理的注释, 直接赋值了?
					this.annotations = value;
				} else if (key === INVALID_COMMENT_KEY) {
					// 删除注释
					for (const { start, end } of value as acorn.Comment[])
						this.context.magicString.remove(start, end);
				}
			} else if (typeof value !== 'object' || value === null) {
				// 这种情况不是一个子节点的key, 所以把value放在当前节点上
				(this as GenericEsTreeNode)[key] = value;
			} else if (Array.isArray(value)) {
				(this as GenericEsTreeNode)[key] = [];
				// 可能时子节点, 对子节点都进行实例化
				for (const child of value) {
					(this as GenericEsTreeNode)[key].push(
						child === null
							? null
							: new (this.context.getNodeConstructor(child.type))(child, this, this.scope)
					);
				}
			} else {
				// 子节点, 实例化
				(this as GenericEsTreeNode)[key] = new (this.context.getNodeConstructor(value.type))(
					value,
					this,
					this.scope
				);
			}
		}
	}

	render(code: MagicString, options: RenderOptions): void {
		for (const key of this.keys) {
			const value = (this as GenericEsTreeNode)[key];
			if (value === null) continue;
			if (Array.isArray(value)) {
				for (const child of value) {
					if (child !== null) child.render(code, options);
				}
			} else {
				value.render(code, options);
			}
		}
	}

	shouldBeIncluded(context: InclusionContext): boolean {
		return this.included || (!context.brokenFlow && this.hasEffects(createHasEffectsContext()));
	}

	protected applyDeoptimizations(): void {}
}

export { NodeBase as StatementBase };

export function locateNode(node: Node): Location {
	const location = locate(node.context.code, node.start, { offsetLine: 1 });
	(location as any).file = node.context.fileName;
	location.toString = () => JSON.stringify(location);

	return location;
}

export function logNode(node: Node): string {
	return node.context.code.slice(node.start, node.end);
}
