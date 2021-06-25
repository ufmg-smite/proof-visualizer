/* eslint-disable @typescript-eslint/explicit-module-boundary-types */
/* eslint-disable @typescript-eslint/no-explicit-any */
import * as React from 'react';

import { Classes, TreeNodeInfo, Tree } from '@blueprintjs/core';

export class VisualizerTree extends React.Component<
    any,
    { nodes: TreeNodeInfo[]; selected: number; originalNodeInfo: any }
> {
    constructor(props: any) {
        super(props);

        this.state = {
            nodes: props.content,
            selected: NaN,
            originalNodeInfo: props.originalNodeInfo,
        };
    }

    public render(): JSX.Element {
        return (
            <Tree
                contents={this.state.nodes}
                onNodeClick={this.handleNodeClick}
                onNodeCollapse={this.handleNodeCollapse}
                onNodeExpand={this.handleNodeExpand}
                className={Classes.ELEVATION_0}
            />
        );
    }

    private handleNodeClick = (nodeData: any, _nodePath: number[], e: React.MouseEvent<HTMLElement>) => {
        const { setNodeInfo } = this.props;
        setNodeInfo(
            this.state.selected !== nodeData.id
                ? {
                      rule: nodeData.rule ? nodeData.rule : '',
                      args: nodeData.args ? nodeData.args : '',
                      conclusion: nodeData.conclusion ? nodeData.conclusion : '',
                      nHided: 0,
                      nDescendants: nodeData.descendants,
                      topHidedNodes: undefined,
                  }
                : this.state.originalNodeInfo,
        );
        const originallySelected = nodeData.isSelected;
        if (!e.shiftKey) {
            this.forEachNode(this.state.nodes, (n) => (n.isSelected = false));
        }
        nodeData.isSelected = originallySelected == null ? true : !originallySelected;
        this.setState({ ...this.state, selected: this.state.selected === nodeData.id ? NaN : nodeData.id });
    };

    private handleNodeCollapse = (nodeData: TreeNodeInfo) => {
        nodeData.isExpanded = false;
        this.setState(this.state);
    };

    private handleNodeExpand = (nodeData: TreeNodeInfo) => {
        nodeData.isExpanded = true;
        this.setState(this.state);
    };

    private forEachNode(nodes: TreeNodeInfo[], callback: (node: TreeNodeInfo) => void) {
        if (nodes == null) {
            return;
        }

        for (const node of nodes) {
            callback(node);
            this.forEachNode(node.childNodes ? node.childNodes : [], callback);
        }
    }
}
