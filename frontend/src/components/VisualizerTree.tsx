/* eslint-disable @typescript-eslint/explicit-module-boundary-types */
/* eslint-disable @typescript-eslint/no-explicit-any */
import * as React from 'react';

import { Classes, Icon, Intent, TreeNodeInfo, Position, Tree } from '@blueprintjs/core';
import { Tooltip2 } from '@blueprintjs/popover2';

export class VisualizerTree extends React.Component<any, { nodes: TreeNodeInfo[] }> {
    constructor(props: any) {
        super(props);

        this.state = {
            nodes: INITIAL_STATE,
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

    private handleNodeClick = (nodeData: TreeNodeInfo, _nodePath: number[], e: React.MouseEvent<HTMLElement>) => {
        const originallySelected = nodeData.isSelected;
        if (!e.shiftKey) {
            this.forEachNode(this.state.nodes, (n) => (n.isSelected = false));
        }
        nodeData.isSelected = originallySelected == null ? true : !originallySelected;
        this.setState(this.state);
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

/* tslint:disable:object-literal-sort-keys so childNodes can come last */
const INITIAL_STATE: TreeNodeInfo[] = [
    {
        id: 0,
        hasCaret: true,
        icon: 'graph',
        label: 'ASSUME => ',
    },
    {
        id: 1,
        icon: 'folder-close',
        isExpanded: true,
        label: (
            <Tooltip2 content="I'm a folder <3" position={Position.RIGHT}>
                Folder 1
            </Tooltip2>
        ),
        childNodes: [
            {
                id: 2,
                icon: 'document',
                label: 'Item 0',
                secondaryLabel: (
                    <Tooltip2 content="An eye!">
                        <Icon icon="eye-open" />
                    </Tooltip2>
                ),
            },
            {
                id: 3,
                icon: <Icon icon="tag" intent={Intent.PRIMARY} className={Classes.TREE_NODE_ICON} />,
                label: 'Organic meditation gluten-free, sriracha VHS drinking vinegar beard man.',
            },
            {
                id: 4,
                hasCaret: true,
                icon: 'folder-close',
                label: (
                    <Tooltip2 content="foo" position={Position.RIGHT}>
                        Folder 2
                    </Tooltip2>
                ),
                childNodes: [
                    { id: 5, label: 'No-Icon Item' },
                    { id: 6, icon: 'tag', label: 'Item 1' },
                    {
                        id: 7,
                        hasCaret: true,
                        icon: 'folder-close',
                        label: 'Folder 3',
                        childNodes: [
                            { id: 8, icon: 'document', label: 'Item 0' },
                            { id: 9, icon: 'tag', label: 'Item 1' },
                        ],
                    },
                ],
            },
        ],
    },
    {
        id: 2,
        hasCaret: true,
        icon: 'folder-close',
        label: 'Super secret files',
        disabled: true,
    },
];
