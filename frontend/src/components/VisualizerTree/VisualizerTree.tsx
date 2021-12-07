/* eslint-disable @typescript-eslint/explicit-module-boundary-types */
/* eslint-disable @typescript-eslint/no-explicit-any */
import React, { useEffect, useReducer, useState } from 'react';

import { Classes, Tree, TreeNodeInfo } from '@blueprintjs/core';
import { TreeProps } from '../../interfaces/interfaces';

const VisualizerTree: React.FC<TreeProps> = ({ darkTheme, content, originalNodeInfo, setNodeInfo }: TreeProps) => {
    // STATES:
    const [, forceUpdate] = useReducer((x) => x + 1, 0);
    const [nodes, setNodes] = useState(content);
    const [selected, setSelected] = useState(NaN);

    // USE EFFECT:
    useEffect(() => setNodes(content), [content]);

    // UTILS:
    const forEachNode = (nodes: TreeNodeInfo[], callback: (node: TreeNodeInfo) => void) => {
        if (nodes == null) {
            return;
        }

        for (const node of nodes) {
            callback(node);
            forEachNode(node.childNodes ? node.childNodes : [], callback);
        }
    };

    const handleNodeClick = (nodeData: any, _nodePath: number[], e: React.MouseEvent<HTMLElement>) => {
        setNodeInfo(
            selected !== nodeData.id
                ? {
                      rule: nodeData.rule ? nodeData.rule : '',
                      args: nodeData.args ? nodeData.args : '',
                      conclusion: nodeData.conclusion ? nodeData.conclusion : '',
                      nHided: nodeData.nHided ? nodeData.nHided : 0,
                      nDescendants: nodeData.descendants,
                      hiddenNodes: nodeData.hiddenNodes,
                  }
                : originalNodeInfo,
        );
        const originallySelected = nodeData.isSelected;

        // Set all the nodes to be not selected
        if (!e.shiftKey) forEachNode(nodes, (n) => (n.isSelected = false));

        nodeData.isSelected = originallySelected == null ? true : !originallySelected;
        setSelected(selected === nodeData.id ? NaN : nodeData.id);
    };

    const handleNodeCollapse = (nodeData: TreeNodeInfo) => {
        nodeData.isExpanded = false;
        forceUpdate();
    };

    const handleNodeExpand = (nodeData: TreeNodeInfo) => {
        nodeData.isExpanded = true;
        forceUpdate();
    };

    return (
        <div style={{ backgroundColor: darkTheme ? '#394b59' : 'white' }}>
            <Tree
                contents={nodes}
                onNodeClick={handleNodeClick}
                onNodeCollapse={handleNodeCollapse}
                onNodeExpand={handleNodeExpand}
                className={Classes.ELEVATION_0}
            />
        </div>
    );
};

export default VisualizerTree;
