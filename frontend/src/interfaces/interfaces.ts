import { Dispatch, SetStateAction } from 'react';
import Nodee from '../components/VisualizerStage/Canvas/NewNode';
import Node from '../components/VisualizerStage/Canvas/VisualizerNode';
import { ActionCreatorWithPayload } from '@reduxjs/toolkit';
import { TreeNodeInfo } from '@blueprintjs/core';

// NODES
interface NodeInterface {
    id: number;
    conclusion: string;
    rule: string;
    args: string;
    views: string[];
    children: number[];
    parents: number[];
    hiddenNodes?: NodeInterface[];
    descendants: number;
}

interface NodeProps {
    id: number;

    conclusion: string;
    rule: string;
    args: string;

    x: number;
    y: number;

    nHided: number;
    nDescendants: number;
    hiddenNodes: number[];

    selected: boolean;

    color: string;

    setNodeOnFocus: (id: number) => void;
    toggleNodeSelection: (id: number, props: any) => void;
    updateNodePosition: (key: number, x: number, y: number) => void;
    openDrawer: (nodeInfo: NodeInfo, tree?: Array<TreeNode>) => void;
    onDragEnd: () => void;
    createTree: (id: number) => TreeNode[];

    tree?: Array<TreeNode>;
}

// Info passed to the info drawer
interface NodeInfo {
    rule: string;
    args: string;
    conclusion: string;
    nHided: number;
    nDescendants: number;
    hiddenNodes: number[];
}

// CANVAS
// Dividir essas interfaces em funções
interface CanvasProps {
    openDrawer: (nodeInfo: NodeInfo) => void;
}

interface CanvasPropsAndRedux extends CanvasProps {
    proof: NodeInterface[];
    visualInfo: ProofState['visualInfo'];
    hideNodes: ActionCreatorWithPayload<number[], string>;
    unhideNodes: ActionCreatorWithPayload<{ pi: number; hiddens: number[] }, string>;
    foldAllDescendants: ActionCreatorWithPayload<number>;
    setVisualInfo: ActionCreatorWithPayload<ProofState['visualInfo'], string>;
}

interface CanvasState {
    canvasSize: { width: number; height: number };
    stage: { stageScale: number; stageX: number; stageY: number };
    showingNodes: { [id: number]: JSX.Element };
    showingEdges: { [id: string]: JSX.Element };
    nodeOnFocus: number;
    nodesSelected: Array<number>;
    proof: NodeInterface[];
    visualInfo: ProofState['visualInfo'];
}

// NAVBAR
interface NavbarProps {
    setDialogIsOpen: Dispatch<SetStateAction<boolean>>;
    setDialogContent: Dispatch<SetStateAction<string>>;
    setDrawerIsOpen: Dispatch<SetStateAction<boolean>>;
}

interface NavbarPropsAndRedux extends NavbarProps {
    proof: ProofState['proof'];
    dot: string;
    view: string;
    visualInfo: ProofState['visualInfo'];
    hiddenNodes: number[][];
    hideNodes: ActionCreatorWithPayload<number[], string>;
}

// TREENODE
interface TreeNode {
    id: number;
    icon: 'graph';
    label: string;
    secondaryLabel: string;
    rule: string;
    args: string;
    conclusion: string;
    parentId: number;
    descendants: number;
    nHided: number;
    hiddenNodes: number[];
    childNodes: TreeNode[];
    parentsId: number[];
    hasCaret: boolean | undefined;
}

interface TreeProps {
    darkTheme: boolean;
    content: TreeNodeInfo[];
    originalNodeInfo: NodeInfo;
    setNodeInfo: Dispatch<SetStateAction<NodeInfo>>;
}

interface LineProps {
    key: string;
    points: Array<number>;
}

// LET DRAWER
interface letDrawerProps {
    drawerIsOpen: boolean;
    setDrawerIsOpen: Dispatch<SetStateAction<boolean>>;
}

// REDUX STATES
interface ReduxState {
    file: FileState;
    proof: ProofState;
    theme: ThemeState;
}
// PROOFS
interface ProofState {
    proof: NodeInterface[];
    view: 'basic' | 'propositional' | 'full';
    style: 'graph' | 'directory';
    hiddenNodes: number[][];
    letMap: {
        [Key: string]: string;
    };
    visualInfo: {
        [id: number]: {
            color: string;
            x: number;
            y: number;
            selected: boolean;
        };
    };
}
// FILE
interface FileState {
    name: string;
    value: string;
    filesCount: number;
}
//THEME
interface ThemeState {
    value: boolean;
}

export type {
    NodeInterface,
    NodeProps,
    NodeInfo,
    CanvasProps,
    CanvasPropsAndRedux,
    CanvasState,
    NavbarProps,
    NavbarPropsAndRedux,
    TreeNode,
    TreeProps,
    LineProps,
    letDrawerProps,
    ReduxState,
    ProofState,
    FileState,
    ThemeState,
};
