import { Dispatch, SetStateAction } from 'react';
import Node from '../components/VisualizerStage/Canvas/VisualizerNode';
import { ActionCreatorWithPayload } from '@reduxjs/toolkit';

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
    proofNodes: Array<NodeInterface>;
    openDrawer: (nodeInfo: NodeInfo) => void;
    view?: string;
    importedData: {
        nodes: Array<{ id: number; color: string; x: number; y: number; hidden: Array<number> }>;
    };
}

interface CanvasState {
    canvasSize: { width: number; height: number };
    stage: { stageScale: number; stageX: number; stageY: number };
    showingNodes: { [id: number]: Node };
    showingEdges: { [id: string]: JSX.Element };
    nodeOnFocus: number;
    nodesSelected: Array<number>;
    proof: NodeInterface[];
    visualInfo: ProofState['visualInfo'];
}

interface CanvasPropsAndRedux {
    proof: NodeInterface[];
    visualInfo: ProofState['visualInfo'];
    myView: 'basic' | 'propositional' | 'full';
    proofNodes: NodeInterface[];
    openDrawer: (nodeInfo: NodeInfo) => void;
    view: string | undefined;
    importedData: {
        nodes: Array<{ id: number; color: string; x: number; y: number; hidden: Array<number> }>;
    };
    hideNodes: ActionCreatorWithPayload<number[], string>;
    unhideNodes: ActionCreatorWithPayload<{ pi: number; hiddens: number[] }, string>;
    foldAllDescendants: ActionCreatorWithPayload<number>;
    setVisualInfo: ActionCreatorWithPayload<ProofState['visualInfo']>;
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

// NAVBAR
interface VisualizerNavbarProps {
    setDialogIsOpen: Dispatch<SetStateAction<boolean>>;
    setDialogContent: Dispatch<SetStateAction<string>>;
    setDrawerIsOpen: Dispatch<SetStateAction<boolean>>;
    downloadProof: (dot: string, proofName: string) => void;
    runCommands: (command: string) => void;
}

// TREENODE
interface TreeNode {
    id: number;
    icon: 'graph';
    parentId: number;
    label: string;
    descendants: number;
    childNodes: TreeNode[];
    rule: string;
    conclusion: string;
    args: string;
}

interface LineProps {
    key: string;
    points: Array<number>;
}

export type {
    CanvasProps,
    CanvasState,
    LineProps,
    NodeInterface,
    NodeProps,
    NodeInfo,
    ProofState,
    VisualizerNavbarProps,
    TreeNode,
    CanvasPropsAndRedux,
};
