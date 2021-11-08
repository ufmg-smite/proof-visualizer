import { ObjectID } from 'mongodb';
import { Dispatch, SetStateAction } from 'react';
import { MaybeElement } from '@blueprintjs/core/lib/esm/common/props';
import { IconName } from '@blueprintjs/core/lib/esm/components/icon/icon';
import Node from '../VisualizerStage/Canvas/VisualizerNode';
import { ActionCreatorWithPayload } from '@reduxjs/toolkit';

// Dividir essas interfaces em funções
interface CanvasProps {
    proofNodes: Array<NodeInterface>;
    openDrawer: (nodeInfo: {
        rule: string;
        args: string;
        conclusion: string;
        nHided: number;
        nDescendants: number;
    }) => void;
    view?: string;
    importedData: {
        nodes: Array<{ id: number; color: string; x: number; y: number; hidden: Array<number> }>;
    };
}

interface CanvasState {
    canvasSize: { width: number; height: number };
    stage: { stageScale: number; stageX: number; stageY: number };
    proofNodes: Array<NodeInterface>;
    showingNodes: { [id: number]: Node };
    showingEdges: { [id: string]: JSX.Element };
    nodeOnFocus: number;
    nodesSelected: Array<number>;
    myProofState: NodeInterfaceT[];
}

interface NodeInterfaceT {
    id: number;
    conclusion: string;
    rule: string;
    args: string;
    views: Array<string>;
    children: number[];
    parents: number[];
    hiddenNodes?: Array<NodeInterfaceT>;
}

interface DialogProps {
    icon: IconName | MaybeElement;
    title: React.ReactNode;
}

interface FormNewProofProps {
    proof: proof;
    setProof: Dispatch<SetStateAction<proof>>;
}

interface LineProps {
    key: string;
    points: Array<number>;
}

// Mudar nome
interface NodeInterface {
    id: number;

    conclusion: string;
    rule: string;
    args: string;
    views: Array<string>;
    children: Array<number>;
    parent: number;
    descendants: number;
    rank: number;

    positionCache: boolean;
    x: number;
    y: number;

    hided: boolean;
    hidedIn: number;

    // The node that hide its children
    hideMyChildNode: number;

    hidedNodes: Array<number>;

    topHidedNodes?: Array<[number, string, string, number, number]>;

    replace?: number;

    tree?: Array<TreeNode>;

    color: string;
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

    selected: boolean;

    topHidedNodes?: Array<[number, string, string, number, number]>;

    color: string;

    setNodeOnFocus: (id: number) => void;
    toggleNodeSelection: (id: number, props: any) => void;
    updateNodeState: (key: number, x: number, y: number) => void;
    unfoldOnClick: (id: number) => void;
    openDrawer: (
        nodeInfo: {
            rule: string;
            args: string;
            conclusion: string;
            nHided: number;
            nDescendants: number;
            topHidedNodes?: Array<[number, string, string, number, number]>;
        },
        tree?: Array<TreeNode>,
    ) => void;

    tree?: Array<TreeNode>;
}

interface proof {
    _id?: ObjectID;
    label: string;
    options?: string;
    problem: string;
    dot?: string;
    view?: string;
}

interface VisualizerDialogProps {
    dialogIsOpen: boolean;
    setDialogIsOpen: Dispatch<SetStateAction<boolean>>;
    dialogContent: string;
    setDialogContent: Dispatch<SetStateAction<string>>;
    addErrorToast: (err: string) => void;
}

interface VisualizerNavbarProps {
    setDialogIsOpen: Dispatch<SetStateAction<boolean>>;
    setDialogContent: Dispatch<SetStateAction<string>>;
    setDrawerIsOpen: Dispatch<SetStateAction<boolean>>;
    downloadProof: (dot: string, proofName: string) => void;
    runCommands: (command: string) => void;
}

interface stateInterface {
    proofReducer: {
        proof: proof;
    };
    darkThemeReducer: {
        darkTheme: boolean;
    };
    styleReducer: {
        style: string;
    };
    letMapReducer: {
        letMap: {
            [Key: string]: string;
        };
    };
    importedDataReducer: {
        importedData: {
            nodes: Array<{ id: number; color: string; x: number; y: number; hidden: Array<number> }>;
        };
    };
}

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

interface NodeInterfaceT {
    id: number;
    conclusion: string;
    rule: string;
    args: string;
    views: Array<string>;
    children: number[];
    parents: number[];
    hiddenNodes?: Array<NodeInterfaceT>;
}

interface CanvasPropsAndRedux {
    myProof: NodeInterfaceT[];
    myView: 'basic' | 'propositional' | 'full';
    proofNodes: NodeInterface[];
    openDrawer: (nodeInfo: {
        rule: string;
        args: string;
        conclusion: string;
        nHided: number;
        nDescendants: number;
    }) => void;
    view: string | undefined;
    importedData: {
        nodes: Array<{ id: number; color: string; x: number; y: number; hidden: Array<number> }>;
    };
    hideNodes: ActionCreatorWithPayload<number[], string>;
    unhideNodes: ActionCreatorWithPayload<number[], string>;
    foldAllDescendants: ActionCreatorWithPayload<number>;
}

export type {
    CanvasProps,
    CanvasState,
    DialogProps,
    FormNewProofProps,
    LineProps,
    NodeInterface,
    NodeProps,
    proof,
    VisualizerDialogProps,
    VisualizerNavbarProps,
    stateInterface,
    TreeNode,
    CanvasPropsAndRedux,
    NodeInterfaceT,
};
