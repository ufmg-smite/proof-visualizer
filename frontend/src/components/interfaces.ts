import { ObjectID } from 'mongodb';
import { Dispatch, SetStateAction } from 'react';
import { MaybeElement } from '@blueprintjs/core/lib/esm/common/props';
import { IconName } from '@blueprintjs/core/lib/esm/components/icon/icon';
import Node from '../components/canvas/VisualizerNode';

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
}

interface CanvasState {
    canvasSize: { width: number; height: number };
    stage: { stageScale: number; stageX: number; stageY: number };
    proofNodes: Array<NodeInterface>;
    showingNodes: { [id: number]: Node };
    showingEdges: { [id: string]: JSX.Element };
    nodeOnFocus: number;
    nodesSelected: Array<number>;
}

interface DialogProps {
    icon: IconName | MaybeElement;
    title: React.ReactNode;
}

interface ElementProofListProps {
    proof: proof;
    deleteProof: (id: ObjectID | undefined, name: string) => void;
    editProof: (proof: proof) => void;
    setProof: (proof: proof) => void;
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

    tree?: any;
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

    setNodeOnFocus: (id: number) => void;
    toggleNodeSelection: (id: number) => void;
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
        tree: any,
    ) => void;

    tree?: any;
}

interface proof {
    _id?: ObjectID;
    label: string;
    options?: string;
    problem: string;
    dot?: string;
    view?: string;
}

interface ProofListProps {
    addDeleteToast: (err: string) => void;
    setDialogIsOpen: Dispatch<SetStateAction<boolean>>;
    setDialogContent: Dispatch<SetStateAction<string>>;
    setProof: Dispatch<SetStateAction<proof>>;
}

interface VisualizerDialogProps {
    dialogIsOpen: boolean;
    setDialogIsOpen: Dispatch<SetStateAction<boolean>>;
    dialogContent: string;
    setDialogContent: Dispatch<SetStateAction<string>>;
    addErrorToast: (err: string) => void;
    addDeleteToast: (err: string) => void;
}

interface VisualizerNavbarProps {
    setDialogIsOpen: Dispatch<SetStateAction<boolean>>;
    setDialogContent: Dispatch<SetStateAction<string>>;
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
}

export type {
    CanvasProps,
    CanvasState,
    DialogProps,
    ElementProofListProps,
    FormNewProofProps,
    LineProps,
    NodeInterface,
    NodeProps,
    proof,
    ProofListProps,
    VisualizerDialogProps,
    VisualizerNavbarProps,
    stateInterface,
};
