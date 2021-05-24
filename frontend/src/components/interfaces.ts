import { ObjectID } from 'mongodb';
import { Dispatch, SetStateAction } from 'react';
import { MaybeElement } from '@blueprintjs/core/lib/esm/common/props';
import { IconName } from '@blueprintjs/core/lib/esm/components/icon/icon';
import Node from '../components/canvas/VisualizerNode';

interface OnClickArgs {
    id: number;
    x: number;
    y: number;
}

interface NodeProps {
    id: number;

    conclusion: string;
    rule: string;

    showingChildren: boolean;

    hasChildren: boolean;
    hidingNode?: boolean;

    x: number;
    y: number;

    selected: boolean;

    onClick: (arg0: OnClickArgs) => void;
    setFocusText: Dispatch<SetStateAction<string>>;
    setNodeOnFocus: (id: number) => void;
    toggleNodeSelection: (id: number) => void;
    updateNodeState: (key: number, x: number, y: number) => void;
}

interface LineProps {
    key: string;
    points: Array<number>;
}

interface NodeInterface {
    id: number;

    conclusion: string;
    rule: string;
    views: Array<string>;
    children: Array<number>;
    parent: number;

    positionCache: boolean;
    x: number;
    y: number;

    hided: boolean;
    hidedIn: number;

    showingChildren: boolean;

    // The node that hide its children
    hideMyChildNode: number;

    hidedNodes: Array<number>;
}

interface proof {
    _id?: ObjectID;
    label: string;
    options?: string;
    problem: string;
    dot?: string;
}

interface ElementProofListProps {
    proof: proof;
    deleteProof: (id: ObjectID | undefined, name: string) => void;
    setDot: (proof: proof) => void;
}

interface FormNewProofProps {
    proof: proof;
    setProof: Dispatch<SetStateAction<proof>>;
}

interface ProofListProps {
    addDeleteToast: (err: string) => void;
    setDialogIsOpen: Dispatch<SetStateAction<boolean>>;
}

interface VisualizerDialogProps {
    darkTheme: boolean;
    dialogIsOpen: boolean;
    setDialogIsOpen: Dispatch<SetStateAction<boolean>>;
    dialogContent: string;
    setDialogContent: Dispatch<SetStateAction<string>>;
    addErrorToast: (err: string) => void;
    addDeleteToast: (err: string) => void;
}

interface DialogProps {
    icon: IconName | MaybeElement;
    title: React.ReactNode;
}

interface VisualizerNavbarProps {
    darkTheme: boolean;
    setDarkTheme: Dispatch<SetStateAction<boolean>>;
    setDialogIsOpen: Dispatch<SetStateAction<boolean>>;
    setDialogContent: Dispatch<SetStateAction<string>>;
}

interface CanvasProps {
    proofNodes: Array<NodeInterface>;
    setFocusText: Dispatch<SetStateAction<string>>;
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

interface proofState {
    label: string;
    options: string | undefined;
    problem: string;
    dot: string | undefined;
}

interface stateInterface {
    proof: {
        label: string;
        options: string | undefined;
        problem: string;
        dot: string | undefined;
    };
}

export type {
    LineProps,
    NodeInterface,
    proof,
    OnClickArgs,
    NodeProps,
    ElementProofListProps,
    FormNewProofProps,
    ProofListProps,
    VisualizerDialogProps,
    DialogProps,
    VisualizerNavbarProps,
    CanvasProps,
    CanvasState,
    proofState,
    stateInterface,
};
