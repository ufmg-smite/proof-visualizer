import { Dispatch, SetStateAction } from 'react';
import { ActionCreatorWithPayload } from '@reduxjs/toolkit';
import { TreeNodeInfo } from '@blueprintjs/core';
import { renderLetKind, ClusterKind } from './enum';

// NODES
interface NodeInterface {
    id: number;
    conclusion: string;
    rule: string;
    args: string;
    children: number[];
    parents: number[];
    hiddenNodes?: NodeInterface[];
    descendants: number;
    dependencies: { piId: number; depsId: number[] }[];
    clusterType: ClusterKind;
}

interface NodeProps {
    id: NodeInterface['id'];
    conclusion: NodeInterface['conclusion'];
    rule: NodeInterface['rule'];
    args: NodeInterface['args'];

    x: number;
    y: number;

    nHided: number;
    nDescendants: number;
    hiddenNodes: number[];
    dependencies: NodeInterface['dependencies'];

    selected: boolean;
    color: string;

    setNodeOnFocus: (id: number) => void;
    toggleNodeSelection: (id: number) => void;
    updateNodePosition: (key: number, x: number, y: number) => void;
    openDrawer: (nodeInfo: NodeInfo, tree?: Array<TreeNode>) => void;
    onDragEnd: () => void;
    createTree: (id: number) => TreeNode[];
}

// Info passed to the info drawer
interface NodeInfo {
    rule: NodeProps['rule'];
    args: NodeProps['args'];
    conclusion: NodeProps['conclusion'];
    nHided: NodeProps['nHided'];
    nDescendants: NodeProps['nDescendants'];
    hiddenNodes: NodeProps['hiddenNodes'];
    dependencies: NodeProps['dependencies'];
}

// CANVAS
// Dividir essas interfaces em funções
interface CanvasProps {
    openDrawer: (nodeInfo: NodeInfo) => void;
    createTree: (proof: NodeInterface[], id: number) => TreeNode[];
}

interface CanvasPropsAndRedux extends CanvasProps {
    proof: NodeInterface[];
    visualInfo: ProofState['visualInfo'];
    nodeFindData: ExternalCmdState['findData'];
    renderData: ExternalCmdState['renderData'];
    spinner: ExternalCmdState['spinner'];

    hideNodes: ActionCreatorWithPayload<number[], string>;
    unhideNodes: ActionCreatorWithPayload<{ pi: number; hiddens: number[] }, string>;
    foldAllDescendants: ActionCreatorWithPayload<number>;
    setVisualInfo: ActionCreatorWithPayload<ProofState['visualInfo'], string>;
    findNode: ActionCreatorWithPayload<{ nodeId: number; option: boolean }, string>;
    reRender: ActionCreatorWithPayload<void, string>;
    addRenderCount: ActionCreatorWithPayload<void, string>;
    blockRenderNewFile: ActionCreatorWithPayload<void, string>;
    setSpinner: ActionCreatorWithPayload<ExternalCmdState['spinner'], string>;
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

// DIRECTORY STYLE
interface DirectoryStyleProps {
    proofTree: TreeNodeInfo[];
    ruleHelper: (s: string) => string;
    indent: (s: string) => string;
    translate: (s: string) => string;
}

// NAVBAR
interface NavbarProps {
    setDialogIsOpen: Dispatch<SetStateAction<boolean>>;
    setDrawerIsOpen: Dispatch<SetStateAction<boolean>>;
    addErrorToast: (err: string) => void;
    inTutorial: boolean;
    setInTutorial: Dispatch<SetStateAction<boolean>>;
    setSmtDrawerIsOpen: React.DispatchWithoutAction;
}

interface NavbarPropsAndRedux extends NavbarProps {
    proof: ProofState['proof'];
    dot: string;
    view: string;
    visualInfo: ProofState['visualInfo'];
    hiddenNodes: number[][];
    hideNodes: ActionCreatorWithPayload<number[], string>;
}

// DIALOG
interface VisualizerDialogProps {
    dialogIsOpen: boolean;
    setDialogIsOpen: Dispatch<SetStateAction<boolean>>;
    addErrorToast: (err: string) => void;
}

// TREENODE
interface TreeNode {
    id: NodeProps['id'];
    conclusion: NodeProps['conclusion'];
    rule: NodeProps['rule'];
    args: NodeProps['args'];
    descendants: NodeProps['nDescendants'];
    nHided: NodeProps['nHided'];
    hiddenNodes: NodeProps['hiddenNodes'];
    dependencies: NodeProps['dependencies'];

    icon: 'graph';
    label: string;
    secondaryLabel: string;
    hasCaret: boolean | undefined;
    parentsId: number[];
    parentId: number;
    childNodes: TreeNode[];
}

interface TreeProps {
    darkTheme: boolean;
    proof: ProofState['proof'];
    positionMap: any;
    content: TreeNodeInfo[];
    setNodeInfo: Dispatch<SetStateAction<NodeInfo>>;
}

interface LineProps {
    key: string;
    points: Array<number>;
}

// VISUALIZERS DRAWER
interface LetRenderProps {
    id: number;
    toRender: string;
    letMap: ProofState['letMap'];
    shouldExpand: boolean;
    shouldRevert: boolean;
    dispatchExpansion: React.Dispatch<{
        type: renderLetKind;
        payload: boolean;
    }>;
}

interface DrawerVisualizerTabProps {
    shouldResize: boolean;
}

interface DrawerProps {
    drawerIsOpen: boolean;
    setDrawerIsOpen: Dispatch<SetStateAction<boolean>>;
}

// SMT DRAWER
interface SmtDrawerProps {
    isOpen: boolean;
    setDrawerIsOpen: React.DispatchWithoutAction;
    addErrorToast: (err: string) => void;
    smtOptions: { argsType: boolean; customArgs: string };
    setSmtOptions: Dispatch<SetStateAction<SmtDrawerProps['smtOptions']>>;
}

// TUTORIAL PROPS
interface TutorialProps {
    inTutorial: boolean;
    setInTutorial: Dispatch<SetStateAction<boolean>>;
}

interface TutorialPopoverProps {
    setIsOpen: Dispatch<SetStateAction<boolean>>;
    nextTutorial: () => void;
    stage: number;
    content: string[];
    W: number;
    position: {
        x: number;
        y: number;
        tW: number;
    };
}

// REDUX STATES
interface ReduxState {
    file: FileState;
    proof: ProofState;
    theme: ThemeState;
    externalCmd: ExternalCmdState;
}
// PROOFS
interface ProofState {
    proof: NodeInterface[];
    view: 'full' | 'clustered' | 'colored-full';
    style: 'graph' | 'directory';
    hiddenNodes: number[][];
    letMap: {
        [Key: string]: string;
    };
    theoryLemmaMap: string[];
    visualInfo: {
        [id: number]: {
            color: string;
            x: number;
            y: number;
            selected: boolean;
        };
    };
    clustersInfos: {
        hiddenNodes: number[];
        type: ClusterKind;
        color: string;
    }[];
    smt: string;
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
//EXTERNAL COMMANDS
interface ExternalCmdState {
    findData: {
        nodeToFind: number;
        findOption: boolean;
    };
    renderData: {
        count: number;
        fileChanged: boolean;
    };
    spinner: 'off' | 'cvc5' | 'render';
}

export type {
    NodeInterface,
    NodeProps,
    NodeInfo,
    CanvasProps,
    CanvasPropsAndRedux,
    CanvasState,
    DirectoryStyleProps,
    NavbarProps,
    NavbarPropsAndRedux,
    VisualizerDialogProps,
    TreeNode,
    TreeProps,
    LineProps,
    LetRenderProps,
    DrawerVisualizerTabProps,
    DrawerProps,
    SmtDrawerProps,
    TutorialProps,
    TutorialPopoverProps,
    ReduxState,
    ProofState,
    FileState,
    ThemeState,
    ExternalCmdState,
};
