import { ObjectID } from 'mongodb';
import { Dispatch, SetStateAction } from 'react';

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

export type { LineProps, NodeInterface, proof, OnClickArgs, NodeProps };
