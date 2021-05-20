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

    onClick: (arg0: onClickArgs) => void;
    setFocusText: Dispatch<SetStateAction<string>>;
    setNodeOnFocus: (id: number) => void;
    updateNodeState: (key: number, x: number, y: number) => void;
}

export type nodeProps = NodeProps;
export type onClickArgs = OnClickArgs;
