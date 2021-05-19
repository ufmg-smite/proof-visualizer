import { Dispatch, SetStateAction } from 'react';

interface OnClickArgs {
    id: number;
    x: number;
    y: number;
}

interface NodeProps {
    rule: string;
    conclusion: string;
    id: number;
    onClick: (arg0: onClickArgs) => void;
    setFocusText: Dispatch<SetStateAction<string>>;
    setCurrentText: Dispatch<SetStateAction<string>>;
    showingChildren: boolean;
    updateNodeState: (key: number, x: number, y: number) => void;
    x: number;
    y: number;
    hasChildren: boolean;
    piNode: boolean;
    setNodeOnFocus: (id: number) => void;
}

export type nodeProps = NodeProps;
export type onClickArgs = OnClickArgs;
