import { KonvaEventObject } from 'konva/types/Node';
import React from 'react';
import { Label, Text, Tag, Group } from 'react-konva';
import { NodeProps } from '../../../interfaces/interfaces';

function textColorFromBg(bgColor: string) {
    const r = parseInt(bgColor.substring(0, 2), 16);
    const g = parseInt(bgColor.substring(2, 4), 16);
    const b = parseInt(bgColor.substring(4, 6), 16);
    return r * 0.299 + g * 0.587 + b * 0.114 > 150 ? '#000000' : '#ffffff';
}

function sixDigitColor(bgColor: string): string {
    if (bgColor.charAt(0) === '#') {
        if (bgColor.length == 4) {
            return bgColor
                .substring(1, 7)
                .split('')
                .map((c) => c + c)
                .join('');
        } else if (bgColor.length == 7) {
            return bgColor.substring(1, 7);
        }
    } else {
        if (bgColor.length == 3) {
            return bgColor
                .split('')
                .map((c) => c + c)
                .join('');
        } else if (bgColor.length == 6) {
            return bgColor;
        }
    }
    return '000000';
}

const Node: React.FC<NodeProps> = ({
    id,
    conclusion,
    rule,
    args,
    x,
    y,
    nHided,
    nDescendants,
    hiddenNodes,
    selected,
    color,
    setNodeOnFocus,
    toggleNodeSelection,
    updateNodePosition,
    openDrawer,
    onDragEnd,
    createTree,
    tree,
}: NodeProps): JSX.Element => {
    return <div>aaaa</div>;
};

export default Node;
