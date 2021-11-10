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

export default class Node extends React.Component<NodeProps> {
    render(): JSX.Element {
        const {
            rule,
            conclusion,
            args,
            id,
            x,
            y,
            selected,
            nHided,
            nDescendants,
            topHidedNodes,
            color,
            setNodeOnFocus,
            updateNodeState,
            toggleNodeSelection,
            openDrawer,
            unfoldOnClick,
            tree,
        } = this.props;

        const bgColor = color;
        const tagProps = {
            fill: bgColor,
            stroke: selected ? 'red' : 'black',
            strokeWidth: selected ? 3 : 1,
        };
        const textProps = {
            align: 'center',
            fill: textColorFromBg(sixDigitColor(bgColor)),
            fontSize: 15,
            height: 35,
            padding: 10,
            width: 300,
        };
        const nHidedStr = nHided ? '#hidden: ' + nHided : '';
        const nDescendantsStr =
            ' #descendants: ' +
            (rule !== 'π'
                ? nDescendants
                : '[' + (topHidedNodes ? topHidedNodes.map((node) => node[3]).join(', ') : '') + ']');

        return (
            <Group
                draggable
                id={id.toString()}
                key={id}
                onDragMove={(e) => {
                    updateNodeState(id, e.target.attrs.x, e.target.attrs.y);
                }}
                x={x}
                y={y}
                onClick={(e) => {
                    if (e.evt.button === 0) {
                        if (e.evt.shiftKey) {
                            toggleNodeSelection(id, this.props);
                        } else {
                            openDrawer(
                                {
                                    rule: rule,
                                    args: args,
                                    conclusion: conclusion,
                                    nHided: nHided,
                                    nDescendants: nDescendants - (rule === 'π' ? nHided : 0),
                                    topHidedNodes: topHidedNodes,
                                },
                                tree,
                            );
                        }
                    } else if (e.evt.button === 2) {
                        setNodeOnFocus(id);
                        const menuNode = document.getElementById('menu');
                        if (menuNode) {
                            menuNode.style.top = `${e.evt.clientY}px`;
                            menuNode.style.left = `${e.evt.clientX}px`;
                            menuNode.style.display = 'initial';
                            window.addEventListener('click', () => {
                                menuNode.style.display = 'none';
                            });
                        }
                    }
                }}
            >
                <Label x={0} y={0}>
                    <Tag {...tagProps} />
                    <Text
                        {...textProps}
                        text={
                            conclusion +
                            (conclusion === '∴' && topHidedNodes
                                ? '[' + topHidedNodes.map((e) => e[2].trim()).join(',') + ']'
                                : '')
                        }
                    />
                </Label>
                <Label x={0} y={35}>
                    <Tag {...tagProps} />
                    <Text
                        {...textProps}
                        text={
                            rule +
                            (rule === 'π' && topHidedNodes
                                ? '[' + topHidedNodes.map((e) => e[1].trim()).join(',') + ']'
                                : '')
                        }
                    />
                </Label>
                <Label x={0} y={70}>
                    <Tag {...tagProps} />
                    <Text {...textProps} text={nHidedStr + nDescendantsStr} />
                </Label>
            </Group>
        );
    }
}
