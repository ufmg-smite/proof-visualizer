import React from 'react';
import { Label, Text, Tag, Group } from 'react-konva';

import { NodeProps } from '../interfaces';

function textColorFromBg(bgColor: string) {
    const color = bgColor.charAt(0) === '#' ? bgColor.substring(1, 7) : bgColor;
    const r = parseInt(color.substring(0, 2), 16);
    const g = parseInt(color.substring(2, 4), 16);
    const b = parseInt(color.substring(4, 6), 16);
    return r * 0.299 + g * 0.587 + b * 0.114 > 150 ? '#000000' : '#ffffff';
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
            setNodeOnFocus,
            updateNodeState,
            toggleNodeSelection,
            openDrawer,
            tree,
        } = this.props;

        const bgColor = '#8d99ae';

        const tagProps = {
            fill: bgColor,
            stroke: selected ? 'red' : 'black',
            strokeWidth: selected ? 3 : 1,
        };
        const textProps = {
            align: 'center',
            fill: textColorFromBg(bgColor),
            fontSize: 15,
            height: 35,
            padding: 10,
            width: 300,
        };
        const nHidedStr = nHided
            ? '#hidden: ' + '[' + (topHidedNodes ? topHidedNodes.map((node) => node[4]).join(', ') : '') + ']'
            : '';
        const nDescendantsStr =
            ' #descendants: ' +
            (rule !== 'π'
                ? nDescendants - 1
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
                            toggleNodeSelection(id);
                        } else {
                            openDrawer(
                                {
                                    rule: rule,
                                    args: args,
                                    conclusion: conclusion,
                                    nHided: nHided,
                                    nDescendants: nDescendants - (rule === 'π' ? nHided : 1),
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
