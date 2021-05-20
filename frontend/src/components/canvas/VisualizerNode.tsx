import React from 'react';
import { Label, Text, Tag, Group } from 'react-konva';

import { nodeProps } from '../interfaces/NodeProps';

function textColorFromBg(bgColor: string) {
    const color = bgColor.charAt(0) === '#' ? bgColor.substring(1, 7) : bgColor;
    const r = parseInt(color.substring(0, 2), 16);
    const g = parseInt(color.substring(2, 4), 16);
    const b = parseInt(color.substring(4, 6), 16);
    return r * 0.299 + g * 0.587 + b * 0.114 > 150 ? '#000000' : '#ffffff';
}

export default class Node extends React.Component<nodeProps> {
    render(): JSX.Element {
        const {
            rule,
            conclusion,
            id,
            showingChildren,
            x,
            y,
            hasChildren,
            hidingNode,
            onClick,
            setFocusText,
            setNodeOnFocus,
            updateNodeState,
        } = this.props;

        const bgClosedColor = '#2b2d42';
        const bgOpenColor = '#8d99ae';

        const bgColor = showingChildren || !hasChildren ? bgOpenColor : bgClosedColor;

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
                    if (e.evt.button === 1) {
                        onClick({ id, x, y });
                    } else if (e.evt.button === 2 && hidingNode) {
                        setNodeOnFocus(id);
                        const menuNode = document.getElementById('menu');
                        if (menuNode) {
                            menuNode.style.top = `${e.evt.clientY}px`;
                            menuNode.style.left = `${e.evt.clientX}px`;
                            menuNode.style.display = 'initial';
                            window.addEventListener('click', () => {
                                menuNode.style.display = 'none';
                            });
                        } else {
                            // Apagar depois que garantido que o menu está ok
                            alert('Problema com menu do canvas');
                        }
                    }
                }}
            >
                <Label
                    onMouseEnter={(e) => {
                        setFocusText(e.target.attrs.text);
                    }}
                    onMouseLeave={() => setFocusText('')}
                    x={0}
                    y={0}
                >
                    <Tag fill={bgColor} stroke="black" />
                    <Text
                        align="center"
                        fill={textColorFromBg(bgColor)}
                        fontSize={15}
                        height={35}
                        padding={10}
                        text={conclusion}
                        width={300}
                    />
                </Label>
                <Label
                    x={0}
                    y={35}
                    onMouseEnter={(e) => {
                        setFocusText(e.target.attrs.text);
                    }}
                    onMouseLeave={() => setFocusText('')}
                >
                    <Tag fill={bgColor} stroke="black" />
                    <Text
                        align="center"
                        fill={textColorFromBg(bgColor)}
                        fontSize={15}
                        height={35}
                        padding={10}
                        text={rule}
                        width={300}
                    />
                </Label>
            </Group>
        );
    }
}
