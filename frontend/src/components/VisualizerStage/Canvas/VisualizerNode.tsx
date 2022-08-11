import { KonvaEventObject } from 'konva/types/Node';
import React, { useEffect, useState } from 'react';
import { Label, Text, Tag, Group, Circle, Arrow } from 'react-konva';
import { NodeProps } from '../../../interfaces/interfaces';

function getTextWidth(text: string, font: string): number {
    const canvas = document.createElement('canvas');
    const context = canvas.getContext('2d');
    let size = 0;
    if (context) {
        context.font = font;
        size = context.measureText(text).width;
    }
    return size;
}

export function textColorFromBg(bgColor: string) {
    const r = parseInt(bgColor.substring(0, 2), 16);
    const g = parseInt(bgColor.substring(2, 4), 16);
    const b = parseInt(bgColor.substring(4, 6), 16);
    return r * 0.299 + g * 0.587 + b * 0.114 > 150 ? '#000000' : '#ffffff';
}

export function sixDigitColor(bgColor: string): string {
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

const Node: React.FC<NodeProps> = (props: NodeProps): JSX.Element => {
    const {
        id,
        conclusion,
        rule,
        args,
        x,
        y,
        nHided,
        nDescendants,
        hiddenNodes,
        dependencies,
        selected,
        color,
        setNodeOnFocus,
        toggleNodeSelection,
        updateNodePosition,
        openDrawer,
        onDragEnd,
        createTree,
    } = props;

    const handleClick = (e: KonvaEventObject<MouseEvent>): void => {
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
                        nDescendants: nDescendants - (rule === 'π' ? 0 : 0),
                        hiddenNodes: hiddenNodes,
                        dependencies: dependencies,
                    },
                    createTree(id),
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
    };

    const depSize = 25,
        depLineSize = 25;
    const bgColor = color;

    const style = {
        tag: {
            fill: bgColor,
            stroke: selected ? 'red' : 'black',
            strokeWidth: selected ? 3 : 1,
        },
        get dep() {
            return { ...this.tag };
        },
        text: {
            align: 'center',
            fill: textColorFromBg(sixDigitColor(bgColor)),
            fontSize: 15,
            height: 35,
            padding: 10,
            width: 300,
        },
        get depText() {
            return {
                ...this.text,
                padding: 0,
                width: depSize * 2,
            };
        },
    };
    const infos = {
        nHided: nHided ? `#hidden: ${nHided}` : '',
        nDescendants: ` #descendants: ${nDescendants}`,
        rule: nHided ? 'π' : rule,
        dependencies: dependencies.length === 1 ? String(dependencies[0].piId) : 'π',
    };

    const [idSize, setIdSize] = useState(50);
    const [descendantSize, setDescendantSize] = useState(style.text.width - 50);

    // Component Did Mount
    useEffect(() => {
        const font = `${style.text.fontSize}px -apple-system, "BlinkMacSystemFont", "Segoe UI", "Roboto", "Oxygen", "Ubuntu", "Cantarell", "Open Sans", "Helvetica Neue", "Icons16", sans-serif`;
        const calc = getTextWidth(id.toString(), font) + style.text.padding * 3;
        setIdSize(calc);
        setDescendantSize(style.text.width - calc);
    }, []);

    return (
        <Group
            draggable
            id={id.toString()}
            key={id}
            onDragMove={(e) => {
                updateNodePosition(id, e.target.attrs.x, e.target.attrs.y);
            }}
            onDragEnd={() => onDragEnd(id)}
            x={x}
            y={y}
            onClick={handleClick}
        >
            <Label x={0} y={0}>
                <Tag {...style.tag} />
                <Text {...style.text} text={conclusion} />
            </Label>
            <Label x={0} y={35}>
                <Tag {...style.tag} />
                <Text {...style.text} text={infos.rule} />
            </Label>
            <Label x={0} y={70} {...{ align: 'right' }}>
                <Tag {...style.tag} />
                <Text {...{ ...style.text, width: idSize }} text={id.toString()} />
            </Label>
            <Label x={idSize} y={70}>
                <Tag {...style.tag} />
                <Text {...{ ...style.text, width: descendantSize }} text={infos.nHided + infos.nDescendants} />
            </Label>
            {dependencies.length ? (
                <Label x={300} y={0}>
                    <Arrow strokeWidth={1} stroke="black" fill="black" points={[depLineSize, 53, 0, 53]} />
                    <Circle x={depLineSize + depSize} y={53} radius={depSize} {...style.dep}></Circle>
                    <Label x={depLineSize} y={45}>
                        <Text {...style.depText} text={infos.dependencies} />
                    </Label>
                </Label>
            ) : null}
        </Group>
    );
};

export default Node;
