import React from 'react';
import '../../interfaces/interfaces';
import { NodeInterface, ProofState } from '../../interfaces/interfaces';
import { textColorFromBg, sixDigitColor } from '../VisualizerStage/Canvas/VisualizerNode';

interface Point {
    x: number;
    y: number;
}

interface ArrowProps {
    origin: Point;
    end: Point;
}

const arrowTriangleH = 15;
const arrowTriangleW = 5;
const fontSize = 15;
const fontFamily = 'Arial';

const Arrow: React.FC<ArrowProps> = ({ origin, end }: ArrowProps) => {
    const h = origin.y - end.y;
    const w = end.x - origin.x;
    const l = Math.sqrt(h ** 2 + w ** 2);

    const sin = h / l;
    const cos = w / l;

    const axeX = end.x - arrowTriangleH * cos;
    const axeY = end.y + arrowTriangleH * sin;

    const alpha = Math.atan2(h, w) + Math.PI / 2;
    const sin1 = Math.sin(alpha);
    const cos1 = Math.cos(alpha);

    const p1X = axeX - arrowTriangleW * cos1;
    const p1Y = axeY + arrowTriangleW * sin1;

    const p2X = axeX + arrowTriangleW * cos1;
    const p2Y = axeY - arrowTriangleW * sin1;

    return (
        <>
            <path d={`M${end.x} ${end.y} L${p1X} ${p1Y} L${p2X} ${p2Y} Z`} />
            <line x1={origin.x} y1={origin.y} x2={end.x} y2={end.y} strokeWidth="1" stroke="black" />
        </>
    );
};

function CreateNode(node: NodeInterface, visualInfo: ProofState['visualInfo'], limits: [number, number]): JSX.Element {
    const { color, x, y } = visualInfo[node.id];
    const [smallestX, smallestY] = limits;
    const newX = x - smallestX;
    const newY = y - smallestY;

    const fill = textColorFromBg(sixDigitColor(color));

    const nHided = node.hiddenNodes ? node.hiddenNodes.length : 0;
    const infos = {
        nHided: nHided ? `#hidden: ${nHided}` : '',
        nDescendants: ` #descendants: ${node.descendants - 1}`,
        rule: nHided ? 'π' : node.rule,
        dependencies: node.dependencies.length === 1 ? String(node.dependencies[0].piId) : 'π',
    };

    return (
        <>
            {node.children.map((child, id) => {
                return (
                    <Arrow
                        key={id}
                        origin={{
                            x: visualInfo[child].x - smallestX + 150,
                            y: visualInfo[child].y - smallestY,
                        }}
                        end={{ x: newX + 150, y: newY + 105 }}
                    />
                );
            })}
            <rect x={newX + 0} y={newY + 0} width={300} height={35} strokeWidth="1" fill={color} stroke="black" />
            <rect x={newX + 0} y={newY + 35} width={300} height={35} strokeWidth="1" fill={color} stroke="black" />
            <rect x={newX + 0} y={newY + 70} width={50} height={35} strokeWidth="1" fill={color} stroke="black" />
            <rect x={newX + 50} y={newY + 70} width={250} height={35} strokeWidth="1" fill={color} stroke="black" />
            <text
                x={newX + 150}
                y={newY + 21}
                fontSize={fontSize}
                fill={fill}
                dominantBaseline="middle"
                textAnchor="middle"
                fontFamily={fontFamily}
            >
                {node.conclusion}
            </text>
            <text
                x={newX + 150}
                y={newY + 56}
                fontSize={fontSize}
                fill={fill}
                dominantBaseline="middle"
                textAnchor="middle"
                fontFamily={fontFamily}
            >
                {infos.rule}
            </text>
            <text
                x={newX + 25}
                y={newY + 91}
                fontSize={fontSize}
                fill={fill}
                dominantBaseline="middle"
                textAnchor="middle"
                fontFamily={fontFamily}
            >
                {node.id.toString()}
            </text>
            <text
                x={newX + 175}
                y={newY + 91}
                fontSize={fontSize}
                fill={fill}
                dominantBaseline="middle"
                textAnchor="middle"
                fontFamily={fontFamily}
            >
                {infos.nHided + infos.nDescendants}
            </text>
            {node.dependencies.length ? (
                <>
                    <circle cx={newX + 350} cy={newY + 53} r={25} strokeWidth="1" fill={color} stroke="black" />
                    <Arrow origin={{ x: newX + 325, y: newY + 53 }} end={{ x: newX + 300, y: newY + 53 }} />
                    <text
                        x={newX + 350}
                        y={newY + 53}
                        fontSize={fontSize}
                        fill={fill}
                        dominantBaseline="middle"
                        textAnchor="middle"
                        fontFamily={fontFamily}
                    >
                        {infos.dependencies}
                    </text>
                </>
            ) : null}
        </>
    );
}

export function ConvertToSVG(proof: NodeInterface[], visualInfo: ProofState['visualInfo']): JSX.Element {
    let [biggestX, biggestY, smallestX, smallestY] = [0, 0, Number.MAX_SAFE_INTEGER, Number.MAX_SAFE_INTEGER];

    // Find the biggest and smallest dimensions
    const keys = Object.keys(visualInfo);
    keys.forEach((key) => {
        const { x, y } = visualInfo[Number(key)];
        //
        if (x > biggestX) biggestX = x;
        if (x < smallestX) smallestX = x;
        //
        if (y > biggestY) biggestY = y;
        if (y < smallestY) smallestY = y;
    });

    return (
        <svg
            id="svg-converted"
            xmlns="http://www.w3.org/2000/svg"
            style={{ position: 'relative', top: '5px', left: '5px', overflow: 'visible' }}
            width={biggestX - smallestX + 420}
            height={biggestY - smallestY + 220}
        >
            {proof.map((node) => {
                return CreateNode(node, visualInfo, [smallestX, smallestY]);
            })}
        </svg>
    );
}
