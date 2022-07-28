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
        <g style={{ transform: `translate(${newX}px,${newY}px)` }}>
            <rect x={0} y={0} width={300} height={35} strokeWidth="1" fill={color} stroke="black" />
            <rect x={0} y={35} width={300} height={35} strokeWidth="1" fill={color} stroke="black" />
            <rect x={0} y={70} width={50} height={35} strokeWidth="1" fill={color} stroke="black" />
            <rect x={50} y={70} width={250} height={35} strokeWidth="1" fill={color} stroke="black" />
            {node.children.map((child, id) => {
                return (
                    <Arrow
                        key={id}
                        origin={{
                            x: visualInfo[child].x - x + 150,
                            y: visualInfo[child].y - y,
                        }}
                        end={{ x: 150, y: 105 }}
                    />
                );
            })}
            <text x={150} y={21} fontSize="15" fill={fill} dominantBaseline="middle" textAnchor="middle">
                {node.conclusion}
            </text>
            <text x={150} y={56} fontSize="15" fill={fill} dominantBaseline="middle" textAnchor="middle">
                {infos.rule}
            </text>
            <text x={25} y={91} fontSize="15" fill={fill} dominantBaseline="middle" textAnchor="middle">
                {node.id.toString()}
            </text>
            <text x={175} y={91} fontSize="15" fill={fill} dominantBaseline="middle" textAnchor="middle">
                {infos.nHided + infos.nDescendants}
            </text>
            {node.dependencies.length ? (
                <>
                    <circle cx={350} cy={53} r={25} strokeWidth="1" fill={color} stroke="black" />
                    <Arrow origin={{ x: 325, y: 53 }} end={{ x: 300, y: 53 }} />
                    <text x={350} y={53} fontSize="15" fill={fill} dominantBaseline="middle" textAnchor="middle">
                        {infos.dependencies}
                    </text>
                </>
            ) : null}
        </g>
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
