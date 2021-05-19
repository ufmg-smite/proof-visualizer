import React from 'react';
import { Arrow } from 'react-konva';

interface LineProps {
    key: number;
    points: Array<number>;
}

const Line = ({ key, points }: LineProps): JSX.Element => {
    return <Arrow key={key} strokeWidth={2} stroke="black" fill="black" points={[...points]} />;
};

export default Line;
