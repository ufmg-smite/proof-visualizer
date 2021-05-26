import React from 'react';
import { Arrow } from 'react-konva';

import { LineProps } from '../interfaces';

const Line = ({ key, points }: LineProps): JSX.Element => {
    return <Arrow key={key} strokeWidth={1} stroke="black" fill="black" points={[...points]} />;
};

export default Line;
