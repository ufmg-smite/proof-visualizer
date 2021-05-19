import React from 'react';
import { Arrow } from 'react-konva';

import { lineProps } from '../interfaces/LineProps';

const Line = ({ key, points }: lineProps): JSX.Element => {
    return <Arrow key={key} strokeWidth={2} stroke="black" fill="black" points={[...points]} />;
};

export default Line;
