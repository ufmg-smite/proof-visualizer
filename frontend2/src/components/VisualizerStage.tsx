import React from 'react';
import { useSelector } from 'react-redux';
import { dotState } from '../redux/dotReducer';

const VisualizerStage: React.FC = () => {
    const dot = useSelector<dotState, dotState['dot']>((state) => state.dot);
    return (
        <>
            <p style={{ color: 'black' }}>{dot}</p>
        </>
    );
};

export default VisualizerStage;
