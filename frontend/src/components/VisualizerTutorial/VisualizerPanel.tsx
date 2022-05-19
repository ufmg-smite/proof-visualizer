import { Portal } from '@blueprintjs/core';
import React, { useEffect, useRef, useState } from 'react';
import { TutorialProps } from '../../interfaces/interfaces';
import '../../scss/Tutorial.scss';
import TutorialPopover from './TutorialPopover';

const W = 180;
const divsIds = [
    'proof-visualizer-name',
    'upload-proof-bt',
    'examples-bt',
    'file-name-title',
    'command',
    'style-bt',
    'visualizers-bt',
    'download-bt',
    'switch-button-dark-theme',
];
const tutorials: string[][] = [['a'], ['b'], ['c'], ['c'], ['c'], ['c'], ['c'], ['c'], ['c']];

// panel stack
const VisualizerTutorial: React.FC<TutorialProps> = ({ inTutorial, setInTutorial }: TutorialProps) => {
    const [stage, setStage] = useState(-1);
    const [position, setPosition] = useState({ x: 0, y: 0 });
    const sizeRef = useRef({ w: 0, h: 0 });

    const increaseStage = () => {
        if (stage < tutorials.length - 1) setStage(stage + 1);
        else setInTutorial(false);
    };

    // ComponentDidMount
    useEffect(() => {
        // Handler to call on window resize and set the value column width
        function handleResize() {
            sizeRef.current.w = window.innerWidth;
            sizeRef.current.h = window.innerHeight;
        }

        // Add event listener
        window.addEventListener('resize', handleResize);
        // Call handler right away so state gets updated with initial window size
        handleResize();

        // Remove event listener on cleanup
        return () => window.removeEventListener('resize', handleResize);
    }, []);

    useEffect(() => {
        if (inTutorial) setStage(0);
        else setStage(-1);
    }, [inTutorial]);

    useEffect(() => {
        const toBeWrapped: HTMLElement | null = document.getElementById(divsIds[stage]);
        if (toBeWrapped) {
            const { x, y, width, height } = toBeWrapped.getClientRects()[0];
            const newY = y + height;
            let newX = x + width / 2;
            // Positioning in the beggining
            if (newX < W) newX = 0;
            // Positioning in the end
            else if (newX + W / 2 > sizeRef.current.w) newX = sizeRef.current.w - W;
            // Positioning in the normal position
            else newX -= W / 2;

            setPosition({ x: newX, y: newY });
        }
    }, [stage]);

    return (
        <Portal className={`tutorial-portal`}>
            <div
                className="bp3-overlay-enter-done"
                style={{
                    width: sizeRef.current.w,
                    height: sizeRef.current.h,
                    pointerEvents: stage >= 0 ? 'auto' : 'none',
                    backgroundColor: stage >= 0 ? 'rgba(87, 82, 82, 0.233)' : 'transparent',
                }}
            >
                {stage >= 0 && (
                    <TutorialPopover
                        setIsOpen={setInTutorial}
                        nextTutorial={increaseStage}
                        content={tutorials[stage]}
                        W={W}
                        position={position}
                    />
                )}
            </div>
        </Portal>
        // bp3-overlay-backdrop
    );
};

export default VisualizerTutorial;
