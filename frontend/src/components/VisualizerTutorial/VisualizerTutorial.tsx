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
const tutorials: string[][] = [
    ["This website is a SMT solver proofs visualizer. Let's start the tutorial"],
    [
        'Here you can upload your proofs to be visualized.',
        'The proofs can have a .dot or .json format.',
        'The .json format is obtained in the download section.',
    ],
    ['Here you can visualize some examples of differents proofs.'],
    ['This is the name of the current proof uploaded'],
    [
        'This is the command section. Here you can apply some commands that will transform the proof, changing the way you comprehend it.',
        "Click in the '?' button to see a description of all commands.",
    ],
    [
        'Here you can change the way the visualizer presents the proof.',
        "The graph style is the default and it's where the commands transformations happens.",
        "In the directory style each proof node is a 'folder' and your children nodes are inside it.",
    ],
    [
        'Here you have access to 3 visualizers:',
        'View: It allow you to change the way the proof nodes are viewed.',
        'Let Map: Here you can see a map of all the LETS used inside the proofs. A let is a therm that shorten some expression (e.g.: let1 = (and A B))',
        'Theory Lemma: It allow you to see all the theory lemmas in the proof construction.',
    ],
    [
        'This section allow you to download the proof in different ways.',
        '.DOT is the default format. It only holds informations about the proof structure and your clusters.',
        '.JSON allow the user to save all the visual informations about the proof (i.e. the nodes positions, colors and foldings after any transformation applied) and your structural infos just like the .DOT.',
        '.PNG prints the proof in the current state (i.e. includes all the transformations) into a image.',
    ],
    ['Allow to change between dark/light mode.'],
];

// panel stack
const VisualizerTutorial: React.FC<TutorialProps> = ({ inTutorial, setInTutorial }: TutorialProps) => {
    const [stage, setStage] = useState(-1);
    const [position, setPosition] = useState({ x: 0, y: 0, tW: 0 });
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
            const newTW = newX;
            // Positioning in the beggining
            if (newX < W) newX = 3;
            // Positioning in the end
            else if (newX + W / 2 > sizeRef.current.w) newX = sizeRef.current.w - W - 3;
            // Positioning in the normal position
            else newX -= W / 2;

            setPosition({ x: newX, y: newY, tW: newTW });
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
