import React, { useState } from 'react';
import { useSelector } from 'react-redux';

import { Intent, Position, Toaster } from '@blueprintjs/core';

import VisualizerNavbar from './components/VisualizerNavbar';
import VisualizerDialog from './components/VisualizerDialog';
import VisualizerStage from './components/VisualizerStage';

import { stateInterface } from './components/interfaces';

const App: React.FC = () => {
    const [dialogIsOpen, setDialogIsOpen] = useState(true);
    const [dialogContent, setDialogContent] = useState('welcome');

    const darkTheme = useSelector<stateInterface, boolean>((state: stateInterface) => state.darkThemeReducer.darkTheme);

    // Toaster
    let toaster: Toaster;
    const refHandlers = {
        toaster: (ref: Toaster) => (toaster = ref),
    };

    return (
        <div className={darkTheme ? ' bp3-dark' : ''}>
            <Toaster position={Position.TOP} ref={refHandlers.toaster} />
            <VisualizerNavbar setDialogIsOpen={setDialogIsOpen} setDialogContent={setDialogContent}></VisualizerNavbar>
            <VisualizerDialog
                dialogIsOpen={dialogIsOpen}
                setDialogIsOpen={setDialogIsOpen}
                dialogContent={dialogContent}
                setDialogContent={setDialogContent}
            ></VisualizerDialog>
            <VisualizerStage></VisualizerStage>
        </div>
    );
};

export default App;
