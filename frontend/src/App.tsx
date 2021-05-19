import React, { useState } from 'react';

import { Intent, Position, Toaster } from '@blueprintjs/core';

import VisualizerNavbar from './components/VisualizerNavbar';
import VisualizerDialog from './components/VisualizerDialog';
import VisualizerStage from './components/VisualizerStage';

const App: React.FC = () => {
    const [darkTheme, setDarkTheme] = useState(true);
    const [dialogIsOpen, setDialogIsOpen] = useState(false);
    const [dialogContent, setDialogContent] = useState('');

    // Toaster
    let toaster: Toaster;
    const refHandlers = {
        toaster: (ref: Toaster) => (toaster = ref),
    };
    const addErrorToast = (err: string) => {
        toaster.show({ icon: 'warning-sign', intent: Intent.DANGER, message: err });
    };
    const addDeleteToast = (proofName: string) => {
        toaster.show({ icon: 'trash', intent: Intent.DANGER, message: '"' + proofName + '" was deleted.' });
    };

    return (
        <div className={darkTheme ? ' bp3-dark' : ''}>
            <Toaster position={Position.TOP} ref={refHandlers.toaster} />
            <VisualizerNavbar
                darkTheme={darkTheme}
                setDarkTheme={setDarkTheme}
                setDialogIsOpen={setDialogIsOpen}
                setDialogContent={setDialogContent}
            ></VisualizerNavbar>
            <VisualizerDialog
                dialogIsOpen={dialogIsOpen}
                setDialogIsOpen={setDialogIsOpen}
                dialogContent={dialogContent}
                setDialogContent={setDialogContent}
                darkTheme={darkTheme}
                addErrorToast={addErrorToast}
                addDeleteToast={addDeleteToast}
            ></VisualizerDialog>
            <VisualizerStage></VisualizerStage>
        </div>
    );
};

export default App;
