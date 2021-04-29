import React, { useState } from 'react';

import VisualizerNavbar from './components/VisualizerNavbar';
import VisualizerDialog from './components/VisualizerDialog';

const App: React.FC = () => {
    const [darkTheme, setDarkTheme] = useState(true);
    const [dialogIsOpen, setDialogIsOpen] = useState(false);
    const [dialogContent, setDialogContent] = useState('');

    return (
        <div className={darkTheme ? ' bp3-dark' : ''}>
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
            ></VisualizerDialog>
        </div>
    );
};

export default App;
