import React, { useEffect, useReducer, useState } from 'react';

import { Intent, Overlay, Position, Spinner, Toaster } from '@blueprintjs/core';

import VisualizerNavbar from '../VisualizerNavbar/VisualizerNavbar';
import VisualizerDialog from '../VisualizerDialog/VisualizerDialog';
import VisualizerStage from '../VisualizerStage/VisualizerStage';
import VisualizersDrawer from '../VisualizersDrawer/VisualizersDrawer';

import { useAppSelector } from '../../store/hooks';
import { selectTheme } from '../../store/features/theme/themeSlice';
import VisualizerTutorial from '../VisualizerTutorial/VisualizerTutorial';
import VisualizerSmtDrawer from '../VisualizerSmtDrawer/VisualizerSmtDrawer';
import { selectSpinner } from '../../store/features/externalCmd/externalCmd';

const App: React.FC = () => {
    const [dialogIsOpen, setDialogIsOpen] = useState(true);
    const [inTutorial, setInTutorial] = useState(false);
    const [drawerIsOpen, setDrawerOpenState] = useState(false);
    const [smtDrawerIsOpen, setSmtDrawerIsOpen] = useState(false);
    const [, disableAllDrawers] = useReducer(() => {
        if (dialogIsOpen) setDialogIsOpen(false);
        if (inTutorial) setInTutorial(false);
        if (drawerIsOpen) setDrawerOpenState(false);
        if (smtDrawerIsOpen) setSmtDrawerIsOpen(false);
        return null;
    }, null);
    const [smtOptions, setSmtOptions] = useState({ argsType: true, customArgs: '' });
    const darkTheme = useAppSelector(selectTheme);
    const spinner = useAppSelector(selectSpinner);

    // Toaster
    let toaster: Toaster;
    const refHandlers = {
        toaster: (ref: Toaster) => (toaster = ref),
    };

    const addErrorToast = (err: string) => {
        toaster.show({ icon: 'warning-sign', intent: Intent.DANGER, message: err });
    };

    useEffect(() => {
        document.getElementsByClassName('bp3-overlay')[0]
            ? (document.getElementsByClassName('bp3-overlay')[0].className = '')
            : null;
    }, [drawerIsOpen]);

    return (
        <div className={darkTheme ? ' bp3-dark' : ''} style={{ height: '100%' }}>
            <VisualizerTutorial inTutorial={inTutorial} setInTutorial={setInTutorial} />
            <Toaster position={Position.TOP} ref={refHandlers.toaster} />
            <VisualizerNavbar
                setDialogIsOpen={setDialogIsOpen}
                setDrawerIsOpen={setDrawerOpenState}
                addErrorToast={addErrorToast}
                inTutorial={inTutorial}
                setInTutorial={setInTutorial}
                setSmtDrawerIsOpen={setSmtDrawerIsOpen}
            />
            <VisualizerDialog
                dialogIsOpen={dialogIsOpen}
                setDialogIsOpen={setDialogIsOpen}
                addErrorToast={addErrorToast}
            />
            <VisualizerStage disableExternalDrawers={disableAllDrawers} />
            {drawerIsOpen ? (
                <VisualizersDrawer drawerIsOpen={drawerIsOpen} setDrawerIsOpen={setDrawerOpenState}></VisualizersDrawer>
            ) : null}
            {smtDrawerIsOpen ? (
                <VisualizerSmtDrawer
                    isOpen={smtDrawerIsOpen}
                    setDrawerIsOpen={setSmtDrawerIsOpen}
                    addErrorToast={addErrorToast}
                    smtOptions={smtOptions}
                    setSmtOptions={setSmtOptions}
                />
            ) : null}
            <Overlay isOpen={spinner !== 'off'} className="spinner-overlay">
                <div className="overlay-container">
                    <div className="spinner-info">
                        <h1>{spinner === 'cvc5' ? 'cvc5 is running!' : 'rendering graph!'}</h1>
                        <Spinner intent={spinner === 'cvc5' ? 'primary' : 'success'} size={80} />
                    </div>
                </div>
            </Overlay>
        </div>
    );
};

export default App;
