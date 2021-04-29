import React, { Dispatch, SetStateAction } from 'react';

import { Button, Classes, Dialog, Intent } from '@blueprintjs/core';
import { MaybeElement } from '@blueprintjs/core/lib/esm/common/props';
import { IconName } from '@blueprintjs/core/lib/esm/components/icon/icon';

import FormNewProof from './FormNewProof';
import ProofList from './ProofList';

import '../scss/VisualizerDialog.scss';

interface VisualizerDialogProps {
    darkTheme: boolean;
    dialogIsOpen: boolean;
    setDialogIsOpen: Dispatch<SetStateAction<boolean>>;
    dialogContent: string;
    setDialogContent: Dispatch<SetStateAction<string>>;
}

interface DialogProps {
    icon: IconName | MaybeElement;
    title: React.ReactNode;
}

const VisualizerDialog: React.FC<VisualizerDialogProps> = ({
    darkTheme,
    dialogIsOpen,
    dialogContent,
    setDialogIsOpen,
}: VisualizerDialogProps) => {
    let dialogProps: DialogProps = { icon: 'error', title: 'Error' };
    let dialogBody = <p>This wasn&apos;t supposed to happen. Please contact the developers.</p>;
    let succesButton = <></>;

    switch (dialogContent) {
        case 'proof-list':
            dialogProps = { icon: 'list', title: 'Proof List' };
            dialogBody = <ProofList></ProofList>;
            break;
        case 'new-proof':
            dialogProps = { icon: 'add', title: 'New Proof' };
            dialogBody = <FormNewProof></FormNewProof>;
            succesButton = (
                <Button
                    onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                        e.preventDefault();
                        setDialogIsOpen(false);
                    }}
                    intent={Intent.SUCCESS}
                >
                    Generate Proof
                </Button>
            );
            break;
    }

    return (
        <>
            <Dialog
                className={darkTheme ? ' bp3-dark' : ''}
                isOpen={dialogIsOpen}
                onClose={(): void => setDialogIsOpen(false)}
                usePortal={true}
                {...dialogProps}
            >
                <div className={Classes.DIALOG_BODY + ' dialog-body'}>{dialogBody}</div>
                <div className={Classes.DIALOG_FOOTER}>
                    <div className={Classes.DIALOG_FOOTER_ACTIONS}>
                        <Button
                            onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                                e.preventDefault();
                                setDialogIsOpen(false);
                            }}
                        >
                            Close
                        </Button>
                        {succesButton}
                    </div>
                </div>
            </Dialog>
        </>
    );
};

export default VisualizerDialog;
