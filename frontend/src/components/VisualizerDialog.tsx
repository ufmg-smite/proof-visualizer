import React, { useState } from 'react';

import axios from 'axios';
import { Button, Classes, Dialog, Intent, Spinner } from '@blueprintjs/core';
import { Icon } from '@blueprintjs/core/lib/esm/components/icon/icon';

import FormNewProof from './FormNewProof';
import ProofList from './ProofList';

import '../scss/VisualizerDialog.scss';
import { proof, VisualizerDialogProps, DialogProps } from './interfaces';

const VisualizerDialog: React.FC<VisualizerDialogProps> = ({
    darkTheme,
    dialogIsOpen,
    dialogContent,
    setDialogIsOpen,
    addErrorToast,
    addDeleteToast,
}: VisualizerDialogProps) => {
    let dialogProps: DialogProps = { icon: 'error', title: 'Error' };
    let dialogBody = <p>This wasn&apos;t supposed to happen. Please contact the developers.</p>;
    let succesButton = <></>;

    const [proof, setProof] = useState<proof>({ label: '', options: '', problem: '' });
    const [processingProof, setProcessingProof] = useState(false);
    const [proofProcessed, setProofProcessed] = useState(false);
    const handleSubmit = async (proof: proof) => {
        await axios
            .post('http://localhost:5000/proof/add', proof)
            .then(async (res) => {
                setProcessingProof(true);
                await axios.get(`http://localhost:5000/proof/process-proof/${res.data}`);
                setProofProcessed(true);
                return res.data;
            })
            .then(() => setProofProcessed(true))
            .catch((err) => {
                setProcessingProof(false);
                addErrorToast(err.response ? err.response.data.message : 'Error! =(');
            });
    };

    switch (dialogContent) {
        case 'proof-list':
            dialogProps = { icon: 'list', title: 'Proof List' };
            dialogBody = <ProofList addDeleteToast={addDeleteToast} setDialogIsOpen={setDialogIsOpen}></ProofList>;
            break;
        case 'new-proof':
            dialogProps = { icon: 'add', title: 'New Proof' };
            dialogBody = proofProcessed ? (
                <div style={{ textAlign: 'center', height: '200px', paddingTop: 50 }}>
                    <Icon icon="tick" intent={Intent.SUCCESS} iconSize={40}></Icon>
                    <br></br>
                    <br></br>
                    <p>Your proof is ready to be visualized!</p>
                </div>
            ) : processingProof ? (
                <div style={{ textAlign: 'center', height: '200px', paddingTop: 50 }}>
                    <p>Processing your proof...</p>
                    <Spinner size={30} />
                </div>
            ) : (
                <FormNewProof proof={proof} setProof={setProof}></FormNewProof>
            );
            succesButton =
                processingProof || proofProcessed ? (
                    <></>
                ) : (
                    <Button
                        onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                            e.preventDefault();
                            setProcessingProof(!processingProof);
                            handleSubmit({ label: proof.label, options: proof.options, problem: proof.problem });
                        }}
                        intent={Intent.SUCCESS}
                        disabled={processingProof || proof.label === '' || proof.problem === ''}
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
                onClose={(): void => {
                    setProof({ label: '', options: '', problem: '' });
                    setProcessingProof(false);
                    setProofProcessed(false);
                    setDialogIsOpen(false);
                }}
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
