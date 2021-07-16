import React, { Dispatch, SetStateAction, useState } from 'react';
import { useDispatch, useSelector } from 'react-redux';

import axios from 'axios';
import { Button, Classes, Dialog, FileInput, Intent, Spinner } from '@blueprintjs/core';
import { Icon } from '@blueprintjs/core/lib/esm/components/icon/icon';
import FormNewProof from './FormNewProof';

import '../scss/VisualizerDialog.scss';
import { proof, VisualizerDialogProps, DialogProps, stateInterface } from './interfaces';

function dialogBodyNewProof(
    proofProcessed: boolean,
    processingProof: boolean,
    proof: proof,
    setProof: Dispatch<SetStateAction<proof>>,
) {
    return proofProcessed ? (
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
}

const readUploadedFileAsText = (inputFile: File) => {
    const temporaryFileReader = new FileReader();

    return new Promise((resolve, reject) => {
        temporaryFileReader.onerror = () => {
            temporaryFileReader.abort();
            reject(new DOMException('Problem parsing input file.'));
        };

        temporaryFileReader.onload = () => {
            resolve(temporaryFileReader.result);
        };
        temporaryFileReader.readAsText(inputFile);
    });
};

const VisualizerDialog: React.FC<VisualizerDialogProps> = ({
    dialogIsOpen,
    dialogContent,
    setDialogContent,
    setDialogIsOpen,
    addErrorToast,
}: VisualizerDialogProps) => {
    const darkTheme = useSelector<stateInterface, boolean>((state: stateInterface) => state.darkThemeReducer.darkTheme);

    let dialogProps: DialogProps = { icon: 'error', title: 'Error' };
    let dialogBody = <p>This wasn&apos;t supposed to happen. Please contact the developers.</p>;
    let succesButton = <></>;

    const [proof, setProof] = useState<proof>({ _id: undefined, label: '', options: '', problem: '' });
    const [processingProof, setProcessingProof] = useState(false);
    const [proofProcessed, setProofProcessed] = useState(false);
    const [fileName, changeFileName] = useState('Choose file...');
    const [file, changeFile] = useState('');
    const dispatch = useDispatch();

    const handleSubmit = async (proof: proof) => {
        setProcessingProof(true);
        await axios
            .post('http://localhost:5000/proof/new-proof/', proof)
            .then(async (res) => {
                setProofProcessed(true);
                proof.dot = res.data;
                dispatch({ type: 'SET_PROOF', payload: proof });
            })
            .catch((err) => {
                setProcessingProof(false);
                addErrorToast(err.response ? err.response.data.message : 'Error! =(');
            });
    };

    switch (dialogContent) {
        case 'welcome':
            dialogProps = { icon: 'graph', title: 'Welcome' };
            dialogBody = (
                <div className="welcome-menu">
                    <h2>Welcome to Proof Visualizer</h2>
                    <p>Open or create a proof to begin exploring the app.</p>
                    <Button
                        style={{ width: '155px' }}
                        icon="add"
                        large
                        text="New proof"
                        onClick={() => setDialogContent('new-proof')}
                    />
                    <Button
                        style={{ width: '155px' }}
                        icon="upload"
                        large
                        text="Upload proof"
                        onClick={() => setDialogContent('upload-proof')}
                    />
                </div>
            );
            break;
        case 'new-proof':
            dialogProps = { icon: 'add', title: 'New Proof' };
            dialogBody = dialogBodyNewProof(proofProcessed, processingProof, proof, setProof);
            succesButton = !proofProcessed ? (
                <Button
                    onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                        e.preventDefault();
                        setProcessingProof(!processingProof);
                        handleSubmit({
                            _id: proof._id,
                            label: proof.label,
                            options: proof.options,
                            problem: proof.problem,
                        });
                    }}
                    intent={Intent.SUCCESS}
                    disabled={processingProof || proof.label === '' || proof.problem === ''}
                >
                    Generate Proof
                </Button>
            ) : (
                <></>
            );
            break;
        case 'upload-proof':
            dialogProps = { icon: 'upload', title: 'Upload Proof' };
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
                <FileInput
                    text={fileName}
                    hasSelection={fileName !== 'Choose file...'}
                    onInputChange={async (e) => {
                        const file = (e as any).target.files[0];
                        console.log((e as any).target.files[0]);
                        try {
                            const fileContents = await readUploadedFileAsText(file);
                            console.log(fileContents);
                            changeFile(fileContents as string);
                            setProof({
                                _id: undefined,
                                label: (e as any).target.files[0].name.split('.')[0],
                                options: '',
                                problem: '',
                            });
                        } catch (er) {
                            console.warn(er.message);
                        }
                        changeFileName((e as any).target.files[0].name);
                    }}
                    fill={true}
                />
            );
            succesButton = !proofProcessed ? (
                <Button
                    onClick={() => {
                        dispatch({ type: 'SET_PROOF', payload: proof });
                        setProcessingProof(true);
                        dispatch({ type: 'SET_DOT', payload: file });
                        setProofProcessed(true);
                    }}
                    intent={Intent.SUCCESS}
                    disabled={fileName === 'Choose file...'}
                >
                    Upload Proof
                </Button>
            ) : (
                <></>
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
                    changeFileName('Choose file...');
                    changeFile('');
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
                                setProof({ label: '', options: '', problem: '' });
                                setProcessingProof(false);
                                setProofProcessed(false);
                                setDialogIsOpen(false);
                                changeFileName('Choose file...');
                                changeFile('');
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
