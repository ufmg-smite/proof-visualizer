import React, { useState } from 'react';
import { useAppDispatch, useAppSelector } from '../../store/hooks';
import { Dispatch, SetStateAction } from 'react';
import { MaybeElement } from '@blueprintjs/core/lib/esm/common/props';
import { IconName } from '@blueprintjs/core/lib/esm/components/icon/icon';

import { Button, Classes, Dialog, FileInput, Icon, Intent, Spinner } from '@blueprintjs/core';

import '../../scss/VisualizerDialog.scss';
import { selectTheme } from '../../store/features/theme/themeSlice';
import { set } from '../../store/features/file/fileSlice';
import { process } from '../../store/features/proof/proofSlice';
import Canvas from '../VisualizerStage/Canvas/VisualizerCanvas';

interface DialogProps {
    icon: IconName | MaybeElement;
    title: React.ReactNode;
}

interface VisualizerDialogProps {
    dialogIsOpen: boolean;
    setDialogIsOpen: Dispatch<SetStateAction<boolean>>;
    dialogContent: string;
    setDialogContent: Dispatch<SetStateAction<string>>;
    addErrorToast: (err: string) => void;
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
    const darkTheme = useAppSelector(selectTheme);

    let dialogProps: DialogProps = { icon: 'error', title: 'Error' };
    let dialogBody = <p>This wasn&apos;t supposed to happen. Please contact the developers.</p>;
    let succesButton = <></>;

    const [processingProof, setProcessingProof] = useState(false);
    const [proofProcessed, setProofProcessed] = useState(false);
    const [fileName, changeFileName] = useState('Choose file...');
    const [file, changeFile] = useState('');
    const dispatch = useAppDispatch();

    switch (dialogContent) {
        case 'welcome':
            dialogProps = { icon: 'graph', title: 'Welcome' };
            dialogBody = (
                <div className="welcome-menu">
                    <h2>Welcome to Proof Visualizer</h2>
                    <p>You can upload the DOT/JSON file of your proof.</p>
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
                        const target = e.target as HTMLInputElement;
                        const file = target.files ? target.files[0] : new File([''], 'filename');
                        if (
                            target.files &&
                            target.files[0] &&
                            target.files[0].name.split('.').slice(-1)[0] !== 'dot' &&
                            target.files[0].name.split('.').slice(-1)[0] !== 'json'
                        ) {
                            addErrorToast('Sorry! Our app only support DOT and JSON files.');
                            return;
                        }
                        try {
                            const fileContents = await readUploadedFileAsText(file);
                            changeFile(fileContents as string);
                            changeFileName(file.name);
                        } catch (er: any) {
                            addErrorToast(er.message);
                        }
                    }}
                    fill={true}
                />
            );
            succesButton = !proofProcessed ? (
                <Button
                    onClick={() => {
                        dispatch(set({ name: fileName, value: file }));

                        Canvas.allowRenderNewFile();
                        const ext = fileName.split('.').pop();
                        if (ext === 'json') Canvas.blockRender();
                        else if (ext === 'dot') Canvas.reRender();

                        setProofProcessed(true);
                        dispatch(process(file));
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
