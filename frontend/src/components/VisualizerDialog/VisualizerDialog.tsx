import React, { useState, useReducer, useEffect } from 'react';
import { useAppDispatch, useAppSelector } from '../../store/hooks';
import { MaybeElement } from '@blueprintjs/core/lib/esm/common/props';
import { IconName } from '@blueprintjs/core/lib/esm/components/icon/icon';

import { Button, Classes, Dialog, FileInput, Intent } from '@blueprintjs/core';

import '../../scss/VisualizerDialog.scss';
import { selectTheme } from '../../store/features/theme/themeSlice';
import { set } from '../../store/features/file/fileSlice';
import { process } from '../../store/features/proof/proofSlice';
import { allowRenderNewFile, blockRender, reRender } from '../../store/features/externalCmd/externalCmd';
import { VisualizerDialogProps } from '../../interfaces/interfaces';

interface DialogProps {
    icon: IconName | MaybeElement;
    title: React.ReactNode;
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
    setDialogIsOpen,
    addErrorToast,
}: VisualizerDialogProps) => {
    const darkTheme = useAppSelector(selectTheme);
    const dispatch = useAppDispatch();

    const [inputIsFocused, setInputIsFocused] = useState(false);
    const [fileName, changeFileName] = useState('Choose file...');
    const [file, changeFile] = useState('');
    const [[focusFlag, flagCount], setFocusFlag] = useReducer(
        (state: number[], newFlag: number): number[] => [newFlag, state[1] + 1],
        [0, 0],
    );

    useEffect(() => {
        if (dialogIsOpen) setFocusFlag(1);
    }, [dialogIsOpen]);

    useEffect(() => {
        let el;
        switch (focusFlag) {
            // Focus the file input
            case 1:
                el = document.getElementsByClassName(Classes.DIALOG_BODY + ' dialog-body');
                (el[0].childNodes[0] as HTMLElement).focus();
                break;
            // Focus the upload button
            case 2:
                el = document.getElementsByClassName(Classes.DIALOG_FOOTER_ACTIONS);
                (el[0].childNodes[0] as HTMLElement).focus();
                break;
        }
    }, [flagCount]);

    const closeDialog = () => {
        setDialogIsOpen(false);
        changeFileName('Choose file...');
        changeFile('');
    };

    const dialogProps: DialogProps = { icon: 'upload', title: 'Upload Proof' };
    const dialogBody = (
        <FileInput
            style={{ outline: inputIsFocused ? '1px white solid' : '', borderRadius: inputIsFocused ? '3px' : '' }}
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
                    // Make sure the file was selected and none error of "no
                    //  file select" will be prompted
                    if (file) {
                        const fileContents = await readUploadedFileAsText(file);
                        changeFile(fileContents as string);
                        changeFileName(file.name);

                        // If succeded, set the focus of the page to the upload button
                        setFocusFlag(2);
                    }
                } catch (er: any) {
                    addErrorToast(er.message);
                }
            }}
            fill={true}
            onFocus={(e) => {
                e.stopPropagation();
                setInputIsFocused(true);
            }}
            onBlur={(e) => {
                e.stopPropagation();
                setInputIsFocused(false);
            }}
        />
    );
    const succesButton = (
        <Button
            onClick={() => {
                dispatch(set({ name: fileName, value: file }));

                dispatch(allowRenderNewFile());
                const ext = fileName.split('.').pop();
                if (ext === 'json') dispatch(blockRender());
                else if (ext === 'dot') dispatch(reRender());

                dispatch(process(file));
                closeDialog();
            }}
            intent={Intent.SUCCESS}
            disabled={fileName === 'Choose file...'}
        >
            Upload Proof
        </Button>
    );

    return (
        <>
            <Dialog
                className={darkTheme ? ' bp3-dark' : ''}
                isOpen={dialogIsOpen}
                onClose={(): void => closeDialog()}
                usePortal={true}
                {...dialogProps}
            >
                <div className={Classes.DIALOG_BODY + ' dialog-body'}>{dialogBody}</div>
                <div className={Classes.DIALOG_FOOTER}>
                    <div className={Classes.DIALOG_FOOTER_ACTIONS}>{succesButton}</div>
                </div>
            </Dialog>
        </>
    );
};

export default VisualizerDialog;
