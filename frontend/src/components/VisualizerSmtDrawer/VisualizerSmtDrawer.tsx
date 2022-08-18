import React, { useEffect, useReducer, useRef, useState } from 'react';

import MonacoEditor from '@monaco-editor/react';
import { Drawer, Position, Classes, Button, FormGroup, Switch, InputGroup } from '@blueprintjs/core';
import { Popover2 } from '@blueprintjs/popover2';

import { selectTheme } from '../../store/features/theme/themeSlice';
import { SmtDrawerProps } from '../../interfaces/interfaces';
import { useAppDispatch, useAppSelector } from '../../store/hooks';

import { process, selectSmt, setSmt } from '../../store/features/proof/proofSlice';
import Module from '../../wasm/cvc5';
import { set } from '../../store/features/file/fileSlice';
import { allowRenderNewFile, reRender, setSpinner } from '../../store/features/externalCmd/externalCmd';

import '../../scss/VisualizerSmtDrawer.scss';

const VisualizerSmtDrawer: React.FC<SmtDrawerProps> = ({
    isOpen,
    setDrawerIsOpen,
    addErrorToast,
    smtOptions,
    setSmtOptions,
}: SmtDrawerProps) => {
    const darkTheme = useAppSelector(selectTheme);
    const proofSmt = useAppSelector(selectSmt);

    const stdoutRef = useRef('');
    const stderrRef = useRef('');
    const changeOutRef = useRef(false);

    const [updateCounter, forceUpdate] = useReducer((x) => x + 1, 0);
    const [errorCounter, forceError] = useReducer((x) => x + 1, 0);
    const [optionsIsOpen, setOptionsIsOpen] = useReducer((open) => !open, false);
    const textRef = useRef(proofSmt + '\n');
    const [argsType, setArgsType] = useState(smtOptions.argsType);
    const [[shouldClusterize, printAsDag], setDefaultOptions] = useState([true, true]);
    const [customArgs, setCustomArgs] = useState(smtOptions.customArgs);
    const [err, setErr] = useState('');

    // The default arguments used in the proof generation
    const defaultArgs = ['--dump-proofs', '--proof-format=dot', '--proof-granularity=theory-rewrite', '--dag-thresh=0'];

    const dispatch = useAppDispatch();

    useEffect(() => {
        // When smt drawer is initialized it focus the escape button
        const bt = document
            .getElementsByClassName('smt-drawer')[0]
            .getElementsByClassName('bp3-button')[0] as HTMLElement;
        bt.tabIndex = 1;
        bt.focus();

        // Remove the overlay when oppening the smt drawer
        const parent = document.getElementsByClassName('smt-drawer')[0].parentElement;
        if (parent) parent.className = '';
    }, []);

    useEffect(() => {
        textRef.current = proofSmt;
        forceUpdate();
    }, [proofSmt]);

    useEffect(() => {
        // If it's custom args
        if (!argsType && updateCounter) {
            // Copy the default args to the custom args, because the probability
            // that the user will use one of these flags is high
            let newArgs = defaultArgs.reduce((acc, arg) => (acc += arg + ' '), '');
            if (shouldClusterize) newArgs += ' --print-dot-clusters';
            if (printAsDag) newArgs += ' --proof-dot-dag';
            setCustomArgs(newArgs);
        }
    }, [argsType]);

    useEffect(() => {
        // When component unmount, make sure that the custom args are saved
        return () => {
            setSmtOptions({ argsType, customArgs });
        };
    }, [argsType, customArgs]);

    useEffect(() => {
        if (errorCounter) addErrorToast(err);
    }, [errorCounter]);

    const options = {
        theme: darkTheme ? 'vs-dark' : 'vs',
        tabIndex: 5,
    };

    const divColor = darkTheme ? 'rgb(255, 255, 255, 0.15)' : 'rgb(0, 0, 0, 0.15)';

    const helpDiv = (
        <div
            className={`bp3-menu ${darkTheme ? 'bp3-dark' : ''}`}
            style={{
                maxWidth: '200px',
                padding: '5px 8px !important',
                boxShadow: '0px 0px 15px rgba(0, 0, 0, 0.651)',
                textAlign: 'justify',
            }}
        >
            Look at{' '}
            <a href="https://cvc5.github.io/docs/cvc5-1.0.0/options.html" target="_blank" rel="noreferrer">
                CVC5 documentation
            </a>{' '}
            to understand more about the argument parser.
        </div>
    );

    const defaultArgsDiv = (
        <div id="helperDiv" className={`bp3-menu ${darkTheme ? 'bp3-dark' : ''}`}>
            Default arguments are:{' '}
            {defaultArgs.reduce((acc: any, str: string) => {
                return (acc += str + ' ');
            }, '')}
        </div>
    );

    const shouldClusterizeDiv = (
        <div id="helperDiv" className={`bp3-menu ${darkTheme ? 'bp3-dark' : ''}`}>
            Whether the proof node clusters (e.g. SAT, CNF, INPUT) will be printed when using the dot format or not.
        </div>
    );

    const printAsDagDiv = (
        <div id="helperDiv" className={`bp3-menu ${darkTheme ? 'bp3-dark' : ''}`}>
            Indicates if the dot proof will be printed as a DAG or as a tree.
        </div>
    );

    // Remove the cvc5> prompt message from the stdout
    const sanitizeDotResult = (result: string): string => result.replaceAll(/(cvc5> )+/g, '');
    const updateStdout = (str: string) => (stdoutRef.current += str + '\n');
    const updateStderr = (str: string) => (stderrRef.current += str + '\n');
    // Function called post the cvc5 execution
    const postCVC5run = (isThereError: boolean) => {
        // Sanitize the string
        stdoutRef.current = sanitizeDotResult(stdoutRef.current).trim();
        // If there was an error
        if (isThereError && !stdoutRef.current.length) {
            // Change the spin message to render
            dispatch(setSpinner('off'));

            setErr(
                stderrRef.current.length
                    ? stderrRef.current
                    : 'Error: Unknown error, check out the arguments parsed or the smt text.',
            );
            forceError();
        }
        // Get the result .dot
        else {
            dispatch(set({ name: 'own-proof.dot', value: stdoutRef.current }));

            dispatch(allowRenderNewFile());
            dispatch(reRender());

            dispatch(process(stdoutRef.current));

            // Change the spin message to render
            dispatch(setSpinner('render'));
        }
    };
    // Clean the output a single time during the cvc5 execution
    const cleanStdout = () => {
        if (!changeOutRef.current) {
            stdoutRef.current = '';
            changeOutRef.current = true;
        }
    };

    return (
        <Drawer
            className={`smt-drawer ${darkTheme ? 'bp3-dark' : ''}`}
            style={{ maxHeight: '65%', width: '35%' }}
            autoFocus={true}
            canEscapeKeyClose={true}
            canOutsideClickClose={false}
            enforceFocus={false}
            hasBackdrop={false}
            isOpen={isOpen}
            position={Position.LEFT}
            usePortal={false}
            onClose={(e) => {
                e.preventDefault();
                setDrawerIsOpen(false);
                // Save the smt
                dispatch(setSmt(textRef.current));
            }}
            icon="code"
            title="SMT Input"
        >
            <div className={Classes.DRAWER_BODY} style={{ overflow: 'hidden' }}>
                <MonacoEditor
                    height={'300px'}
                    language="graphql"
                    value={textRef.current}
                    onChange={(value) => value !== undefined && (textRef.current = value)}
                    onMount={() => forceUpdate()}
                    options={options}
                />
                <div className={optionsIsOpen ? 'options-sec' : 'options-sec-open'}>
                    <Switch
                        label="Default args or custom args"
                        style={{ margin: '10px 20px' }}
                        checked={argsType}
                        onChange={() => setArgsType(!argsType)}
                        tabIndex={4}
                    />
                    <FormGroup
                        label={
                            <div>
                                Default args:{' '}
                                <Popover2
                                    disabled={!argsType}
                                    content={defaultArgsDiv}
                                    placement="auto"
                                    modifiers={{ arrow: { enabled: true } }}
                                    hoverCloseDelay={200}
                                    hoverOpenDelay={200}
                                >
                                    <Button disabled={!argsType} icon="help" className="bp3-minimal" tabIndex={4} />
                                </Popover2>
                            </div>
                        }
                        className="args-forms"
                        style={{ borderBottom: `1px solid ${divColor}`, borderTop: `1px solid ${divColor}` }}
                        disabled={!argsType}
                    >
                        <div className="default-option-div">
                            <Switch
                                label="Should clusterize proof"
                                disabled={!argsType}
                                checked={shouldClusterize}
                                onChange={() => setDefaultOptions([!shouldClusterize, printAsDag])}
                                tabIndex={4}
                            />
                            <Popover2
                                disabled={!argsType}
                                content={shouldClusterizeDiv}
                                placement="auto"
                                modifiers={{ arrow: { enabled: true } }}
                                hoverCloseDelay={200}
                                hoverOpenDelay={200}
                            >
                                <Button disabled={!argsType} icon="help" className="bp3-minimal" tabIndex={4} />
                            </Popover2>
                        </div>
                        <div className="default-option-div">
                            <Switch
                                label="Should print as tree or as DAG"
                                disabled={!argsType}
                                checked={printAsDag}
                                onChange={() => setDefaultOptions([shouldClusterize, !printAsDag])}
                                tabIndex={4}
                            />
                            <Popover2
                                disabled={!argsType}
                                content={printAsDagDiv}
                                placement="auto"
                                modifiers={{ arrow: { enabled: true } }}
                                hoverCloseDelay={200}
                                hoverOpenDelay={200}
                            >
                                <Button disabled={!argsType} icon="help" className="bp3-minimal" tabIndex={4} />
                            </Popover2>
                        </div>
                    </FormGroup>
                    <FormGroup label="Custom args" className="args-forms" disabled={argsType}>
                        <InputGroup
                            id="text-input"
                            placeholder="Placeholder text"
                            disabled={argsType}
                            rightElement={
                                <Popover2
                                    disabled={argsType}
                                    content={helpDiv}
                                    placement="auto"
                                    modifiers={{ arrow: { enabled: true } }}
                                    hoverCloseDelay={200}
                                    hoverOpenDelay={200}
                                >
                                    <Button disabled={argsType} icon="help" className="bp3-minimal" tabIndex={4} />
                                </Popover2>
                            }
                            value={customArgs}
                            onChange={(e) => setCustomArgs(e.target.value)}
                            tabIndex={4}
                        />
                    </FormGroup>
                </div>
                <footer
                    style={{
                        position: 'relative',
                        borderTop: optionsIsOpen ? `solid 1px ${divColor}` : '',
                    }}
                >
                    <Button
                        style={{ float: 'left' }}
                        className="bp3-minimal margin-5"
                        icon="more"
                        text="Options"
                        onClick={() => setOptionsIsOpen()}
                        tabIndex={1}
                    />
                    <div style={{ float: 'right', display: 'flex' }}>
                        <Button
                            className="bp3-minimal margin-5"
                            icon="code"
                            text="Generate proof"
                            onClick={() => {
                                dispatch(setSmt(textRef.current));

                                let args = defaultArgs;
                                // If is default args
                                if (argsType) {
                                    // Add the arguments selected by the user
                                    if (shouldClusterize) args.push('--print-dot-clusters');
                                    if (printAsDag) args.push('--proof-dot-dag');
                                }
                                // Custom args
                                else {
                                    // Split the arguments into an array
                                    args = customArgs.split('--');
                                    args = args
                                        .map((arg) => arg.trim())
                                        .filter((arg) => {
                                            return arg.length !== 0;
                                        })
                                        .map((arg) => '--' + arg);

                                    let i = 0;
                                    // Make sure that the output format is .dot
                                    const isThereFormat = args.some((arg, id) => {
                                        i = id;
                                        return arg.indexOf('--proof-format') !== -1;
                                    });
                                    // If there isn't a proof format
                                    if (!isThereFormat) args.push('--proof-format=dot');
                                    // Verify is the format is the correct one
                                    else if (!args[i].match(/--proof-format\s*=\s*dot/)) {
                                        args[i] = '--proof-format=dot';
                                    }
                                }

                                // Reset the stdout and stderr before executing cvc5
                                stdoutRef.current = '';
                                stderrRef.current = '';
                                changeOutRef.current = false;

                                // Only calls web assembly when there is some text on the code editor
                                if (textRef.current.trim().length) {
                                    dispatch(setSpinner('cvc5'));

                                    // Run cvc5
                                    Module({
                                        arguments: args,
                                        proofTxt: textRef.current,
                                        out: updateStdout,
                                        err: updateStderr,
                                        postCVC5: postCVC5run,
                                        cleanStdout: cleanStdout,
                                        binaryFileName: 'cvc5.wasm',
                                    });
                                }
                                // There isn't text in the code editor
                                else {
                                    addErrorToast('Error: Empty proof in the code editor.');
                                }
                            }}
                            tabIndex={3}
                        />
                    </div>
                </footer>
            </div>
        </Drawer>
    );
};

export default VisualizerSmtDrawer;
