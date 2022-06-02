import React, { useEffect, useReducer, useRef, useState } from 'react';

import MonacoEditor from '@monaco-editor/react';
import { Drawer, Position, Classes, Button, FormGroup, Switch, InputGroup } from '@blueprintjs/core';
import { Popover2 } from '@blueprintjs/popover2';

import { selectTheme } from '../../store/features/theme/themeSlice';
import { SmtDrawerProps } from '../../interfaces/interfaces';
import { useAppDispatch, useAppSelector } from '../../store/hooks';

import { selectSmt, setSmt } from '../../store/features/proof/proofSlice';

const VisualizerSmtDrawer: React.FC<SmtDrawerProps> = ({ isOpen, setDrawerIsOpen }: SmtDrawerProps) => {
    const darkTheme = useAppSelector(selectTheme);
    const proofSmt = useAppSelector(selectSmt);

    const [, forceUpdate] = useReducer((x) => x + 1, 0);
    const [optionsIsOpen, setOptionsIsOpen] = useReducer((open) => !open, false);
    const textRef = useRef(proofSmt + '\n');
    const [argsType, setArgsType] = useState(true);
    const [[shouldClusterize, printAsDag], setDefaultOptions] = useState([true, true]);
    const [customArgs, setCustomArgs] = useState('');

    const dispatch = useAppDispatch();

    useEffect(() => {
        // When smt drawer is initialized it focus the escape button
        const bt = document
            .getElementsByClassName('smt-drawer')[0]
            .getElementsByClassName('bp3-button')[0] as HTMLElement;
        bt.tabIndex = 1;
        bt.focus();
    }, []);

    useEffect(() => {
        textRef.current = proofSmt;
        forceUpdate();
    }, [proofSmt]);

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
            <a href="https://cvc5.github.io/docs/cvc5-1.0.0/" target="_blank" rel="noreferrer">
                CVC5 documentation
            </a>{' '}
            to understand more about the argument parser.
        </div>
    );

    return (
        <Drawer
            className={`smt-drawer ${darkTheme ? 'bp3-dark' : ''}`}
            style={{ maxHeight: '65%', width: '35%' }}
            autoFocus={true}
            canEscapeKeyClose={true}
            canOutsideClickClose={true}
            enforceFocus={false}
            hasBackdrop={false}
            isOpen={isOpen}
            position={Position.LEFT}
            usePortal={false}
            onClose={(e) => {
                e.preventDefault();
                setDrawerIsOpen();
            }}
            icon="applications"
            title="Visualizers"
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
                <div
                    style={{
                        height: optionsIsOpen ? '220px' : '0',
                        position: 'relative',
                        overflow: 'auto',
                        transition: 'height 0.24s ease-out',
                        visibility: optionsIsOpen ? 'visible' : 'hidden',
                    }}
                >
                    <Switch
                        className="switch"
                        label="Default args or custom args"
                        style={{ margin: '10px 20px' }}
                        checked={argsType}
                        onChange={() => setArgsType(!argsType)}
                        tabIndex={4}
                    />
                    <FormGroup
                        label="Default args"
                        style={{
                            padding: '10px 20px',
                            borderBottom: `1px solid ${divColor}`,
                            borderTop: `1px solid ${divColor}`,
                            marginBottom: '0',
                        }}
                        disabled={!argsType}
                    >
                        <Switch
                            label="Should clusterize proof"
                            disabled={!argsType}
                            checked={shouldClusterize}
                            onChange={() => setDefaultOptions([!shouldClusterize, printAsDag])}
                            tabIndex={4}
                        />
                        <Switch
                            label="Should print as tree or as DAG"
                            disabled={!argsType}
                            checked={printAsDag}
                            onChange={() => setDefaultOptions([shouldClusterize, !printAsDag])}
                            tabIndex={4}
                        />
                    </FormGroup>
                    <FormGroup
                        label="Custom args"
                        style={{ padding: '10px 20px', marginBottom: '0' }}
                        disabled={argsType}
                    >
                        <InputGroup
                            id="text-input"
                            placeholder="Placeholder text"
                            disabled={argsType}
                            rightElement={
                                <Popover2
                                    disabled={argsType}
                                    content={helpDiv}
                                    placement="auto"
                                    modifiers={{
                                        arrow: { enabled: true },
                                    }}
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
                        style={{ float: 'left', margin: '5px' }}
                        className="bp3-minimal"
                        icon="more"
                        text="Options"
                        onClick={() => setOptionsIsOpen()}
                        tabIndex={1}
                    />
                    <div style={{ float: 'right', display: 'flex' }}>
                        <Button
                            style={{ margin: '5px' }}
                            className="bp3-minimal"
                            icon="floppy-disk"
                            text="Save"
                            onClick={() => dispatch(setSmt(textRef.current))}
                            tabIndex={2}
                        />
                        <Button
                            style={{ margin: '5px' }}
                            className="bp3-minimal"
                            icon="code"
                            text="Generate proof"
                            onClick={() => {
                                dispatch(setSmt(textRef.current));
                                // Run cvc5
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
