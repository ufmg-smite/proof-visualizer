import React, { useEffect, useReducer, useRef, useState } from 'react';

import MonacoEditor from '@monaco-editor/react';
import { Drawer, Position, Classes, Button, FormGroup, Switch, Divider, InputGroup } from '@blueprintjs/core';
import { selectTheme } from '../../store/features/theme/themeSlice';
import { SmtDrawerProps } from '../../interfaces/interfaces';
import { useAppDispatch, useAppSelector } from '../../store/hooks';

import { selectSmt, setSmt } from '../../store/features/proof/proofSlice';

const VisualizerSmtDrawer: React.FC<SmtDrawerProps> = ({ isOpen, setDrawerIsOpen }: SmtDrawerProps) => {
    const darkTheme = useAppSelector(selectTheme);
    const proofSmt = useAppSelector(selectSmt);
    const [, forceUpdate] = useReducer((x) => x + 1, 0);
    const [optionsIsOpen, setOptionsIsOpen] = useReducer((open) => !open, true);
    const textRef = useRef(proofSmt + '\n');
    const [argsType, setArgsType] = useState(true);

    const dispatch = useAppDispatch();

    useEffect(() => {
        textRef.current = proofSmt;
        forceUpdate();
    }, [proofSmt]);

    const options = {
        theme: darkTheme ? 'vs-dark' : 'vs',
    };
    const divColor = darkTheme ? 'rgb(255, 255, 255, 0.15)' : 'rgb(0, 0, 0, 0.15)';

    return (
        <Drawer
            className={darkTheme ? 'bp3-dark' : ''}
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
            <div className={'smt-drawer ' + Classes.DRAWER_BODY} style={{ overflow: 'hidden' }}>
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
                        position: 'relative',
                        height: optionsIsOpen ? '200px' : '0',
                        transition: 'height 1s ease-out',
                        overflow: 'auto',
                    }}
                >
                    <Switch
                        label="Default args or custom args"
                        style={{ margin: '10px 20px' }}
                        checked={argsType}
                        onChange={() => setArgsType(!argsType)}
                    />
                    <FormGroup
                        label="Proof options"
                        style={{
                            padding: '10px 20px',
                            borderBottom: `1px solid ${divColor}`,
                            borderTop: `1px solid ${divColor}`,
                            marginBottom: '0',
                        }}
                        disabled={!argsType}
                    >
                        <Switch label="Should clusterize proof" disabled={!argsType} />
                        <Switch label="Should traverse as tree or as DAG" disabled={!argsType} />
                    </FormGroup>
                    <FormGroup
                        label="Proof options"
                        style={{ padding: '10px 20px', marginBottom: '0' }}
                        disabled={argsType}
                    >
                        <InputGroup id="text-input" placeholder="Placeholder text" disabled={argsType} />
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
                    />
                    <Button
                        style={{ float: 'right', margin: '5px' }}
                        className="bp3-minimal"
                        icon="code"
                        text="Upload proof"
                        onClick={() => {
                            dispatch(setSmt(textRef.current));
                            // Run cvc5
                        }}
                    />
                    <Button
                        style={{ float: 'right', margin: '5px' }}
                        className="bp3-minimal"
                        icon="floppy-disk"
                        text="Save"
                        onClick={() => dispatch(setSmt(textRef.current))}
                    />
                </footer>
            </div>
        </Drawer>
    );
};

export default VisualizerSmtDrawer;
