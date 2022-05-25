import React, { useEffect, useReducer, useRef } from 'react';

import MonacoEditor from '@monaco-editor/react';
import { Drawer, Position, Classes, Button } from '@blueprintjs/core';
import { selectTheme } from '../../store/features/theme/themeSlice';
import { SmtDrawerProps } from '../../interfaces/interfaces';
import { useAppDispatch, useAppSelector } from '../../store/hooks';

import '../../scss/VisualizersDrawer.scss';
import { selectSmt, setSmt } from '../../store/features/proof/proofSlice';

const VisualizerSmtDrawer: React.FC<SmtDrawerProps> = ({ isOpen, setDrawerIsOpen }: SmtDrawerProps) => {
    const darkTheme = useAppSelector(selectTheme);
    const proofSmt = useAppSelector(selectSmt);
    const [, forceUpdate] = useReducer((x) => x + 1, 0);
    const textRef = useRef(proofSmt + '\n');

    const dispatch = useAppDispatch();
    useEffect(() => {
        if (isOpen) {
            textRef.current += '\n';
            forceUpdate();
        }
    }, [isOpen]);

    useEffect(() => {
        textRef.current = proofSmt;
        forceUpdate();
    }, [proofSmt]);

    const options = {
        theme: darkTheme ? 'vs-dark' : 'vs',
    };

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
            <div className={'smt-drawer ' + Classes.DRAWER_BODY}>
                <MonacoEditor
                    height={'300px'}
                    language="sb"
                    value={textRef.current}
                    onChange={(value) => value !== undefined && (textRef.current = value)}
                    onMount={() => {
                        textRef.current = textRef.current.substring(0, textRef.current.length - 1);
                        forceUpdate();
                    }}
                    options={options}
                />
                <Button
                    style={{ alignSelf: 'end', float: 'right', margin: '5px' }}
                    className="bp3-minimal"
                    icon="code"
                    text="Upload proof"
                    onClick={() => {
                        dispatch(setSmt(textRef.current));
                        // Run cvc5
                    }}
                />
            </div>
        </Drawer>
    );
};

export default VisualizerSmtDrawer;
