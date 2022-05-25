import React, { useEffect, useState } from 'react';

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
    const [text, setText] = useState(proofSmt + '\n');

    const dispatch = useAppDispatch();
    useEffect(() => {
        if (isOpen) setText(text + '\n');
    }, [isOpen]);

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
                    value={text}
                    onChange={(value) => value !== undefined && setText(value)}
                    onMount={() => setText(text.substring(0, text.length - 1))}
                    options={options}
                />
                <Button
                    style={{ alignSelf: 'end', float: 'right' }}
                    className="bp3-minimal"
                    icon="code"
                    text="Upload proof"
                    onClick={() => {
                        dispatch(setSmt(text));
                        // Run cvc5
                    }}
                />
            </div>
        </Drawer>
    );
};

export default VisualizerSmtDrawer;
