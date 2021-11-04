import React, { useState } from 'react';
import { Dispatch, SetStateAction } from 'react';
import { Button, Drawer, Classes, Position } from '@blueprintjs/core';

import { useAppSelector } from '../app/hooks';
import { selectTheme } from '../features/theme/themeSlice';
import { selectLetMap } from '../features/proof/proofSlice';

interface letDrawerProps {
    drawerIsOpen: boolean;
    setDrawerIsOpen: Dispatch<SetStateAction<boolean>>;
}

const indent = (s: string) => {
    let newS = s.replaceAll(' ', '\n');
    let i = 0;
    let pCounter = 0;
    while (i < newS.length) {
        if (newS[i] === '(') pCounter++;
        else if (newS[i] === ')') pCounter--;
        else if (newS[i] === '\n') {
            if (newS[i + 1] === ')') {
                newS = [newS.slice(0, i + 1), '    '.repeat(pCounter - 1), newS.slice(i + 1)].join('');
                i += pCounter - 1;
            } else {
                newS = [newS.slice(0, i + 1), '    '.repeat(pCounter), newS.slice(i + 1)].join('');
                i += pCounter;
            }
        }
        i++;
    }
    return newS;
};

const VisualizerLetDrawer: React.FC<letDrawerProps> = ({ drawerIsOpen, setDrawerIsOpen }: letDrawerProps) => {
    const darkTheme = useAppSelector(selectTheme);
    const letMap = useAppSelector(selectLetMap);
    const [letMapS, setLetMapS] = useState(letMap);

    return (
        <Drawer
            className={darkTheme ? 'bp3-dark' : ''}
            style={{ maxHeight: '65%', width: '35%' }}
            autoFocus={true}
            canEscapeKeyClose={true}
            canOutsideClickClose={false}
            enforceFocus={true}
            hasBackdrop={false}
            isOpen={drawerIsOpen}
            position={Position.RIGHT}
            usePortal={false}
            onClose={(e) => {
                e.preventDefault();
                setDrawerIsOpen(false);
            }}
            icon="translate"
            title="Let Map"
        >
            <div className={Classes.DRAWER_BODY}>
                <div className={Classes.DIALOG_BODY}>
                    <table
                        id="table-node-info"
                        className="bp3-html-table bp3-html-table-bordered bp3-html-table-condensed bp3-html-table-striped"
                        style={{ width: '100%' }}
                    >
                        <thead>
                            <tr>
                                <th style={{ width: '100px' }}>Property</th>
                                <th>Value</th>
                                <th style={{ width: '250px' }}>Action</th>
                            </tr>
                        </thead>
                        <tbody>
                            {Object.keys(letMapS).map(function (key) {
                                return (
                                    <tr key={key}>
                                        <td>
                                            <strong>{key}</strong>
                                        </td>
                                        <td style={{ width: '100%', whiteSpace: 'pre-wrap' }}>
                                            {indent(letMapS[key])
                                                .split('\n')
                                                .map((e) => {
                                                    if (e.indexOf(' let') === -1) {
                                                        return <span>{e + '\n'}</span>;
                                                    } else {
                                                        return (
                                                            <span
                                                                onClick={() => {
                                                                    const newLetMap = { ...letMapS };
                                                                    const i = newLetMap[key].indexOf(
                                                                        e.replace(/^\s+|\s+$/g, ''),
                                                                    );
                                                                    const l = newLetMap[key].slice(i).split(/[ |)]/)[0];
                                                                    newLetMap[key] = newLetMap[key].replace(
                                                                        l,
                                                                        letMap[l],
                                                                    );
                                                                    setLetMapS(newLetMap);
                                                                }}
                                                            >
                                                                {e + '\n'}
                                                            </span>
                                                        );
                                                    }
                                                })}
                                        </td>
                                        <td style={{ width: '150px', display: 'flex', flexDirection: 'column' }}>
                                            <Button
                                                onClick={() => {
                                                    const newLetMap = { ...letMapS };
                                                    let i = newLetMap[key].indexOf('let');
                                                    while (i !== -1) {
                                                        const l = newLetMap[key].slice(i).split(/[ |)]/)[0];
                                                        newLetMap[key] = newLetMap[key].replace(l, letMap[l]);
                                                        i = newLetMap[key].indexOf('let');
                                                    }
                                                    setLetMapS(newLetMap);
                                                }}
                                                className="bp3-minimal"
                                                icon="translate"
                                                text="Expand"
                                            />
                                            <Button
                                                onClick={() => {
                                                    const newLetMap = { ...letMapS };
                                                    newLetMap[key] = letMap[key];
                                                    setLetMapS(newLetMap);
                                                }}
                                                className="bp3-minimal"
                                                icon="undo"
                                                text="Revert"
                                            />
                                        </td>
                                    </tr>
                                );
                            })}
                        </tbody>
                    </table>
                </div>
            </div>
        </Drawer>
    );
};

export default VisualizerLetDrawer;
