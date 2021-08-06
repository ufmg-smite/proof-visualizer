import React, { useState } from 'react';
import { useSelector } from 'react-redux';
import { Dispatch, SetStateAction } from 'react';
import { Button, Drawer, Classes, Position } from '@blueprintjs/core';

import { stateInterface } from './interfaces';

import Sexprs from './functions/sFormatter';

interface letDrawerProps {
    drawerIsOpen: boolean;
    setDrawerIsOpen: Dispatch<SetStateAction<boolean>>;
}

const indent = (s: string) => {
    return Sexprs().stringify(Sexprs().parse(s));
};

const VisualizerLetDrawer: React.FC<letDrawerProps> = ({ drawerIsOpen, setDrawerIsOpen }: letDrawerProps) => {
    const darkTheme = useSelector<stateInterface, boolean>((state: stateInterface) => state.darkThemeReducer.darkTheme);
    const letMap = useSelector<
        stateInterface,
        {
            [Key: string]: string;
        }
    >((state: stateInterface) => state.letMapReducer.letMap);
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
                                            {Sexprs().stringify(
                                                Sexprs().parse(
                                                    letMapS[key].split('\n').map((e: string) => {
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
                                                                        const l = newLetMap[key]
                                                                            .slice(i)
                                                                            .split(/[ |)]/)[0];
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
                                                    }),
                                                ),
                                            )}
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
