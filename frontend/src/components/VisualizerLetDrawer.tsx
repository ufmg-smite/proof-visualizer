import React, { useState } from 'react';
import { useSelector } from 'react-redux';
import { Dispatch, SetStateAction } from 'react';
import { Button, Drawer, Classes, Position } from '@blueprintjs/core';

import '../scss/VisualizerNavbar.scss';
import { stateInterface } from './interfaces';

interface letDrawerProps {
    letMap: {
        [Key: string]: string;
    };
    drawerIsOpen: boolean;
    setDrawerIsOpen: Dispatch<SetStateAction<boolean>>;
}

const VisualizerLetDrawer: React.FC<letDrawerProps> = ({ letMap, drawerIsOpen, setDrawerIsOpen }: letDrawerProps) => {
    const darkTheme = useSelector<stateInterface, boolean>((state: stateInterface) => state.darkThemeReducer.darkTheme);
    const [letMapS, setLetMapS] = useState(letMap);

    return (
        <Drawer
            className={darkTheme ? 'bp3-dark' : ''}
            style={{ maxHeight: '50%' }}
            autoFocus={true}
            canEscapeKeyClose={true}
            canOutsideClickClose={true}
            enforceFocus={true}
            hasBackdrop={false}
            isOpen={drawerIsOpen}
            position={Position.RIGHT}
            usePortal={true}
            onClose={(e) => {
                e.preventDefault();
                setDrawerIsOpen(false);
            }}
            icon="translate"
            title="Letification"
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
                                <th style={{ width: '30px' }}>Property</th>
                                <th>Value</th>
                                <th>Action</th>
                            </tr>
                        </thead>
                        <tbody>
                            {Object.keys(letMapS).map(function (key) {
                                return (
                                    <tr key={key}>
                                        <td>
                                            <strong>{key}</strong>
                                        </td>
                                        <td>{letMapS[key]}</td>
                                        <td>
                                            <Button
                                                onClick={() => {
                                                    const newLetMap = { ...letMapS };
                                                    let i = newLetMap[key].indexOf('let');
                                                    while (i !== -1) {
                                                        const l = newLetMap[key].slice(i).split(/[ |)]/)[0];
                                                        newLetMap[key] = newLetMap[key].replace(l, newLetMap[l]);
                                                        i = newLetMap[key].indexOf('let');
                                                    }
                                                    setLetMapS(newLetMap);
                                                }}
                                                className="bp3-minimal"
                                                icon="translate"
                                                text="Translate"
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
