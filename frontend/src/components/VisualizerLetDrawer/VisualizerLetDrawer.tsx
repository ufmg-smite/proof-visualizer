import React, { useEffect, useRef, useState } from 'react';
import { Button, Drawer, Classes, Position } from '@blueprintjs/core';

import Let from './let';
import '../../scss/Let.scss';
import { DrawerProps } from '../../interfaces/interfaces';
import { useAppSelector } from '../../store/hooks';
import { selectTheme } from '../../store/features/theme/themeSlice';
import { selectLetMap } from '../../store/features/proof/proofSlice';

const font =
    '14px / 18px -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Oxygen, Ubuntu, Cantarell, "Open Sans", "Helvetica Neue", Icons16, sans-serif';

const VisualizerLetDrawer: React.FC<DrawerProps> = ({ drawerIsOpen, setDrawerIsOpen }: DrawerProps) => {
    const darkTheme = useAppSelector(selectTheme);
    const letMap = useAppSelector(selectLetMap);
    const widthRef = useRef(0);

    const [letMapS, setLetMapS] = useState({ ...letMap });
    const [resizeMode, setResizeMode] = useState(0);
    const letsRef = useRef<{ [key: string]: Let }>({});

    // ComponentDidMount
    useEffect(() => {
        // Handler to call on window resize and set the value column width
        function handleResize() {
            const width = widthRef.current;

            // -22 from the fixed padding size
            const newWidth = document.getElementsByClassName('letMap-value-column')[0].clientWidth - 24;
            width === newWidth ? setResizeMode(1) : width > newWidth ? setResizeMode(0) : setResizeMode(2);

            widthRef.current = newWidth;
        }

        // Add event listener
        window.addEventListener('resize', handleResize);
        // Call handler right away so state gets updated with initial window size
        handleResize();

        // Remove event listener on cleanup
        return () => window.removeEventListener('resize', handleResize);
    }, []);

    const expandLet = (parent: string, key: string, letIdx: number) => {
        const lets = letsRef.current;

        const externalRef = lets[key];
        lets[parent].isExpanded = true;
        letMapS[parent] = lets[parent].expandPartialy(externalRef, letIdx);
        setLetMapS({ ...letMapS });
    };

    const expandAll = (key: string) => {
        const lets = letsRef.current;

        lets[key].isExpanded = true;
        letMapS[key] = lets[key].expandValue(true);
        setLetMapS({ ...letMapS });
    };

    const revertLet = (key: string) => {
        const lets = letsRef.current;

        // Only when is expanded
        if (lets[key].isExpanded) {
            lets[key].isExpanded = false;
            letMapS[key] = lets[key].shrinkValue();
            setLetMapS({ ...letMapS });
        }
    };

    const renderLet = (key: string): JSX.Element => {
        const lets = letsRef.current;
        const width = widthRef.current;

        // Waits for the width to be updated and the DOM element to be updated
        if (width) {
            let currentLet = letMapS[key];

            let indices: { [key: number]: string } = {};
            // Finds all occurences of let in the currentLet
            [...currentLet.matchAll(/let\d+/g)].forEach((match) => {
                if (match.index) indices[match.index] = match[0];
            });

            // If it's the first render (make sure that the lets obj is not calculated every time)
            if (Object.keys(lets).length !== Object.keys(letMapS).length) {
                lets[key] = new Let(key, currentLet, lets, indices);
            }

            // If doesn't fits, then indent
            if (!lets[key].fitsTheWindow(width, font)) {
                currentLet = lets[key].indent(width, true, font);
                letMapS[key] = currentLet;

                indices = {};
                // Finds all occurences of let in the currentLet after indentation
                [...currentLet.matchAll(/let\d+/g)].forEach((match) => {
                    if (match.index) indices[match.index] = match[0];
                });
            }
            // If fits
            else {
                // Only in the momment the page size is growing and the line is broken
                if (resizeMode >= 0 && lets[key].lines.length > 1) {
                    // Reset the line
                    lets[key].lines = [
                        { value: lets[key].isExpanded ? lets[key].groupUp() : lets[key].value, indentLevel: 0 },
                    ];
                    lets[key].biggerID = 0;

                    // Indent it again
                    currentLet = lets[key].indent(width, false, font);
                    letMapS[key] = currentLet;

                    indices = {};
                    // Finds all occurences of let in the currentLet after indentation
                    [...currentLet.matchAll(/let\d+/g)].forEach((match) => {
                        if (match.index) indices[match.index] = match[0];
                    });
                }
            }

            const arr: (JSX.Element | string)[] = [];
            let start = 0;
            // Slice the currentLet into an array with strings and JSX elements
            Object.keys(indices).forEach((index, i, self) => {
                const idx = Number(index);
                const thisLet = indices[idx];

                // Add the elements to the arr
                arr.push(currentLet.substring(start, idx));
                arr.push(
                    <a
                        className={darkTheme ? 'let-literal-or' : 'let-literal'}
                        onClick={() => {
                            expandLet(key, thisLet, idx);
                        }}
                    >
                        {thisLet}
                    </a>,
                );
                // Defines a new start
                start = idx + thisLet.length;

                // If it's the last let
                if (i === self.length - 1) {
                    arr.push(currentLet.substring(start, currentLet.length));
                }
            });

            // If there is a let in this current let
            if (Object.keys(indices).length) {
                return <span className="let-instance">{arr}</span>;
            } else {
                return <span className="let-instance">{currentLet}</span>;
            }
        }
        return <></>;
    };

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
                                <th className="letMap-value-column">Value</th>
                                <th style={{ width: '250px' }}>Action</th>
                            </tr>
                        </thead>
                        <tbody>
                            {Object.keys(letMapS).map((key) => {
                                return (
                                    <tr key={key}>
                                        <td>
                                            <strong>{key}</strong>
                                        </td>
                                        <td style={{ width: '100%', whiteSpace: 'pre-wrap' }}>{renderLet(key)}</td>
                                        <td style={{ width: '150px', height: '100%' }}>
                                            <Button
                                                onClick={() => expandAll(key)}
                                                className="bp3-minimal"
                                                icon="translate"
                                                text="Expand"
                                            />
                                            <Button
                                                onClick={() => revertLet(key)}
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
