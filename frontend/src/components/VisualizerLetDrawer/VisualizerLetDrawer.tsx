import React, { useEffect, useRef, useState } from 'react';
import { Button, Classes } from '@blueprintjs/core';

import Let from './let';
import '../../scss/Let.scss';
import { useAppSelector } from '../../store/hooks';
import { selectTheme } from '../../store/features/theme/themeSlice';
import { selectLetMap } from '../../store/features/proof/proofSlice';

const font =
    '14px / 18px -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Oxygen, Ubuntu, Cantarell, "Open Sans", "Helvetica Neue", Icons16, sans-serif';

const VisualizerLetDrawer: React.FC = () => {
    const darkTheme = useAppSelector(selectTheme);
    const widthRef = useRef(0);
    const [resizeMode, setResizeMode] = useState(0);

    const [letMap, setLetMap] = useState({ ...useAppSelector(selectLetMap) });
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

        // Init the let ref
        Object.keys(letMap).forEach((key) => {
            const currentLet = letMap[key];
            const indices: { [key: number]: string } = {};
            // Finds all occurences of let in the currentLet
            [...currentLet.matchAll(/let\d+/g)].forEach((match) => {
                if (match.index) indices[match.index] = match[0];
            });

            letsRef.current[key] = new Let(key, currentLet, letsRef.current, indices);
        });

        // Remove event listener on cleanup
        return () => window.removeEventListener('resize', handleResize);
    }, []);

    const expandLet = (parent: string, key: string, letIdx: number) => {
        const lets = letsRef.current;

        const externalRef = lets[key];
        lets[parent].isExpanded = true;
        letMap[parent] = lets[parent].expandPartialy(externalRef, letIdx);
        setLetMap({ ...letMap });
    };

    const expandAll = (key: string) => {
        const thisLet = letsRef.current[key];
        thisLet.isExpanded = true;
        letMap[key] = thisLet.expandValue(true);
        setLetMap({ ...letMap });
    };

    const revertLet = (key: string) => {
        const thisLet = letsRef.current[key];
        // Only when is expanded
        if (thisLet.isExpanded) {
            thisLet.isExpanded = false;
            letMap[key] = thisLet.shrinkValue();
            setLetMap({ ...letMap });
        }
    };

    const renderLet = (key: string): JSX.Element => {
        const lets = letsRef.current;
        const width = widthRef.current;

        // Waits for the width to be updated and the DOM element to be updated
        if (width) {
            let currentLet = letMap[key];
            const thisLet = lets[key];

            // If doesn't fits, then indent
            if (!thisLet.fitsTheWindow(width, font)) {
                currentLet = thisLet.indent(width, true, font);
                letMap[key] = currentLet;
            }
            // If fits, then only in the momment the page size is growing and the line is broken
            else if (resizeMode >= 0 && thisLet.lines.length > 1) {
                // Reset the line
                thisLet.lines = [{ value: thisLet.isExpanded ? thisLet.groupUp() : thisLet.value, indentLevel: 0 }];
                thisLet.biggerID = 0;

                // Indent it again
                currentLet = thisLet.indent(width, false, font);
                letMap[key] = currentLet;
            }

            // Finds all occurences of let in the currentLet
            const indices: { [key: number]: string } = {};
            [...currentLet.matchAll(/let\d+/g)].forEach((match) => {
                if (match.index) indices[match.index] = match[0];
            });

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
        <div className={Classes.DIALOG_BODY}>
            <table
                id="table-node-info-2"
                className="bp3-html-table bp3-html-table-bordered bp3-html-table-condensed bp3-html-table-striped"
                style={{ width: '100%' }}
            >
                <thead>
                    <tr>
                        <th style={{ width: '50px' }}>Property</th>
                        <th className="letMap-value-column">Value</th>
                        <th style={{ width: '100px' }}>Action</th>
                    </tr>
                </thead>
                <tbody>
                    {Object.keys(letMap).map((key, id) => {
                        return (
                            <tr key={id}>
                                <td>
                                    <strong>{key}</strong>
                                </td>
                                <td style={{ width: '100%', whiteSpace: 'pre-wrap' }}>{renderLet(key)}</td>
                                <td style={{ width: '100px', height: '100%' }}>
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
    );
};

export default VisualizerLetDrawer;
