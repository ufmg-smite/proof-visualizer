import React, { useEffect, useRef, useState } from 'react';
import { Button, Classes } from '@blueprintjs/core';
import { selectLetMap, selectTheoryLemmas } from '../../store/features/proof/proofSlice';
import { useAppSelector } from '../../store/hooks';
import Let from '../VisualizerLetDrawer/let';
import { selectTheme } from '../../store/features/theme/themeSlice';

const font =
    '14px / 18px -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Oxygen, Ubuntu, Cantarell, "Open Sans", "Helvetica Neue", Icons16, sans-serif';

const VisualizerTheoryLemma: React.FC = () => {
    const darkTheme = useAppSelector(selectTheme);
    const theoryLemmas = useAppSelector(selectTheoryLemmas);
    const letMap = useAppSelector(selectLetMap);
    const widthRef = useRef(0);

    const [tLemmaS, setTLemmaS] = useState([...theoryLemmas]);
    const [resizeMode, setResizeMode] = useState(0);
    const letsRef = useRef<{ [key: string]: Let }>({});
    const tlRef = useRef<Let[]>([]);

    // ComponentDidMount
    useEffect(() => {
        // Handler to call on window resize and set the value column width
        function handleResize() {
            const width = widthRef.current;

            // -22 from the fixed padding size
            const newWidth = document.getElementsByClassName('theoryLemma-value-column')[0].clientWidth - 24;
            width === newWidth ? setResizeMode(1) : width > newWidth ? setResizeMode(0) : setResizeMode(2);

            widthRef.current = newWidth;
        }

        // Add event listener
        window.addEventListener('resize', handleResize);
        // Call handler right away so state gets updated with initial window size
        handleResize();

        // Init the lets
        Object.keys(letMap).forEach((key) => {
            const currentLet = letMap[key];

            const indices: { [key: number]: string } = {};
            // Finds all occurences of let in the currentLet
            [...currentLet.matchAll(/let\d+/g)].forEach((match) => {
                if (match.index) indices[match.index] = match[0];
            });
            letsRef.current[key] = new Let(key, currentLet, letsRef.current, indices);
        });

        // Init the theory lemmas
        theoryLemmas.forEach((tl, id) => {
            const indices: { [key: number]: string } = {};
            // Finds all occurences of let in the currentTL
            [...tl.matchAll(/let\d+/g)].forEach((match) => {
                if (match.index) indices[match.index] = match[0];
            });
            tlRef.current.push(new Let(String(id), tl, letsRef.current, indices));
        });

        // Remove event listener on cleanup
        return () => window.removeEventListener('resize', handleResize);
    }, []);

    const expandLet = (parent: number, key: string, letIdx: number) => {
        const lets = letsRef.current;
        const tls = tlRef.current;
        const externalRef = lets[key];
        tls[parent].isExpanded = true;
        tLemmaS[parent] = tls[parent].expandPartialy(externalRef, letIdx);
        setTLemmaS([...tLemmaS]);
    };

    const expandAll = (key: number) => {
        const tls = tlRef.current;
        tls[key].isExpanded = true;
        tLemmaS[key] = tls[key].expandValue(true);
        setTLemmaS([...tLemmaS]);
    };

    const revertLet = (key: number) => {
        const tls = tlRef.current;
        // Only when is expanded
        if (tls[key].isExpanded) {
            tls[key].isExpanded = false;
            tLemmaS[key] = tls[key].shrinkValue();
            setTLemmaS([...tLemmaS]);
        }
    };

    const renderLet = (key: number): JSX.Element => {
        const tls = tlRef.current;
        const width = widthRef.current;

        // Waits for the width to be updated and the DOM element to be updated
        if (width) {
            let currentTL = tLemmaS[key];

            let indices: { [key: number]: string } = {};
            // Finds all occurences of let in the currentTL
            [...currentTL.matchAll(/let\d+/g)].forEach((match) => {
                if (match.index) indices[match.index] = match[0];
            });

            // If doesn't fits, then indent
            if (!tls[key].fitsTheWindow(width, font)) {
                currentTL = tls[key].indent(width, true, font);
                tLemmaS[key] = currentTL;

                indices = {};
                // Finds all occurences of let in the currentTL after indentation
                [...currentTL.matchAll(/let\d+/g)].forEach((match) => {
                    if (match.index) indices[match.index] = match[0];
                });
            }
            // If fits
            else {
                // Only in the momment the page size is growing and the line is broken
                if (resizeMode >= 0 && tls[key].lines.length > 1) {
                    // Reset the line
                    tls[key].lines = [
                        { value: tls[key].isExpanded ? tls[key].groupUp() : tls[key].value, indentLevel: 0 },
                    ];
                    tls[key].biggerID = 0;

                    // Indent it again
                    currentTL = tls[key].indent(width, false, font);
                    tLemmaS[key] = currentTL;

                    indices = {};
                    // Finds all occurences of let in the currentTL after indentation
                    [...currentTL.matchAll(/let\d+/g)].forEach((match) => {
                        if (match.index) indices[match.index] = match[0];
                    });
                }
            }

            const arr: (JSX.Element | string)[] = [];
            let start = 0;
            // Slice the currentTL into an array with strings and JSX elements
            Object.keys(indices).forEach((index, i, self) => {
                const idx = Number(index);
                const thisLet = indices[idx];

                // Add the elements to the arr
                arr.push(currentTL.substring(start, idx));
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
                    arr.push(currentTL.substring(start, currentTL.length));
                }
            });

            // If there is a let in this current let
            if (Object.keys(indices).length) {
                return <span className="let-instance">{arr}</span>;
            } else {
                return <span className="let-instance">{currentTL}</span>;
            }
        }
        return <></>;
    };

    return (
        <div className={Classes.DIALOG_BODY}>
            <table
                id="table-node-info-2"
                className="bp3-html-table bp3-html-table-bordered bp3-html-table-condensed bp3-html-table-striped"
                style={{ width: '100%', minWidth: '230px' }}
            >
                <thead>
                    <tr>
                        <th className="theoryLemma-value-column">Value</th>
                        <th style={{ width: '100px' }}>Action</th>
                    </tr>
                </thead>
                <tbody>
                    {theoryLemmas.map((tl, id) => {
                        return (
                            <tr key={id}>
                                <td style={{ width: '100%', whiteSpace: 'pre-wrap' }}>{renderLet(id)}</td>
                                <td style={{ width: '100px', height: '100%' }}>
                                    <Button
                                        onClick={() => expandAll(id)}
                                        className="bp3-minimal"
                                        icon="translate"
                                        text="Expand"
                                    />
                                    <Button
                                        onClick={() => revertLet(id)}
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

export default VisualizerTheoryLemma;
