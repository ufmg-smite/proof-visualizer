import React, { useState, useRef, useEffect } from 'react';
import { useAppSelector } from '../../store/hooks';
import { selectTheme } from '../../store/features/theme/themeSlice';
import { LetRenderProps } from '../../interfaces/interfaces';
import { renderLetKind } from '../../interfaces/enum';
import Let from './let';
import { Pre } from '@blueprintjs/core';

const font = '13px monospace';

const LetRender: React.FC<LetRenderProps> = ({
    id,
    toRender,
    letMap,
    shouldExpand,
    shouldRevert,
    dispatchExpansion,
}: LetRenderProps) => {
    const darkTheme = useAppSelector(selectTheme);
    const widthRef = useRef(0);
    const [resizeMode, setResizeMode] = useState(0);
    const [letMapS, setLetMapS] = useState(
        (() => {
            const newMap = { ...letMap };
            if (toRender[0] !== '(' && toRender[toRender.length] !== ')') {
                toRender = `(${toRender})`;
            }
            newMap['this'] = toRender;
            return newMap;
        })(),
    );

    const initializeLet = (key = 'this', lets: { [key: string]: Let } = {}) => {
        const currentLet = letMapS[key];
        const indices: { [key: number]: string } = {};

        // Finds all occurences of let in the currentLet
        [...currentLet.matchAll(/let\d+/g)].forEach((match) => {
            if (match.index) indices[match.index] = match[0];
        });

        // Call recursive for all the external lets
        Object.keys(indices).forEach((indice) => {
            initializeLet(indices[Number(indice)], lets);
        });

        // If this let was not created yet
        if (Object.keys(lets).indexOf(key) === -1) {
            lets[key] = new Let(key, currentLet, lets, indices);
        }

        return lets;
    };
    const letsRef = useRef<{ [key: string]: Let }>(initializeLet());

    // ComponentDidMount
    useEffect(() => {
        // Handler to call on window resize and set the value column width
        function handleResize() {
            const width = widthRef.current;

            const newWidth = document.getElementsByClassName(`let-render-${id}`)[0].clientWidth - 30;
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

    useEffect(() => {
        // Expand
        if (shouldExpand) {
            expandAll('this');
            dispatchExpansion({ type: renderLetKind.EXPAND, payload: false });
        }
        // Revert
        else if (shouldRevert) {
            revertLet('this');
            dispatchExpansion({ type: renderLetKind.REVERT, payload: false });
        }
    }, [shouldExpand, shouldRevert]);

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

    const renderLet = (): JSX.Element => {
        const lets = letsRef.current;
        const width = widthRef.current;
        const key = 'this';

        // Waits for the width to be updated and the DOM element to be updated
        if (width) {
            let currentLet = letMapS[key];
            let indices: { [key: number]: string } = {};

            // Finds all occurences of let in the currentLet
            [...currentLet.matchAll(/let\d+/g)].forEach((match) => {
                if (match.index !== undefined) indices[match.index] = match[0];
            });

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
                return (
                    <span className="let-instance" style={{ overflowWrap: 'break-word' }}>
                        {arr}
                    </span>
                );
            } else {
                return (
                    <span className="let-instance" style={{ overflowWrap: 'break-word' }}>
                        {currentLet}
                    </span>
                );
            }
        }
        return <></>;
    };

    return (
        <Pre
            className={`let-render-${id}`}
            style={{ maxHeight: '300px', overflow: 'auto', margin: '0', whiteSpace: 'pre-wrap' }}
        >
            {renderLet()}
        </Pre>
    );
};

export default LetRender;
