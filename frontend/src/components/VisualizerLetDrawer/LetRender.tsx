import React, { useState, useRef, useEffect } from 'react';
import { useAppSelector } from '../../store/hooks';
import { selectTheme } from '../../store/features/theme/themeSlice';
import { LetRenderProps } from '../../interfaces/interfaces';
import Let from './let';
import { Button } from '@blueprintjs/core';

const font = '13px monospace';
const triggerSize = 300;

const LetRender: React.FC<LetRenderProps> = ({ id, toRender, letMap }: LetRenderProps) => {
    const darkTheme = useAppSelector(selectTheme);
    const widthRef = useRef({ letRender: 0, full: 0 });
    const [resizeMode, setResizeMode] = useState(0);
    const [letMapS, setLetMapS] = useState(
        (() => {
            const newMap = { ...letMap };
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
            const width = widthRef.current.letRender;

            const fullWidth = document.getElementsByClassName(`let-corpus-${id}`)[0].clientWidth;
            const newWidth = document.getElementsByClassName(`let-render-${id}`)[0].clientWidth - 10;
            width === newWidth ? setResizeMode(1) : width > newWidth ? setResizeMode(0) : setResizeMode(2);

            widthRef.current = { letRender: newWidth, full: fullWidth };
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

    const renderLet = (): JSX.Element => {
        const lets = letsRef.current;
        const width = widthRef.current.letRender;
        const key = 'this';

        // Waits for the width to be updated and the DOM element to be updated
        if (width) {
            let currentLet = letMapS[key];
            let indices: { [key: number]: string } = {};

            // Finds all occurences of let in the currentLet
            [...currentLet.matchAll(/let\d+/g)].forEach((match) => {
                if (match.index) indices[match.index] = match[0];
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

    const btColumnSize = widthRef.current.full > triggerSize ? 100 : 40;

    return (
        <div
            className={`let-corpus-${id}`}
            style={{
                display: 'grid',
                gridTemplateColumns: `auto ${btColumnSize + 7}px`,
            }}
        >
            <div className={`let-render-${id}`} style={{ height: '100%', borderRight: 'solid 1px' }}>
                {renderLet()}
            </div>
            <div
                style={{
                    width: `${btColumnSize}px`,
                    display: 'flex',
                    flexFlow: 'column',
                    justifySelf: 'right',
                }}
            >
                <Button
                    onClick={() => expandAll('this')}
                    className="bp3-minimal"
                    icon="translate"
                    text={widthRef.current.full > triggerSize ? 'Expand' : null}
                />
                <Button
                    onClick={() => revertLet('this')}
                    className="bp3-minimal"
                    icon="undo"
                    text={widthRef.current.full > triggerSize ? 'Revert' : null}
                />
            </div>
        </div>
    );
};

export default LetRender;
