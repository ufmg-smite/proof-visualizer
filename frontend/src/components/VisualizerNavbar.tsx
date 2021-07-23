import React, { useEffect, useState } from 'react';
import { useSelector, useDispatch } from 'react-redux';

import { Alignment, Button, Icon, Navbar, Switch, Menu, MenuItem } from '@blueprintjs/core';
import { Popover2 } from '@blueprintjs/popover2';

import '../scss/VisualizerNavbar.scss';
import { VisualizerNavbarProps, stateInterface, proof } from './interfaces';

function useWindowSize() {
    // Initialize state with undefined width/height so server and client renders match
    // Learn more here: https://joshwcomeau.com/react/the-perils-of-rehydration/
    const [windowSize, setWindowSize] = useState({
        width: 0,
        height: 0,
    });
    useEffect(() => {
        // Handler to call on window resize
        function handleResize() {
            // Set window width/height to state
            setWindowSize({
                width: window.innerWidth,
                height: window.innerHeight,
            });
        }
        // Add event listener
        window.addEventListener('resize', handleResize);
        // Call handler right away so state gets updated with initial window size
        handleResize();
        // Remove event listener on cleanup
        return () => window.removeEventListener('resize', handleResize);
    }, []); // Empty array ensures that effect is only run on mount
    return windowSize;
}

const VisualizerNavbar: React.FC<VisualizerNavbarProps> = ({
    setDialogIsOpen,
    setDialogContent,
    setDrawerIsOpen,
}: VisualizerNavbarProps) => {
    const openDialog = (content: string): void => {
        setDialogIsOpen(true);
        setDialogContent(content);
    };
    const proof = useSelector<stateInterface, proof>((state: stateInterface) => state.proofReducer.proof);
    const darkTheme = useSelector<stateInterface, boolean>((state: stateInterface) => state.darkThemeReducer.darkTheme);
    const windowSize = useWindowSize();

    const dispatch = useDispatch();

    const setDarkTheme = () => {
        dispatch({ type: 'TOGGLE_DARK_THEME', payload: {} });
    };

    const setStyle = (style: string) => {
        dispatch({ type: 'SET_STYLE', payload: style });
    };

    const changeView = (view: string) => {
        switch (view) {
            case 'basic':
                dispatch({ type: 'BASIC_VIEW', payload: proof.dot });
                break;
            case 'propositional':
                dispatch({ type: 'PROPOSITIONAL_VIEW', payload: proof.dot });
                break;
            case 'full':
                dispatch({ type: 'FULL_VIEW', payload: proof.dot });
                break;
            default:
        }
        dispatch({ type: 'SET_DOT', payload: '' });
        setTimeout(function () {
            dispatch({ type: 'SET_DOT', payload: proof.dot });
        }, 10);
    };

    const styleMenu = (
        <Menu>
            <MenuItem
                icon="diagram-tree"
                text="Tree"
                onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                    e.preventDefault();
                    setStyle('tree');
                }}
            />
            <MenuItem
                icon="folder-open"
                text="Directory"
                onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                    e.preventDefault();
                    setStyle('directory');
                }}
            />
        </Menu>
    );

    const viewsMenu = (
        <Menu>
            <MenuItem
                text="Basic"
                onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                    e.preventDefault();
                    changeView('basic');
                }}
            />
            <MenuItem
                text="Propositional"
                onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                    e.preventDefault();
                    changeView('propositional');
                }}
            />
            <MenuItem
                text="Full"
                onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                    e.preventDefault();
                    changeView('full');
                }}
            />
        </Menu>
    );
    const exampleMenu = (
        <Menu>
            <MenuItem
                icon="manually-entered-data"
                text="Problem"
                href={`data:attachment/text,${encodeURIComponent(proof.problem)}`}
                download={proof.label ? `${proof.label.replaceAll(' ', '_')}.smt2` : null}
            />
            <MenuItem
                icon="graph"
                text="Dot"
                href={`data:attachment/text,${encodeURIComponent(proof.dot ? proof.dot : '')}`}
                download={proof.label ? `${proof.label.replaceAll(' ', '_')}.dot` : ''}
            />
            <MenuItem
                icon="square"
                text="PNG"
                onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                    e.preventDefault();
                    const link = document.createElement('a');
                    link.download = proof.label ? `${proof.label.replaceAll(' ', '_')}.png` : '';
                    link.href = (
                        document.getElementsByClassName('konvajs-content')[0].children[0] as HTMLCanvasElement
                    ).toDataURL('image/png');
                    link.click();
                }}
            />
        </Menu>
    );
    return (
        <Navbar>
            <Navbar.Group align={Alignment.LEFT}>
                <Navbar.Heading>
                    <b>{windowSize.width >= 900 ? 'Proof Visualizer' : 'PV'}</b>
                </Navbar.Heading>
                <Navbar.Divider />
                <Button
                    onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                        e.preventDefault();
                        openDialog('upload-proof');
                    }}
                    className="bp3-minimal"
                    icon="upload"
                    text={windowSize.width >= 900 ? 'Upload Proof' : ''}
                />
            </Navbar.Group>

            <Navbar.Group align={Alignment.RIGHT}>
                {proof.label ? (
                    <>
                        <Navbar.Heading>{proof.label}</Navbar.Heading>
                        <Navbar.Divider />
                        <Popover2
                            content={proof.label ? styleMenu : undefined}
                            placement="bottom-end"
                            disabled={proof.label ? false : true}
                        >
                            <Button
                                icon="presentation"
                                className="bp3-minimal"
                                text={windowSize.width >= 900 ? 'Style' : ''}
                                disabled={proof.label ? false : true}
                            />
                        </Popover2>
                        <Popover2
                            content={proof.label ? viewsMenu : undefined}
                            placement="bottom-end"
                            disabled={proof.label ? false : true}
                        >
                            <Button
                                className="bp3-minimal"
                                icon="diagram-tree"
                                text={windowSize.width >= 900 ? 'View' : ''}
                                disabled={proof.label ? false : true}
                            />
                        </Popover2>
                        <Button
                            className="bp3-minimal"
                            icon="translate"
                            text={windowSize.width >= 900 ? 'Let Map' : ''}
                            disabled={proof.label ? false : true}
                            onClick={() => setDrawerIsOpen(true)}
                        />
                        <Popover2
                            content={proof.label ? exampleMenu : undefined}
                            placement="bottom-end"
                            disabled={proof.label ? false : true}
                        >
                            <Button
                                className="bp3-minimal"
                                icon="download"
                                text={windowSize.width >= 900 ? 'Download' : ''}
                                disabled={proof.label ? false : true}
                            />
                        </Popover2>
                        <Navbar.Divider />
                    </>
                ) : null}

                <span id="switch-button-dark-theme">
                    <Switch checked={darkTheme} onChange={() => setDarkTheme()} />
                    <Icon icon={darkTheme ? 'moon' : 'flash'}></Icon>
                </span>
            </Navbar.Group>
        </Navbar>
    );
};

export default VisualizerNavbar;
