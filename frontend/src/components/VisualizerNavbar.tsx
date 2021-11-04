import React, { useEffect, useState, Dispatch, SetStateAction } from 'react';

import { useAppSelector, useAppDispatch } from '../app/hooks';
import { selectFile, selectFileName } from '../features/file/fileSlice';
import { applyView, changeStyle } from '../features/proof/proofSlice';

import '../scss/VisualizerNavbar.scss';

import { Alignment, Button, Icon, InputGroup, Navbar, Switch, Menu, MenuItem } from '@blueprintjs/core';
import { Popover2 } from '@blueprintjs/popover2';
import { selectTheme, toggle } from '../features/theme/themeSlice';

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

interface VisualizerNavbarProps {
    setDialogIsOpen: Dispatch<SetStateAction<boolean>>;
    setDialogContent: Dispatch<SetStateAction<string>>;
    setDrawerIsOpen: Dispatch<SetStateAction<boolean>>;
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
    const file = useAppSelector(selectFile);
    const fileName = useAppSelector(selectFileName);
    const darkTheme = useAppSelector(selectTheme);
    const windowSize = useWindowSize();
    const [command, setCommand] = useState('');

    const dispatch = useAppDispatch();

    const styleMenu = (
        <Menu>
            <MenuItem
                icon="diagram-tree"
                text="Graph"
                onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                    e.preventDefault();
                    dispatch(changeStyle('graph'));
                }}
            />
            <MenuItem
                icon="folder-open"
                text="Directory"
                onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                    e.preventDefault();
                    dispatch(changeStyle('directory'));
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
                    dispatch(applyView('basic'));
                }}
            />
            <MenuItem
                text="Propositional"
                onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                    e.preventDefault();
                    dispatch(applyView('propositional'));
                }}
            />
            <MenuItem
                text="Full"
                onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                    e.preventDefault();
                    dispatch(applyView('full'));
                }}
            />
        </Menu>
    );

    const exampleMenu = (
        <Menu>
            <MenuItem
                icon="layout"
                text="JSON"
                onClick={() => {
                    // TODO
                }}
            />
            <MenuItem
                icon="graph"
                text="DOT"
                href={`data:attachment/text,${encodeURIComponent(file ? file : '')}`}
                download={fileName ? `${fileName.replaceAll(' ', '_')}.dot` : ''}
            />
            <MenuItem
                icon="square"
                text="PNG"
                onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                    e.preventDefault();
                    const link = document.createElement('a');
                    link.download = fileName ? `${fileName.replaceAll(' ', '_')}.png` : '';
                    link.href = (
                        document.getElementsByClassName('konvajs-content')[0].children[0] as HTMLCanvasElement
                    ).toDataURL('image/png');
                    link.click();
                }}
            />
        </Menu>
    );

    const runCommands = (command: string): void => {
        switch (command.split(' ')[0]) {
            case '/view':
                switch (command.split(' ')[1]) {
                    case 'basic':
                        dispatch(applyView('basic'));
                        break;
                    case 'propositional':
                        dispatch(applyView('propositional'));
                        break;
                    case 'full':
                        dispatch(applyView('full'));
                        break;
                }
                break;
        }
    };

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
                {fileName ? (
                    <>
                        <Navbar.Heading>{fileName}</Navbar.Heading>
                        <Navbar.Divider />
                        <InputGroup
                            id="command"
                            placeholder="/command"
                            value={command}
                            onChange={(e) => setCommand(e.target.value)}
                        />
                        <Button
                            style={{ marginLeft: '5px' }}
                            icon="play"
                            onClick={() => {
                                runCommands(command);
                                setCommand('');
                            }}
                        />
                        <Navbar.Divider />
                        <Popover2
                            content={fileName ? styleMenu : undefined}
                            placement="bottom-end"
                            disabled={fileName ? false : true}
                        >
                            <Button
                                icon="presentation"
                                className="bp3-minimal"
                                text={windowSize.width >= 900 ? 'Style' : ''}
                                disabled={fileName ? false : true}
                            />
                        </Popover2>
                        <Popover2
                            content={fileName ? viewsMenu : undefined}
                            placement="bottom-end"
                            disabled={fileName ? false : true}
                        >
                            <Button
                                className="bp3-minimal"
                                icon="diagram-tree"
                                text={windowSize.width >= 900 ? 'View' : ''}
                                disabled={fileName ? false : true}
                            />
                        </Popover2>
                        <Button
                            className="bp3-minimal"
                            icon="translate"
                            text={windowSize.width >= 900 ? 'Let Map' : ''}
                            disabled={fileName ? false : true}
                            onClick={() => setDrawerIsOpen(true)}
                        />
                        <Popover2
                            content={fileName ? exampleMenu : undefined}
                            placement="bottom-end"
                            disabled={fileName ? false : true}
                        >
                            <Button
                                className="bp3-minimal"
                                icon="download"
                                text={windowSize.width >= 900 ? 'Download' : ''}
                                disabled={fileName ? false : true}
                            />
                        </Popover2>
                        <Navbar.Divider />
                    </>
                ) : null}

                <span id="switch-button-dark-theme">
                    <Switch checked={useAppSelector(selectTheme)} onChange={() => dispatch(toggle())} />
                    <Icon icon={darkTheme ? 'moon' : 'flash'}></Icon>
                </span>
            </Navbar.Group>
        </Navbar>
    );
};

export default VisualizerNavbar;
