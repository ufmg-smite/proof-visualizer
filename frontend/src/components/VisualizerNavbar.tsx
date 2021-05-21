import React, { Dispatch, SetStateAction } from 'react';
import { proofState } from '../redux/dotReducer';
import { useSelector } from 'react-redux';

import { Alignment, Button, Icon, Navbar, Switch, Menu, MenuItem } from '@blueprintjs/core';
import { Popover2 } from '@blueprintjs/popover2';

import '../scss/VisualizerNavbar.scss';

interface VisualizerNavbarProps {
    darkTheme: boolean;
    setDarkTheme: Dispatch<SetStateAction<boolean>>;
    setDialogIsOpen: Dispatch<SetStateAction<boolean>>;
    setDialogContent: Dispatch<SetStateAction<string>>;
}

const VisualizerNavbar: React.FC<VisualizerNavbarProps> = ({
    darkTheme,
    setDarkTheme,
    setDialogIsOpen,
    setDialogContent,
}: VisualizerNavbarProps) => {
    const openDialog = (content: string): void => {
        setDialogIsOpen(true);
        setDialogContent(content);
    };
    const proof = useSelector<proofState, proofState>((state: proofState) => state);

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
                    link.href = (document.getElementsByClassName('konvajs-content')[0]
                        .children[0] as HTMLCanvasElement).toDataURL('image/png');
                    link.click();
                }}
            />
        </Menu>
    );

    return (
        <Navbar>
            <Navbar.Group align={Alignment.LEFT}>
                <Navbar.Heading>Proof Visualizer</Navbar.Heading>
                <Navbar.Divider />
                <Button
                    onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                        e.preventDefault();
                        openDialog('proof-list');
                    }}
                    className="bp3-minimal"
                    icon="list"
                    text="Proof list"
                />
                <Button
                    onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                        e.preventDefault();
                        openDialog('new-proof');
                    }}
                    className="bp3-minimal"
                    icon="add"
                    text="New Proof"
                />
            </Navbar.Group>

            <Navbar.Group align={Alignment.RIGHT}>
                <Popover2 content={proof.label ? exampleMenu : undefined} placement="bottom-end">
                    <Button
                        className="bp3-minimal"
                        icon="download"
                        text="Download"
                        disabled={proof.label ? false : true}
                    />
                </Popover2>
                <Button
                    onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                        e.preventDefault();
                    }}
                    className="bp3-minimal"
                    icon="reset"
                    text="Basic view"
                    disabled={proof.label ? false : true}
                />
                <Navbar.Divider />
                <span id="switch-button-dark-theme">
                    <Switch checked={darkTheme} onChange={() => setDarkTheme(!darkTheme)} />
                    <Icon icon={darkTheme ? 'moon' : 'flash'}></Icon>
                </span>
            </Navbar.Group>
        </Navbar>
    );
};

export default VisualizerNavbar;
