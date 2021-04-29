import React, { Dispatch, SetStateAction } from 'react';
import '../scss/VisualizerNavbar.scss';
import { Navbar, Button, Alignment, Switch, Icon } from '@blueprintjs/core';

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

    return (
        <Navbar>
            <Navbar.Group align={Alignment.LEFT}>
                <Navbar.Heading>Proof Visualizer</Navbar.Heading>
                <Navbar.Divider />
                <Button
                    onClick={() => openDialog('proof-list')}
                    className="bp3-minimal"
                    icon="list"
                    text="Proof list"
                />
                <Button onClick={() => openDialog('new-proof')} className="bp3-minimal" icon="add" text="New Proof" />
            </Navbar.Group>
            <Navbar.Group align={Alignment.RIGHT}>
                <span id="switch-button-dark-theme">
                    <Switch checked={darkTheme} onChange={() => setDarkTheme(!darkTheme)} />
                    <Icon icon="contrast"></Icon>
                </span>
            </Navbar.Group>
        </Navbar>
    );
};

export default VisualizerNavbar;
