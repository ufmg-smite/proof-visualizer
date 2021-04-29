import React, { Dispatch, SetStateAction } from 'react';
import '../scss/VisualizerNavbar.scss';
import { Navbar, Button, Alignment, Switch, Icon } from '@blueprintjs/core';

interface VisualizerNavbarProps {
    darkTheme: boolean;
    setDarkTheme: Dispatch<SetStateAction<boolean>>;
}

const VisualizerNavbar: React.FC<VisualizerNavbarProps> = ({ darkTheme, setDarkTheme }: VisualizerNavbarProps) => {
    return (
        <Navbar>
            <Navbar.Group align={Alignment.LEFT}>
                <Navbar.Heading>Proof Visualizer</Navbar.Heading>
                <Navbar.Divider />
                <Button className="bp3-minimal" icon="list" text="Proof list" />
                <Button className="bp3-minimal" icon="add" text="New Proof" />
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
