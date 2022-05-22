import React, { useState } from 'react';

import '../../scss/VisualizersDrawer.scss';
import { Drawer, Position, Classes, Tabs, Tab, TabId, Button } from '@blueprintjs/core';
import { selectTheme } from '../../store/features/theme/themeSlice';
import { DrawerProps, SmtDrawerProps } from '../../interfaces/interfaces';

import { useAppSelector, useAppDispatch } from '../../store/hooks';
import { applyView, selectNodeClusters, selectNodes } from '../../store/features/proof/proofSlice';
import { reRender } from '../../store/features/externalCmd/externalCmd';
import VisualizerLetDrawer from '../VisualizerLetDrawer/VisualizerLetDrawer';
import VisualizerTheoryLemma from '../VisualizerTheoryLemma/VisualizerTheoryLemma';
import { ClusterKind } from '../../interfaces/enum';

const VisualizerSmtDrawer: React.FC<SmtDrawerProps> = ({ isOpen, setDrawerIsOpen }: SmtDrawerProps) => {
    const darkTheme = useAppSelector(selectTheme);

    return (
        <Drawer
            className={darkTheme ? 'bp3-dark' : ''}
            style={{ maxHeight: '65%', width: '35%' }}
            autoFocus={true}
            canEscapeKeyClose={true}
            canOutsideClickClose={true}
            enforceFocus={false}
            hasBackdrop={false}
            isOpen={isOpen}
            position={Position.LEFT}
            usePortal={false}
            onClose={(e) => {
                e.preventDefault();
                setDrawerIsOpen();
            }}
            icon="applications"
            title="Visualizers"
        >
            <div className={Classes.DRAWER_BODY}>
                <Button
                    style={{ justifySelf: 'end' }}
                    className="bp3-minimal"
                    icon="code"
                    onClick={() => {
                        //
                    }}
                />
            </div>
        </Drawer>
    );
};

export default VisualizerSmtDrawer;
