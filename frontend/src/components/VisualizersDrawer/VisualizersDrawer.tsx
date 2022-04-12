import React, { useState } from 'react';

import '../../scss/VisualizersDrawer.scss';
import { Drawer, Position, Classes, Tabs, Tab, TabId, Button } from '@blueprintjs/core';
import { selectTheme } from '../../store/features/theme/themeSlice';
import { DrawerProps } from '../../interfaces/interfaces';

import { useAppSelector, useAppDispatch } from '../../store/hooks';
import { applyView } from '../../store/features/proof/proofSlice';
import { reRender } from '../../store/features/externalCmd/externalCmd';
import VisualizerLetDrawer from '../VisualizerLetDrawer/VisualizerLetDrawer';
import VisualizerTheoryLemma from '../VisualizerTheoryLemma/VisualizerTheoryLemma';

const VisualizersDrawer: React.FC<DrawerProps> = ({ drawerIsOpen, setDrawerIsOpen }: DrawerProps) => {
    const darkTheme = useAppSelector(selectTheme);
    const dispatch = useAppDispatch();

    const [tabID, setTabID] = useState('lm');

    const handleTabChange = (newTabId: TabId, _: any, e: any): void => {
        setTabID(typeof newTabId === 'string' ? newTabId : String(newTabId));
    };

    const menus = {
        view: (
            <div className={'view-infos ' + Classes.DIALOG_BODY}>
                <div className="bts">
                    <Button
                        text="Full"
                        onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                            e.preventDefault();
                            dispatch(applyView('full'));
                            dispatch(reRender());
                        }}
                    />
                    <Button
                        text="Clustered"
                        onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                            e.preventDefault();
                            dispatch(applyView('clustered'));
                            dispatch(reRender());
                        }}
                    />
                </div>
                <div className="views-color-map">
                    <span>⬜ First Scope</span>
                    <span>🟪 SAT</span>
                    <span>🟨 CNF</span>
                    <span>🟩 Theory Lemma</span>
                    <span>🟫 Pre Processing</span>
                    <span>🟦 Input</span>
                </div>
            </div>
        ),
        letMap: <VisualizerLetDrawer />,
        theoryLemma: <VisualizerTheoryLemma />,
    };

    return (
        <Drawer
            className={darkTheme ? 'bp3-dark' : ''}
            style={{ maxHeight: '65%', width: '35%' }}
            autoFocus={true}
            canEscapeKeyClose={true}
            canOutsideClickClose={false}
            enforceFocus={true}
            hasBackdrop={false}
            isOpen={drawerIsOpen}
            position={Position.RIGHT}
            usePortal={false}
            onClose={(e) => {
                e.preventDefault();
                setDrawerIsOpen(false);
            }}
            icon="applications"
            title="Visualizers"
        >
            <div className={Classes.DRAWER_BODY}>
                <Tabs id="services-tabs" onChange={handleTabChange} selectedTabId={tabID}>
                    <Tab id="vw" title="View" panel={menus['view']} className="services-tab" />
                    <Tab id="lm" title="Let Map" panel={menus['letMap']} className="services-tab" />
                    <Tab id="tl" title="Theory Lemma" panel={menus['theoryLemma']} className="services-tab" />
                </Tabs>
            </div>
        </Drawer>
    );
};

export default VisualizersDrawer;
