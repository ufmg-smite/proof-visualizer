import React, { useState } from 'react';
import { ControlGroup, Button, InputGroup } from '@blueprintjs/core';

const Menu = ({
    unfold,
    foldSelectedNodes,
    foldAllDescendants,
    changeNodeColor,
    options,
}: {
    unfold: () => void;
    foldSelectedNodes: () => void;
    foldAllDescendants: () => void;
    changeNodeColor: (color: string) => void;
    options: { unfold: boolean; foldSelected: boolean; foldAllDescendants: boolean };
}): JSX.Element => {
    const [color, setColor] = useState('');
    return (
        <div className="bp3-popover2-content">
            <ul id="menu" className="bp3-menu">
                {options.unfold ? (
                    <li className="">
                        <a className="bp3-menu-item" onClick={() => unfold()}>
                            <div className="bp3-text-overflow-ellipsis bp3-fill bp3-icon-eye-open">
                                <span> Unfold</span>
                            </div>
                        </a>
                    </li>
                ) : null}
                {options.foldSelected ? (
                    <li className="">
                        <a className="bp3-menu-item" onClick={() => foldSelectedNodes()}>
                            <div className="bp3-text-overflow-ellipsis bp3-fill bp3-icon-eye-off">
                                <span> Fold selected nodes</span>
                            </div>
                        </a>
                    </li>
                ) : null}
                {options.foldAllDescendants ? (
                    <li className="">
                        <a className="bp3-menu-item" onClick={() => foldAllDescendants()}>
                            <div className="bp3-text-overflow-ellipsis bp3-fill bp3-icon-eye-off">
                                <span> Fold all descendants</span>
                            </div>
                        </a>
                    </li>
                ) : null}
                <li className="">
                    <a className="bp3-menu-item">
                        <div className="bp3-text-overflow-ellipsis bp3-fill">
                            <span>
                                <span onClick={() => changeNodeColor('#f72b34')}> 🟥</span>
                                <span onClick={() => changeNodeColor('#ff8334')}> 🟧</span>
                                <span onClick={() => changeNodeColor('#ffc149')}> 🟨</span>
                                <span onClick={() => changeNodeColor('#60aa51')}> 🟩</span>
                                <span onClick={() => changeNodeColor('#0097e4')}> 🟦</span>
                                <span onClick={() => changeNodeColor('#a73da5')}> 🟪</span>
                                <span onClick={() => changeNodeColor('#a95a49')}> 🟫</span>
                                <span onClick={() => changeNodeColor('#464646')}> ⬛</span>
                                <span onClick={() => changeNodeColor('#f0f0f0')}> ⬜</span>
                            </span>
                        </div>
                    </a>
                </li>
                <li className="">
                    <a className="bp3-menu-item">
                        <div className="bp3-text-overflow-ellipsis bp3-fill">
                            <ControlGroup
                                onClick={(e) => {
                                    e.stopPropagation();
                                }}
                                fill={true}
                                vertical={false}
                            >
                                <InputGroup
                                    placeholder="#fff"
                                    value={color}
                                    onChange={(e) => setColor(e.target.value)}
                                />
                                <Button
                                    icon="style"
                                    onClick={() => {
                                        changeNodeColor(color);
                                        setColor('');
                                    }}
                                    disabled={color.match(/^(#[a-f0-9]{6})|(#[a-f0-9]{3})$/i) === null}
                                ></Button>
                            </ControlGroup>
                        </div>
                    </a>
                </li>
            </ul>
        </div>
    );
};

export default Menu;
