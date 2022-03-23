import React, { useEffect, useState } from 'react';
import { ControlGroup, Button, InputGroup } from '@blueprintjs/core';
import { colorConverter } from '../../../store/features/theme/auxi';

const Menu = ({
    unfold,
    foldSelectedNodes,
    foldAllDescendants,
    changeNodeColor,
    currentColor,
    options,
}: {
    unfold: () => void;
    foldSelectedNodes: () => void;
    foldAllDescendants: () => void;
    changeNodeColor: (color: string) => void;
    currentColor: string;
    options: { unfold: boolean; foldSelected: boolean; foldAllDescendants: boolean };
}): JSX.Element => {
    const [color, setColor] = useState(currentColor);

    useEffect(() => {
        setColor(currentColor);
    }, [currentColor]);

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
                                <span onClick={() => changeNodeColor(colorConverter('red'))}> 🟥</span>
                                <span onClick={() => changeNodeColor(colorConverter('orange'))}> 🟧</span>
                                <span onClick={() => changeNodeColor(colorConverter('yellow'))}> 🟨</span>
                                <span onClick={() => changeNodeColor(colorConverter('green'))}> 🟩</span>
                                <span onClick={() => changeNodeColor(colorConverter('blue'))}> 🟦</span>
                                <span onClick={() => changeNodeColor(colorConverter('purple'))}> 🟪</span>
                                <span onClick={() => changeNodeColor(colorConverter('brown'))}> 🟫</span>
                                <span onClick={() => changeNodeColor(colorConverter('black'))}> ⬛</span>
                                <span onClick={() => changeNodeColor(colorConverter('white'))}> ⬜</span>
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
                                    placeholder={currentColor}
                                    value={color}
                                    onChange={(e) => setColor(e.target.value)}
                                />
                                <Button
                                    icon="style"
                                    onClick={() => {
                                        changeNodeColor(color);
                                        setColor('');
                                    }}
                                    disabled={color.match(/^#([0-9a-f]{3}){1,2}$/i) === null}
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
