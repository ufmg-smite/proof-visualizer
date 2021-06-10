import React from 'react';

const Menu = ({
    unfold,
    foldSelectedNodes,
    foldAllDescendants,
    options,
}: {
    unfold: () => void;
    foldSelectedNodes: () => void;
    foldAllDescendants: () => void;
    options: { unfold: boolean; foldSelected: boolean; foldAllDescendants: boolean };
}): JSX.Element => {
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
            </ul>
        </div>
    );
};

export default Menu;
