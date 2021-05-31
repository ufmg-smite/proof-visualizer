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
        <div id="menu">
            <div>
                {options.unfold ? (
                    <button onClick={() => unfold()} type="button" id="pulse-button">
                        Unfold
                    </button>
                ) : null}
                {options.foldSelected ? (
                    <button onClick={() => foldSelectedNodes()} type="button" id="delete-button">
                        Fold selected nodes
                    </button>
                ) : null}
                {options.foldAllDescendants ? (
                    <button onClick={() => foldAllDescendants()} type="button" id="pulse-button">
                        Fold all descendants
                    </button>
                ) : null}
            </div>
        </div>
    );
};

export default Menu;
