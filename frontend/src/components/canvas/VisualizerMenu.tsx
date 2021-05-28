import React from 'react';

const Menu = ({
    unfold,
    foldSelectedNodes,
    options,
}: {
    unfold: () => void;
    foldSelectedNodes: () => void;
    options: { unfold: boolean; foldSelected: boolean };
}): JSX.Element => {
    return (
        <div id="menu">
            <div>
                {options.unfold ? (
                    <>
                        <button onClick={() => unfold()} type="button" id="pulse-button">
                            Unfold
                        </button>
                    </>
                ) : null}
                {options.foldSelected ? (
                    <button onClick={() => foldSelectedNodes()} type="button" id="delete-button">
                        Fold selected nodes
                    </button>
                ) : null}
            </div>
        </div>
    );
};

export default Menu;
