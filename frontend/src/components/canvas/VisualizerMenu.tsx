import React from 'react';

const Menu = ({
    unfold,
    options,
}: {
    unfold: (s: string) => void;
    options: { unfold: boolean; foldSelected: boolean };
}): JSX.Element => {
    return (
        <div id="menu">
            <div>
                {options.unfold ? (
                    <>
                        <button onClick={() => unfold('all')} type="button" id="pulse-button">
                            Unfold All Nodes
                        </button>
                        <button onClick={() => unfold('propositional')} type="button" id="delete-button">
                            Unfold Propositional View
                        </button>
                    </>
                ) : null}
                {options.foldSelected ? (
                    <button onClick={() => null} type="button" id="delete-button">
                        Fold selected nodes
                    </button>
                ) : null}
            </div>
        </div>
    );
};

export default Menu;
