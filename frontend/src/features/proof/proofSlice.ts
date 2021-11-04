import { createSlice, PayloadAction } from '@reduxjs/toolkit';
import { RootState } from '../../app/store';
import { processDot, piNodeChildren, piNodeParents, descendants } from './auxi';

export interface NodeInterface {
    id: number;
    conclusion: string;
    rule: string;
    args: string;
    views: string[];
    children: number[];
    parents: number[];
    hiddenNodes?: NodeInterface[];
    descendants: number;
}

export interface ProofState {
    proof: NodeInterface[];
    view: 'basic' | 'propositional' | 'full';
    style: 'graph' | 'directory';
    hiddenNodes: number[][];
    letMap: {
        [Key: string]: string;
    };
    visualInfo: {
        id: number;
        color: string;
        x: number;
        y: number;
    }[];
}

const initialState: ProofState = {
    proof: [],
    view: 'full',
    style: 'graph',
    hiddenNodes: [],
    letMap: {},
    visualInfo: [],
};

export const proofSlice = createSlice({
    name: 'proof',
    initialState,

    reducers: {
        process: (state, action: PayloadAction<string>) => {
            const [proof, letMap] = processDot(action.payload);
            state.proof = proof;
            state.view = 'full';
            state.hiddenNodes = [];
            state.letMap = letMap;
        },
        hideNodes: (state, action: PayloadAction<number[]>) => {
            state.hiddenNodes = state.hiddenNodes
                .concat([
                    action.payload.filter(
                        (id) =>
                            id > 0 &&
                            id < state.proof.length &&
                            state.hiddenNodes.every((hiddenNodesArray) => hiddenNodesArray.indexOf(id) === -1),
                    ),
                ])
                .filter((hiddenNodesArray) => hiddenNodesArray.length > 0);
        },
        unhideNodes: (state, action: PayloadAction<number[]>) => {
            state.hiddenNodes = state.hiddenNodes
                .map((hiddenNodesArray) => hiddenNodesArray.filter((id) => action.payload.indexOf(id) === -1))
                .filter((hiddenNodesArray) => hiddenNodesArray.length > 0);
        },
        applyView: (state, action: PayloadAction<'basic' | 'propositional' | 'full'>) => {
            switch (action.payload) {
                case 'basic':
                    state.view = 'basic';
                    state.hiddenNodes = [
                        state.proof
                            .filter((proofNode) => proofNode.views.indexOf('basic') === -1)
                            .map((proofNode) => proofNode.id),
                    ];
                    break;
                case 'propositional':
                    state.view = 'propositional';
                    state.hiddenNodes = [
                        state.proof
                            .filter(
                                (proofNode) =>
                                    proofNode.views.indexOf('basic') === -1 &&
                                    proofNode.views.indexOf('propositional') === -1,
                            )
                            .map((proofNode) => proofNode.id),
                    ];
                    break;
                case 'full':
                    state.view = 'full';
                    state.hiddenNodes = [];
                    break;
            }
        },
        changeStyle: (state, action: PayloadAction<'graph' | 'directory'>) => {
            switch (action.payload) {
                case 'graph':
                    state.style = 'graph';
                    break;
                case 'directory':
                    state.style = 'directory';
                    break;
            }
        },
        foldAllDescendants: (state, action: PayloadAction<number>) => {
            state.hiddenNodes = state.hiddenNodes
                .concat([
                    [action.payload, ...descendants(state.proof, action.payload)].filter(
                        (id) =>
                            id > 0 &&
                            id < state.proof.length &&
                            state.hiddenNodes.every((hiddenNodesArray) => hiddenNodesArray.indexOf(id) === -1),
                    ),
                ])
                .filter((hiddenNodesArray) => hiddenNodesArray.length > 0);
        },
        setVisualInfo: (state, action: PayloadAction<ProofState['visualInfo']>) => {
            state.visualInfo = action.payload;
        },
    },
});

export const { process, hideNodes, unhideNodes, foldAllDescendants, applyView, changeStyle, setVisualInfo } =
    proofSlice.actions;

export const selectProof = (state: RootState): NodeInterface[] => {
    let proof = state.proof.proof;
    const hiddenNodes = state.proof.hiddenNodes;

    hiddenNodes.forEach((hiddenNodesArray) => {
        const children = piNodeChildren(proof, hiddenNodesArray);
        const parents = piNodeParents(proof, hiddenNodesArray);
        const piNodeId = proof.length;
        proof = proof.concat({
            id: piNodeId,
            conclusion: '∴',
            rule: 'π',
            args: '',
            views: [],
            children: children,
            parents: parents,
            hiddenNodes: hiddenNodesArray.map((hiddenNode) => proof[hiddenNode]),
            descendants: 0,
        });
        children.forEach(
            (childId) =>
                (proof[childId] = {
                    ...proof[childId],
                    parents: proof[childId].parents
                        .concat([piNodeId])
                        .filter((proofNode) => hiddenNodesArray.indexOf(proofNode) === -1),
                }),
        );
        parents.forEach(
            (parentId) =>
                (proof[parentId] = {
                    ...proof[parentId],
                    children: proof[parentId].children
                        .concat([piNodeId])
                        .filter((proofNode) => hiddenNodesArray.indexOf(proofNode) === -1),
                }),
        );
    });

    proof = proof.filter((proofNode) =>
        hiddenNodes.every((hiddenNodesArray) => hiddenNodesArray.indexOf(proofNode.id) === -1),
    );

    return proof;
};

export const selectView = (state: RootState): 'basic' | 'propositional' | 'full' => {
    return state.proof.view;
};

export const selectStyle = (state: RootState): 'graph' | 'directory' => {
    return state.proof.style;
};

export const selectLetMap = (state: RootState): { [Key: string]: string } => {
    return state.proof.letMap;
};

export const selectVisualInfo = (state: RootState): ProofState['visualInfo'] => {
    return state.proof.visualInfo;
};

export default proofSlice.reducer;