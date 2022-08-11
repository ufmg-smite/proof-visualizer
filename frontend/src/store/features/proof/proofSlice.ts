import { createSlice, PayloadAction } from '@reduxjs/toolkit';
import { RootState } from '../../store';
import {
    processDot,
    piNodeChildren,
    piNodeParents,
    descendants,
    findNodesClusters,
    groupPiNodeDependencies,
    sliceNodesCluster,
    extractTheoryLemmas,
} from './auxi';
import { NodeInterface, ProofState } from '../../../interfaces/interfaces';
import { colorConverter } from '../theme/auxi';
import { ClusterKind } from '../../../interfaces/enum';
import { BaseUndo, ColorUndo, MoveUndo } from '../../../interfaces/undoClasses';

const STACK_MAX_SIZE = 5;

const addToStack = (state: any, action: PayloadAction<BaseUndo>) => {
    if (state.undoStack.length === STACK_MAX_SIZE) state.undoStack.shift();
    state.undoStack.push(action.payload);
};

const initialState: ProofState = {
    proof: [],
    view: 'full',
    style: 'graph',
    hiddenNodes: [],
    letMap: {},
    theoryLemmaMap: [],
    visualInfo: [],
    clustersInfos: [],
    smt: '',
    undoStack: [],
};

export const proofSlice = createSlice({
    name: 'proof',
    initialState,

    reducers: {
        process: (state, action: PayloadAction<string>) => {
            // Reset the state
            state.clustersInfos = [];

            let proofJSON;
            let dot = action.payload;
            let isJSON = false;

            // If the payload is a .json file
            if (dot.indexOf('{"dot":"') !== -1) {
                proofJSON = JSON.parse(dot);
                dot = proofJSON.dot;
                isJSON = true;
            }

            const [proof, letMap, clustersColors] = processDot(dot);
            state.proof = proof;
            state.letMap = letMap;
            state.view = 'full';

            // If there are clusters
            let clusters: number[][] = [];
            if (Object.keys(clustersColors).length) {
                state.view = 'clustered';

                // Slice the clusters
                const clustersMap: number[] = Array(state.proof.length).fill(-1);
                clusters = sliceNodesCluster(state.proof, clustersMap);

                // Maps the cluster infos
                clusters.forEach((cluster) => {
                    const type = state.proof[cluster[0]].clusterType;
                    state.clustersInfos.push({
                        hiddenNodes: cluster,
                        type: type,
                        color: colorConverter(clustersColors[type]),
                    });
                });

                // Extract the theory lemmas
                state.theoryLemmaMap = extractTheoryLemmas(state.proof, state.clustersInfos, true);
            } else {
                state.theoryLemmaMap = extractTheoryLemmas(state.proof, state.clustersInfos, false);
            }

            if (isJSON) {
                state.view = proofJSON.view;
                state.hiddenNodes = proofJSON.hiddenNodes;
                state.visualInfo = proofJSON.visualInfo;
            }
            // Is .dot
            else {
                state.hiddenNodes = clusters.filter((c) => c.length > 1);

                // Init the visual info
                const visualInfo: ProofState['visualInfo'] = {};
                state.proof.forEach((node) => {
                    visualInfo[node.id] = {
                        color: '#fff',
                        x: 0,
                        y: 0,
                        selected: false,
                    };
                });

                let size = state.proof.length;
                state.clustersInfos.forEach((cluster) => {
                    visualInfo[cluster.hiddenNodes.length !== 1 ? size++ : cluster.hiddenNodes[0]] = {
                        color: cluster.color,
                        x: 0,
                        y: 0,
                        selected: false,
                    };
                });

                state.visualInfo = visualInfo;
            }
        },
        hideNodes: (state, action: PayloadAction<number[]>) => {
            const toHideNodes = action.payload.filter(
                (id) =>
                    id > 0 &&
                    id < state.proof.length &&
                    state.hiddenNodes.every((hiddenNodesArray) => hiddenNodesArray.indexOf(id) === -1),
            );

            const clusters = findNodesClusters(state.proof, toHideNodes);
            state.hiddenNodes = state.hiddenNodes
                .concat(clusters)
                .filter((hiddenNodesArray) => hiddenNodesArray.length > 0);

            // Set the visual info for the new pi nodes
            const piNodeId = Object.keys(state.visualInfo).length;
            for (let i = 0; i < clusters.length; i++) {
                state.visualInfo = {
                    ...state.visualInfo,
                    [piNodeId + i]: {
                        color: '#555',
                        x: 0,
                        y: 0,
                        selected: false,
                    },
                };
            }

            // Unselect the selected nodes
            toHideNodes.forEach(
                (id) =>
                    (state.visualInfo[id] = {
                        ...state.visualInfo[id],
                        selected: false,
                    }),
            );
        },
        foldAllDescendants: (state, action: PayloadAction<number>) => {
            state.hiddenNodes = state.hiddenNodes
                .concat([
                    [action.payload, ...descendants(state.proof, action.payload)].filter(
                        (id, index, self) =>
                            id > 0 &&
                            id < state.proof.length &&
                            state.hiddenNodes.every((hiddenNodesArray) => hiddenNodesArray.indexOf(id) === -1) &&
                            self.indexOf(id) === index,
                    ),
                ])
                .filter((hiddenNodesArray) => hiddenNodesArray.length > 0);

            // Set the visual info for the new pi node and the root node
            const piNodeId = Object.keys(state.visualInfo).length;
            state.visualInfo = {
                ...state.visualInfo,
                [action.payload]: {
                    ...state.visualInfo[action.payload],
                    selected: false,
                },
                [piNodeId]: {
                    color: '#555',
                    x: 0,
                    y: 0,
                    selected: false,
                },
            };
        },
        unhideNodes: (state, action: PayloadAction<{ pi: number; hiddens: number[] }>) => {
            const { pi, hiddens } = action.payload;
            state.hiddenNodes = state.hiddenNodes
                .map((hiddenNodesArray) => hiddenNodesArray.filter((id) => hiddens.indexOf(id) === -1))
                .filter((hiddenNodesArray) => hiddenNodesArray.length > 0);

            const color = state.visualInfo[pi].color;
            // Make sure the ids are realocated
            const size = Object.keys(state.visualInfo).length;
            for (let i = pi; i < size - 1; i++) {
                state.visualInfo[i] = state.visualInfo[i + 1];
            }
            // Delete the last position
            delete state.visualInfo[size - 1];

            // Unselect the hidden nodes and set their color equal to the pi node
            hiddens.forEach(
                (id) =>
                    (state.visualInfo[id] = {
                        ...state.visualInfo[id],
                        color: color !== '#555' ? color : state.visualInfo[id].color,
                        selected: false,
                    }),
            );
        },
        setVisualInfo: (state, action: PayloadAction<ProofState['visualInfo']>) => {
            state.visualInfo = action.payload;
        },
        selectNodes: (state, action: PayloadAction<number[]>) => {
            const len = Object.keys(state.visualInfo).length;
            action.payload.forEach((id) => {
                if (id >= 0 && id < len) {
                    state.visualInfo[id].selected = true;
                }
            });
        },
        unselectNodes: (state, action: PayloadAction<number[]>) => {
            const len = Object.keys(state.visualInfo).length;
            action.payload.forEach((id) => {
                if (id >= 0 && id < len) {
                    state.visualInfo[id].selected = false;
                }
            });
        },
        changeStyle: (state, action: PayloadAction<ProofState['style']>) => {
            switch (action.payload) {
                case 'graph':
                    state.style = 'graph';
                    break;
                case 'directory':
                    state.style = 'directory';
                    break;
            }
        },
        applyView: (state, action: PayloadAction<ProofState['view']>) => {
            const visualInfoSize = Object.keys(state.visualInfo).length;
            const proofSize = state.proof.length;
            // Delete all the pi nodes
            for (let i = 0; i < visualInfoSize - proofSize; i++) {
                delete state.visualInfo[proofSize + i];
            }

            switch (action.payload) {
                // View without hidden Nodes
                case 'full':
                    if (state.hiddenNodes.length || state.view === 'colored-full') {
                        state.proof.forEach((node) => {
                            state.visualInfo[node.id] = {
                                color: '#fff',
                                x: 0,
                                y: 0,
                                selected: false,
                            };
                        });

                        state.hiddenNodes = [];
                    }
                    state.view = 'full';
                    break;
                // Cluster all the nodes in your respective group
                case 'clustered':
                    // If there are clusters infos
                    if (state.clustersInfos.length) {
                        state.view = 'clustered';

                        state.hiddenNodes = [];
                        let size = Object.keys(state.visualInfo).length;

                        state.clustersInfos.forEach((cluster) => {
                            if (cluster.hiddenNodes.length !== 1) {
                                state.visualInfo[size++] = {
                                    color: cluster.color,
                                    x: 0,
                                    y: 0,
                                    selected: false,
                                };

                                state.hiddenNodes.push(cluster.hiddenNodes);
                            }
                            // Cluster with 1 node
                            else {
                                state.visualInfo[cluster.hiddenNodes[0]] = {
                                    color: cluster.color,
                                    x: 0,
                                    y: 0,
                                    selected: false,
                                };
                            }
                        });
                    }
                    break;
                // Apply full view but apply the clustrer color
                case 'colored-full':
                    state.view = 'colored-full';
                    state.hiddenNodes = [];

                    // If there are clusters infos
                    if (state.clustersInfos.length) {
                        state.clustersInfos.forEach((cluster) => {
                            cluster.hiddenNodes.forEach((node) => {
                                state.visualInfo[node] = {
                                    color: cluster.color,
                                    x: 0,
                                    y: 0,
                                    selected: false,
                                };
                            });
                        });
                    }
                    break;
            }
        },
        applyColor: (state, action: PayloadAction<string>) => {
            const nodes: number[] = [],
                colors: string[] = [];
            Object.keys(state.visualInfo).forEach((id) => {
                const nodeID = Number(id);
                if (state.visualInfo[nodeID].selected) {
                    nodes.push(nodeID);
                    colors.push(state.visualInfo[nodeID].color);

                    state.visualInfo[nodeID].color = action.payload;
                    state.visualInfo[nodeID].selected = false;
                }
            });
            //
            if (nodes.length) addToStack(state, { payload: new ColorUndo(nodes, colors), type: 'string' });
        },
        setSmt: (state, action: PayloadAction<string>) => {
            state.smt = action.payload;
        },
        addUndo: addToStack,
        undo: (state, action: PayloadAction<string>) => {
            const topUndo = state.undoStack[state.undoStack.length - 1];
            const { nodes } = topUndo;
            switch (action.payload) {
                case 'MoveUndo':
                    const { x, y } = topUndo as MoveUndo;
                    state.visualInfo[nodes[0]] = {
                        ...state.visualInfo[nodes[0]],
                        x,
                        y,
                    };

                    break;
                case 'ColorUndo':
                    const { color } = topUndo as ColorUndo;
                    nodes.forEach((node, id) => {
                        state.visualInfo[node] = {
                            ...state.visualInfo[node],
                            color: color[id],
                        };
                    });

                    break;
                case 'FoldUndo':
                    break;
                case 'HideUndo':
                    break;
                case 'UnfoldUndo':
                    break;
                case 'SelectUndo':
                    break;
            }
            state.undoStack.pop();
        },
    },
});

export const {
    process,
    hideNodes,
    foldAllDescendants,
    unhideNodes,
    setVisualInfo,
    selectNodes,
    unselectNodes,
    changeStyle,
    applyView,
    applyColor,
    setSmt,
    addUndo,
    undo,
} = proofSlice.actions;

export const selectProof = (state: RootState): NodeInterface[] => {
    let proof = state.proof.proof;
    const hiddenNodes = state.proof.hiddenNodes;

    hiddenNodes.forEach((hiddenNodesArray) => {
        const dependencies: { [parentId: number]: number[] } = {};
        const children = piNodeChildren(proof, hiddenNodesArray);
        const parents = piNodeParents(proof, hiddenNodesArray, dependencies);
        const piNodeDependencies = groupPiNodeDependencies(proof, hiddenNodesArray);

        const piNodeId = proof.length;
        proof = proof.concat({
            id: piNodeId,
            conclusion: '∴',
            rule: 'π',
            args: '',
            children: children,
            parents: parents,
            hiddenNodes: hiddenNodesArray.map((hiddenNode) => proof[hiddenNode]),
            descendants: 1,
            dependencies: piNodeDependencies,
            clusterType: ClusterKind.NONE,
        });

        const piNode = proof[piNodeId];

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

        // Set the dependencies array of each parent that has deps and remove
        //  the children that are dependencies
        Object.keys(dependencies).forEach((parent) => {
            const parentId = Number(parent);
            proof[parentId] = {
                ...proof[parentId],
                children: proof[parentId].children.filter((c) => dependencies[parentId].indexOf(c) === -1),
                dependencies: [...proof[parentId].dependencies, { piId: piNodeId, depsId: dependencies[parentId] }],
            };
        });

        // Get the high hierarchy nodes in this pi node
        const highHierarchyNodes = hiddenNodesArray?.filter((node) =>
            proof[node].parents.every((parentId) => piNode.parents.indexOf(parentId) !== -1),
        );

        // Get the conclusion array
        const conclusion = highHierarchyNodes.map((node) => ' ' + proof[node].conclusion);
        piNode.conclusion = conclusion.length > 1 ? `[${conclusion} ]` : `${conclusion}`;

        // Get the rule array
        const rule = highHierarchyNodes.map((node) => ' ' + proof[node].rule);
        piNode.rule = rule.length > 1 ? `[${rule} ]` : `${rule} `;

        // Set the descendants number
        piNode.descendants = piNode.children.reduce(
            (ac: number, childID) => ((ac += proof[childID].descendants), ac),
            1,
        );
    });

    proof = proof.filter((proofNode) =>
        hiddenNodes.every((hiddenNodesArray) => hiddenNodesArray.indexOf(proofNode.id) === -1),
    );

    return proof;
};

export const selectOriginalProof = (state: RootState): NodeInterface[] => {
    return state.proof.proof;
};

export const selectView = (state: RootState): ProofState['view'] => {
    return state.proof.view;
};

export const selectStyle = (state: RootState): 'graph' | 'directory' => {
    return state.proof.style;
};

export const selectLetMap = (state: RootState): { [Key: string]: string } => {
    return state.proof.letMap;
};

export const selectTheoryLemmas = (state: RootState): ProofState['theoryLemmaMap'] => {
    return state.proof.theoryLemmaMap;
};

export const selectVisualInfo = (state: RootState): ProofState['visualInfo'] => {
    if (state.proof.proof.length) return state.proof.visualInfo;
    // If there is no proof node
    return { 0: { color: '#555', x: 0, y: 0, selected: false } };
};

export const selectHiddenNodes = (state: RootState): number[][] => {
    return state.proof.hiddenNodes;
};

export const selectNodeClusters = (state: RootState): ProofState['clustersInfos'] => {
    return state.proof.clustersInfos;
};

export const selectSmt = (state: RootState): ProofState['smt'] => {
    return state.proof.smt;
};

export const selectTopUndo = (state: RootState): BaseUndo => state.proof.undoStack[state.proof.undoStack.length - 1];

export default proofSlice.reducer;
