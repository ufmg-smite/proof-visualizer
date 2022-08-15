import { FoldUndo, HideUndo, UnfoldUndo } from './../../../interfaces/undoClasses';
import { Draft, PayloadAction } from '@reduxjs/toolkit';
import { processDot, descendants, findNodesClusters, sliceNodesCluster, extractTheoryLemmas } from './auxi';
import { ProofState } from '../../../interfaces/interfaces';
import { colorConverter } from '../theme/auxi';
import { BaseUndo, ColorUndo, MoveUndo } from '../../../interfaces/undoClasses';

const STACK_MAX_SIZE = 5;

function addUndo(state: Draft<ProofState>, action: PayloadAction<BaseUndo>): void {
    // Ensures max size
    if (state.undoQueue.length === STACK_MAX_SIZE) state.undoQueue.shift();
    // Add to stack
    state.undoQueue.push(action.payload);
}

function process(state: Draft<ProofState>, action: PayloadAction<string>): void {
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
}

function hideNodes(state: Draft<ProofState>, action: PayloadAction<number[]>): void {
    const toHideNodes = action.payload.filter(
        (id) =>
            id > 0 &&
            id < state.proof.length &&
            state.hiddenNodes.every((hiddenNodesArray) => hiddenNodesArray.indexOf(id) === -1),
    );

    const clusters = findNodesClusters(state.proof, toHideNodes);
    // If there are clusters to hide
    if (clusters.length) {
        const objs = Object.keys(state.visualInfo);
        const oldGreatesPiNode = state.proof.length + state.hiddenNodes.length;
        state.hiddenNodes = state.hiddenNodes
            .concat(clusters)
            .filter((hiddenNodesArray) => hiddenNodesArray.length > 0);

        // Set the visual info for the new pi nodes
        for (let i = 0; i < clusters.length; i++) {
            state.visualInfo[oldGreatesPiNode + i] = {
                color: '#555',
                x: 0,
                y: 0,
                selected: false,
            };
        }

        // Save the position of all nodes
        const pos: { id: number; x: number; y: number }[] = [];
        objs.forEach((key) => {
            const id = Number(key);
            pos.push({ id: id, x: state.visualInfo[id].x, y: state.visualInfo[id].y });
        });

        // Add undo action
        addUndo(state, { payload: new HideUndo([], pos, clusters.length), type: 'string' });
    }
    // Unselect the selected nodes
    toHideNodes.forEach((id) => (state.visualInfo[id].selected = false));
}

function foldAllDescendants(state: Draft<ProofState>, action: PayloadAction<number>): void {
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
    const objs = Object.keys(state.visualInfo);
    const piNodeId = objs.length;
    // Set new visual info for the nodes
    state.visualInfo[action.payload].selected = false;
    state.visualInfo[piNodeId] = {
        color: '#555',
        x: 0,
        y: 0,
        selected: false,
    };

    // Save the position of all nodes
    const pos: { id: number; x: number; y: number }[] = [];
    objs.forEach((key) => {
        const id = Number(key);
        pos.push({ id: id, x: state.visualInfo[id].x, y: state.visualInfo[id].y });
    });

    // Add undo action
    addUndo(state, { payload: new FoldUndo([], pos), type: 'string' });
}

function unfoldNodes(state: Draft<ProofState>, action: PayloadAction<{ pi: number; hiddens: number[] }>): void {
    const { pi, hiddens } = action.payload;
    state.hiddenNodes = state.hiddenNodes
        .map((hiddenNodesArray) => hiddenNodesArray.filter((id) => hiddens.indexOf(id) === -1))
        .filter((hiddenNodesArray) => hiddenNodesArray.length > 0);

    const color = state.visualInfo[pi].color;
    const pos: { id: number; x: number; y: number }[] = [];
    const objs = Object.keys(state.visualInfo);
    const size = objs.length;

    // Save all the positions
    objs.forEach((key) => {
        const id = Number(key);
        pos.push({ id: id, x: state.visualInfo[id].x, y: state.visualInfo[id].y });
    });

    // Make sure the ids are realocated
    for (let i = pi; i < size - 1; i++) {
        state.visualInfo[i] = state.visualInfo[i + 1];
    }
    // Delete the last position
    delete state.visualInfo[size - 1];

    const colors: { id: number; color: string }[] = [];
    // Unselect the hidden nodes and set their color equal to the pi node
    hiddens.forEach((id) => {
        // Save all the hidden nodes colors
        colors.push({ id: id, color: state.visualInfo[id].color });
        state.visualInfo[id] = {
            ...state.visualInfo[id],
            color: color !== '#555' ? color : state.visualInfo[id].color,
            selected: false,
        };
    });
    colors.push({ id: pi, color: color });

    // Add undo action
    addUndo(state, { payload: new UnfoldUndo(action.payload.hiddens, pos, colors), type: 'string' });
}

function setVisualInfo(state: Draft<ProofState>, action: PayloadAction<ProofState['visualInfo']>): void {
    state.visualInfo = action.payload;
}

function selectNodes(state: Draft<ProofState>, action: PayloadAction<number[]>): void {
    const len = Object.keys(state.visualInfo).length;
    action.payload.forEach((id) => {
        if (id >= 0 && id < len) {
            state.visualInfo[id].selected = true;
        }
    });
}

function unselectNodes(state: Draft<ProofState>, action: PayloadAction<number[]>): void {
    const len = Object.keys(state.visualInfo).length;
    action.payload.forEach((id) => {
        if (id >= 0 && id < len) {
            state.visualInfo[id].selected = false;
        }
    });
}

function changeStyle(state: Draft<ProofState>, action: PayloadAction<ProofState['style']>): void {
    switch (action.payload) {
        case 'graph':
            state.style = 'graph';
            break;
        case 'directory':
            state.style = 'directory';
            break;
    }
}

function applyView(state: Draft<ProofState>, action: PayloadAction<ProofState['view']>): void {
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
}

function applyColor(state: Draft<ProofState>, action: PayloadAction<string>): void {
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
    if (nodes.length) addUndo(state, { payload: new ColorUndo(nodes, colors), type: 'string' });
}

function moveNode(state: Draft<ProofState>, action: PayloadAction<{ id: number; x: number; y: number }>): void {
    const { id, x, y } = action.payload;
    addUndo(state, {
        payload: new MoveUndo([id], state.visualInfo[id].x, state.visualInfo[id].y),
        type: 'string',
    });

    // Update the position
    state.visualInfo[id].x = x;
    state.visualInfo[id].y = y;
}

function setSmt(state: Draft<ProofState>, action: PayloadAction<string>): void {
    state.smt = action.payload;
}

function undo(state: Draft<ProofState>, action: PayloadAction<string>): void {
    const topUndo = state.undoQueue.pop();
    if (topUndo) {
        const { nodes } = topUndo;
        if (action.payload === 'MoveUndo') {
            const { x, y } = topUndo as MoveUndo;
            state.visualInfo[nodes[0]] = {
                ...state.visualInfo[nodes[0]],
                x,
                y,
            };
        } else if (action.payload === 'ColorUndo') {
            const { color } = topUndo as ColorUndo;
            nodes.forEach((node, id) => {
                state.visualInfo[node] = {
                    ...state.visualInfo[node],
                    color: color[id],
                };
            });
        } else if (action.payload === 'FoldUndo') {
            const { positions } = topUndo as FoldUndo;
            // Remove the old pi node
            state.hiddenNodes.splice(state.hiddenNodes.length - 1, 1);
            delete state.visualInfo[state.proof.length + state.hiddenNodes.length];
            // Put all the nodes in the older position
            positions.forEach(({ id, x, y }) => {
                state.visualInfo[id].x = x;
                state.visualInfo[id].y = y;
            });
        } else if (action.payload === 'HideUndo') {
            const { positions, nPiNodes } = topUndo as HideUndo;
            // Remove the old pi nodes
            for (let len = state.proof.length + state.hiddenNodes.length, i = 0; i < nPiNodes; i++) {
                delete state.visualInfo[--len];
            }
            state.hiddenNodes.splice(state.hiddenNodes.length - nPiNodes, nPiNodes);

            // Put all the nodes in the older position
            positions.forEach(({ id, x, y }) => {
                state.visualInfo[id].x = x;
                state.visualInfo[id].y = y;
            });
        } else if (action.payload === 'UnfoldUndo') {
            const { positions, colors } = topUndo as UnfoldUndo;
            let i;
            // Create the old pi node in the right position
            const oldPiNum = colors[colors.length - 1].id;
            const newSize = state.proof.length + state.hiddenNodes.length;
            state.hiddenNodes.splice(oldPiNum - state.proof.length, 0, nodes);
            // Shift the pi nodes visual info
            for (i = newSize; i > oldPiNum; i--) {
                state.visualInfo[i] = state.visualInfo[i - 1];
            }
            state.visualInfo[i] = { x: 0, y: 0, color: '', selected: false };
            // Put all the nodes in the older position
            positions.forEach(({ id, x, y }) => {
                state.visualInfo[id].x = x;
                state.visualInfo[id].y = y;
            });
            // Set the old color of all the hidden nodes
            colors.forEach(({ id, color }) => {
                state.visualInfo[id].color = color;
            });
        }
    }
}

const reducers = {
    addUndo,
    process,
    hideNodes,
    foldAllDescendants,
    unfoldNodes,
    setVisualInfo,
    selectNodes,
    unselectNodes,
    changeStyle,
    applyView,
    applyColor,
    moveNode,
    setSmt,
    undo,
};

export default reducers;
