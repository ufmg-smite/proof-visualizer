import { FoldUndo, HideUndo, UnfoldUndo } from './../../../interfaces/undoClasses';
import { Draft, PayloadAction } from '@reduxjs/toolkit';
import { processDot, descendants, findNodesClusters, sliceNodesCluster, extractTheoryLemmas } from './auxi';
import { ExternalCmdState, ProofState } from '../../../interfaces/interfaces';
import { colorConverter } from '../theme/auxi';
import { BaseUndo, ColorUndo, MoveUndo } from '../../../interfaces/undoClasses';
import Deque from 'double-ended-queue';

const STACK_MAX_SIZE = 20;
const undoQueue = new Deque<BaseUndo>();

function addUndo(undo: BaseUndo): void {
    // Ensures max size
    if (undoQueue.length === STACK_MAX_SIZE) undoQueue.shift();
    // Add to stack
    undoQueue.push(undo);
}

function clearUndo(): void {
    undoQueue.clear();
}

function clearHiddenNodes(state: Draft<ProofState>, action: PayloadAction<null>): void {
    state.hiddenNodes.forEach((hiddenArray) => hiddenArray.forEach((node) => (state.proof[node].isHidden = undefined)));
    state.hiddenNodes = [];
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
        // Init the visual info
        state.visualInfo = {};
        state.proof.forEach((node) => {
            state.visualInfo[node.id] = {
                color: '#fff',
                x: 0,
                y: 0,
                selected: false,
            };
        });

        let size = state.proof.length;
        clearHiddenNodes(state, { payload: null, type: 'string' });
        state.clustersInfos.forEach(({ hiddenNodes, color }) => {
            let index;
            if (hiddenNodes.length > 1) {
                state.hiddenNodes.push(hiddenNodes);
                index = size++;
            } else index = hiddenNodes[0];
            state.visualInfo[index] = {
                color: color,
                x: 0,
                y: 0,
                selected: false,
            };
        });
    }
    // Set all the hidden nodes as hidden
    state.hiddenNodes.forEach((hiddenNodesArray, i) => {
        const piID = state.proof.length + i;
        hiddenNodesArray.forEach((node) => (state.proof[node].isHidden = piID));
    });
}

function hideNodes(state: Draft<ProofState>, action: PayloadAction<number[]>): void {
    const size = state.proof.length + state.hiddenNodes.length;

    const toHideNodes = action.payload.filter((id) => id > 0 && id < state.proof.length && !state.proof[id].isHidden);

    const clusters = findNodesClusters(state.proof, toHideNodes);
    // If there are clusters to hide
    if (clusters.length) {
        clusters.forEach((cluster) => state.hiddenNodes.push(cluster));

        // Save the position of all nodes
        const pos: { id: number; x: number; y: number }[] = [];
        for (let id = 0; id < size; id++) {
            pos.push({ id: id, x: state.visualInfo[id].x, y: state.visualInfo[id].y });
        }

        // Set the visual info for the new pi nodes
        clusters.forEach((cluster, i) => {
            const piID = size + i;
            state.visualInfo[piID] = {
                color: '#555',
                x: 0,
                y: 0,
                selected: false,
            };

            cluster.forEach((nodeID) => (state.proof[nodeID].isHidden = piID));
        });

        // Add undo action
        addUndo(new HideUndo([], pos, clusters.length));
    }
    // Unselect the selected nodes
    toHideNodes.forEach((id) => (state.visualInfo[id].selected = false));
}

function foldAllDescendants(state: Draft<ProofState>, action: PayloadAction<number>): void {
    const size = state.proof.length + state.hiddenNodes.length;
    const hashMap: { [nodeID: number]: boolean } = {};
    const newHidden = [action.payload, ...descendants(state.proof, action.payload)].filter((id) => {
        let isTheFirst = true;
        if (hashMap[id]) isTheFirst = false;
        else hashMap[id] = true;

        return id > 0 && id < state.proof.length && isTheFirst && !state.proof[id].isHidden;
    });

    // If the array is valid to become a pi node
    if (newHidden.length > 1) {
        state.hiddenNodes.push(newHidden);
        newHidden.forEach((nodeID) => {
            state.proof[nodeID].isHidden = size;
            state.visualInfo[nodeID].selected = false;
        });

        // Set the visual info for the new pi node and the root node
        state.visualInfo[action.payload].selected = false;
        state.visualInfo[size] = {
            color: '#555',
            x: 0,
            y: 0,
            selected: false,
        };

        // Save the position of all nodes
        const pos: { id: number; x: number; y: number }[] = [];
        for (let id = 0; id < size; id++) {
            pos.push({ id: id, x: state.visualInfo[id].x, y: state.visualInfo[id].y });
        }

        // Add undo action
        addUndo(new FoldUndo([], pos));
    }
}

function unfoldNodes(state: Draft<ProofState>, action: PayloadAction<number>): void {
    const pi = action.payload;
    const hiddenID = pi - state.proof.length;
    const hiddens = state.hiddenNodes[hiddenID];
    const size = state.proof.length + state.hiddenNodes.length;
    const color = state.visualInfo[pi].color;

    // Save all the positions
    const pos: { id: number; x: number; y: number }[] = [];
    for (let id = 0; id < size; id++) {
        pos.push({ id: id, x: state.visualInfo[id].x, y: state.visualInfo[id].y });
    }

    // Unselect the hidden nodes and set their color equal to the pi node
    const colors: { id: number; color: string }[] = [];
    hiddens.forEach((id) => {
        // Save all the hidden nodes colors
        colors.push({ id: id, color: state.visualInfo[id].color });
        // Signalize nodes are unhided
        state.proof[id].isHidden = undefined;
        state.visualInfo[id] = {
            ...state.visualInfo[id],
            color: color !== '#555' ? color : state.visualInfo[id].color,
            selected: false,
        };
    });
    colors.push({ id: pi, color: color });

    // Remove the pi node array
    state.hiddenNodes.splice(hiddenID, 1);

    // Make sure the ids are realocated
    for (let i = pi; i < size - 1; i++) {
        state.visualInfo[i] = state.visualInfo[i + 1];
    }
    // Delete the last position
    delete state.visualInfo[size - 1];

    // Add undo action
    addUndo(new UnfoldUndo([...hiddens], pos, colors));
}

function setVisualInfo(state: Draft<ProofState>, action: PayloadAction<ProofState['visualInfo']>): void {
    state.visualInfo = action.payload;
}

function selectByArea(state: Draft<ProofState>, action: PayloadAction<ExternalCmdState['selectData']>): void {
    const { upperL, lowerR } = action.payload;
    const size = state.proof.length + state.hiddenNodes.length;
    for (let i = 0; i < size; i++) {
        const thisNode = state.visualInfo[i];
        if (upperL.x <= thisNode.x && thisNode.x <= lowerR.x && upperL.y <= thisNode.y && thisNode.y <= lowerR.y) {
            thisNode.selected = true;
        }
    }
}
function selectNodes(state: Draft<ProofState>, action: PayloadAction<number[]>): void {
    const len = state.proof.length + state.hiddenNodes.length;
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
    // Delete all the pi nodes visual info
    for (let i = state.proof.length; i < state.proof.length + state.hiddenNodes.length; i++) {
        delete state.visualInfo[i];
    }
    clearUndo();

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

                clearHiddenNodes(state, { payload: null, type: 'string' });
            }
            state.view = 'full';
            break;
        // Cluster all the nodes in your respective group
        case 'clustered':
            // If there are clusters infos
            if (state.clustersInfos.length) {
                state.view = 'clustered';

                clearHiddenNodes(state, { payload: null, type: 'string' });
                let size = state.proof.length;

                state.clustersInfos.forEach(({ hiddenNodes, color }) => {
                    let index;
                    if (hiddenNodes.length > 1) {
                        state.hiddenNodes.push(hiddenNodes);
                        hiddenNodes.forEach((node) => (state.proof[node].isHidden = size));
                        index = size++;
                    }
                    // Cluster with 1 node
                    else index = hiddenNodes[0];

                    state.visualInfo[index] = {
                        color: color,
                        x: 0,
                        y: 0,
                        selected: false,
                    };
                });
            }
            break;
        // Apply full view but apply the clustrer color
        case 'colored-full':
            state.view = 'colored-full';
            clearHiddenNodes(state, { payload: null, type: 'string' });

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
    const colorMap: { [color: string]: number[] } = {};
    let nodesLen = 0;
    for (let nodeID = 0; nodeID < state.proof.length + state.hiddenNodes.length; nodeID++) {
        const thisInfo = state.visualInfo[nodeID];
        if (thisInfo.selected) {
            if (colorMap[thisInfo.color]) colorMap[thisInfo.color].push(nodeID);
            else {
                colorMap[thisInfo.color] = [nodeID];
            }
            nodesLen++;

            thisInfo.color = action.payload;
            thisInfo.selected = false;
        }
    }
    //
    if (nodesLen) addUndo(new ColorUndo([], colorMap));
}

function moveNode(state: Draft<ProofState>, action: PayloadAction<{ id: number; x: number; y: number }>): void {
    const { id, x, y } = action.payload;
    addUndo(new MoveUndo([id], state.visualInfo[id].x, state.visualInfo[id].y));

    // Update the position
    state.visualInfo[id].x = x;
    state.visualInfo[id].y = y;
}

function setSmt(state: Draft<ProofState>, action: PayloadAction<string>): void {
    state.smt = action.payload;
}

function undo(state: Draft<ProofState>, action: PayloadAction<void>): void {
    const topUndo = undoQueue.pop();
    if (topUndo) {
        const { nodes, name } = topUndo;
        if (name === 'MoveUndo') {
            const { x, y } = topUndo as MoveUndo;
            state.visualInfo[nodes[0]] = {
                ...state.visualInfo[nodes[0]],
                x,
                y,
            };
        } else if (name === 'ColorUndo') {
            const { colorMap } = topUndo as ColorUndo;
            Object.keys(colorMap).forEach((color) => {
                colorMap[color].forEach((node) => (state.visualInfo[node].color = color));
            });
        } else if (name === 'FoldUndo') {
            const { positions } = topUndo as FoldUndo;
            // Make sure the node is not hidden
            state.hiddenNodes[state.hiddenNodes.length - 1].forEach((node) => (state.proof[node].isHidden = undefined));
            // Remove the old pi node
            state.hiddenNodes.splice(state.hiddenNodes.length - 1, 1);
            delete state.visualInfo[state.proof.length + state.hiddenNodes.length];
            // Put all the nodes in the older position
            positions.forEach(({ id, x, y }) => {
                state.visualInfo[id].x = x;
                state.visualInfo[id].y = y;
            });
        } else if (name === 'HideUndo') {
            const { positions, nPiNodes } = topUndo as HideUndo;
            // Remove the old pi nodes
            for (let len = state.proof.length + state.hiddenNodes.length, i = 0; i < nPiNodes; i++) {
                delete state.visualInfo[--len];
                // Make sure the node is not hidden
                state.hiddenNodes[nPiNodes - i - 1].forEach((node) => (state.proof[node].isHidden = undefined));
            }
            state.hiddenNodes.splice(state.hiddenNodes.length - nPiNodes, nPiNodes);

            // Put all the nodes in the older position
            positions.forEach(({ id, x, y }) => {
                state.visualInfo[id].x = x;
                state.visualInfo[id].y = y;
            });
        } else if (name === 'UnfoldUndo') {
            const { positions, colors } = topUndo as UnfoldUndo;
            let i;
            // Create the old pi node in the right position
            const oldPiNum = colors[colors.length - 1].id;
            const newSize = state.proof.length + state.hiddenNodes.length;
            state.hiddenNodes.splice(oldPiNum - state.proof.length, 0, nodes);
            // Make sure all the hidden nodes will be signalized as hidden
            nodes.forEach((nodeID) => (state.proof[nodeID].isHidden = oldPiNum));
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
    process,
    hideNodes,
    foldAllDescendants,
    unfoldNodes,
    setVisualInfo,
    selectByArea,
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
