import React, { Component } from 'react';
import { Stage, Layer } from 'react-konva';
import Konva from 'konva';
import dagre from 'dagre';
import Node from './VisualizerNode';
import Line from './VisualizerLine';
import Menu from './VisualizerMenu';

import {
    NodeProps,
    LineProps,
    TreeNode,
    CanvasPropsAndRedux,
    NodeInterface,
    ProofState,
    ReduxState,
} from '../../../interfaces/interfaces';

import '../../../scss/VisualizerCanvas.scss';

import { CanvasProps, CanvasState } from '../../../interfaces/interfaces';

import { connect } from 'react-redux';
import { selectProof, selectVisualInfo } from '../../../store/features/proof/proofSlice';
import {
    hideNodes,
    unhideNodes,
    foldAllDescendants,
    applyView,
    setVisualInfo,
} from '../../../store/features/proof/proofSlice';

function handleWheel(e: Konva.KonvaEventObject<WheelEvent>): { stageScale: number; stageX: number; stageY: number } {
    e.evt.preventDefault();

    const scaleBy = 1.08;
    const stage = e.target.getStage();
    if (stage) {
        const oldScale = stage.scaleX();
        const pointerPosition = stage.getPointerPosition();
        let x, y;

        if (pointerPosition) {
            [x, y] = [pointerPosition.x, pointerPosition.y];
        } else {
            [x, y] = [0, 0];
        }

        const mousePointTo = {
            x: x / oldScale - stage.x() / oldScale,
            y: y / oldScale - stage.y() / oldScale,
        };

        const newScale = e.evt.deltaY > 0 ? oldScale * scaleBy : oldScale / scaleBy;

        return {
            stageScale: newScale,
            stageX: -(mousePointTo.x - x / newScale) * newScale,
            stageY: -(mousePointTo.y - y / newScale) * newScale,
        };
    }
    return {
        stageScale: 1,
        stageX: 0,
        stageY: 0,
    };
}

class Canvas extends Component<CanvasPropsAndRedux, CanvasState> {
    constructor(props: CanvasPropsAndRedux) {
        super(props);
        this.componentDidUpdate = this.componentDidUpdate.bind(this);
        this.setNodeOnFocus = this.setNodeOnFocus.bind(this);

        this.state = {
            canvasSize: {
                width: 520,
                height: 300,
            },
            stage: {
                stageScale: 1,
                stageX: 0,
                stageY: 0,
            },
            showingNodes: {},
            showingEdges: {},
            nodeOnFocus: NaN,
            nodesSelected: [],
            proof: [],
            visualInfo: {},
        };
    }
    // TODO: achar uma maneira melhor de fazer esse firstRender
    private static renderData = { count: 0 };

    // Allow to reRender the tree
    static reRender = () => (Canvas.renderData.count = 0);

    static copyNodePosition = (
        visualInfo: ProofState['visualInfo'],
        showingNodes: CanvasState['showingNodes'],
    ): ProofState['visualInfo'] => {
        // Get the current position of the nodes and create a proofState with them included
        const newVisualInfo: ProofState['visualInfo'] = {};
        Object.keys(visualInfo).forEach((id) => {
            const key = Number(id);

            if (showingNodes[key]) {
                newVisualInfo[key] = {
                    ...visualInfo[key],
                    x: showingNodes[key].props.x,
                    y: showingNodes[key].props.y,
                };
            } else {
                newVisualInfo[key] = {
                    ...visualInfo[key],
                };
            }
        });
        return newVisualInfo;
    };

    static newNodeProps = (node: NodeInterface, visualInfos: ProofState['visualInfo']): NodeProps => {
        const visualInfo = visualInfos[node.id];
        return {
            id: node.id,
            conclusion: node.conclusion,
            rule: node.rule,
            args: node.args,
            x: visualInfo.x,
            y: visualInfo.y,
            nHided: node.hiddenNodes ? node.hiddenNodes.length : 0,
            nDescendants: node.descendants - 1,
            hiddenNodes: node.hiddenNodes ? node.hiddenNodes.map((node) => node.id) : [],
            selected: visualInfo.selected,
            color: visualInfo.color,
            setNodeOnFocus: () => undefined,
            toggleNodeSelection: () => undefined,
            updateNodePosition: () => undefined,
            openDrawer: () => undefined,
            onDragEnd: () => undefined,
        };
    };

    static getDerivedStateFromProps(props: CanvasPropsAndRedux, current_state: CanvasState) {
        const proofChanged = JSON.stringify(current_state.proof) !== JSON.stringify(props.proof);
        const visualInfoChanged = JSON.stringify(current_state.visualInfo) !== JSON.stringify(props.visualInfo);

        if (proofChanged || visualInfoChanged) {
            const showingNodes = props.proof.reduce(
                (ac: any, node) => ((ac[node.id] = new Node(Canvas.newNodeProps(node, props.visualInfo))), ac),
                {},
            );
            if (showingNodes[0] && Canvas.renderData.count < 2) {
                Canvas.renderData.count++;

                const g = new dagre.graphlib.Graph();
                g.setGraph({ rankdir: 'BT', ranker: 'tight-tree' });
                g.setDefaultEdgeLabel(function () {
                    return {};
                });
                props.proof.forEach((node) => {
                    g.setNode(node.id.toString(), { width: 300, height: 130 });
                    node.children.forEach((child) => {
                        g.setEdge(child.toString(), node.id.toString());
                    });
                });
                dagre.layout(g);

                const xOffset = g.node('0').x - (showingNodes[0].props.x ? showingNodes[0].props.x : 0);
                const yOffset = g.node('0').y - (showingNodes[0].props.y ? showingNodes[0].props.y : 0);
                g.nodes().forEach((v) => {
                    try {
                        const { x, y } = g.node(v);
                        const key = parseInt(v);
                        showingNodes[key] = new Node({
                            ...showingNodes[key].props,
                            x: x - xOffset,
                            y: y - yOffset,
                        });
                    } catch (e) {
                        console.log(e);
                    }
                });

                props.setVisualInfo(Canvas.copyNodePosition(props.visualInfo, showingNodes));
            }

            return {
                showingNodes: showingNodes,
                showingEdges: {},
                proof: props.proof,
                visualInfo: props.visualInfo,
            };
        }
        return null;
    }

    componentDidMount(): void {
        const { showingNodes } = this.state;
        const { view, proof } = this.props;

        this.setState({
            proof: proof,
            showingNodes: proof.reduce(
                (ac: any, node) => ((ac[node.id] = new Node(Canvas.newNodeProps(node, this.props.visualInfo))), ac),
                {},
            ),
        });

        if (showingNodes[0]) {
            if (view !== 'imported_data') {
                const [width, height] = [window.innerWidth, window.innerHeight - 50];

                this.setState({
                    canvasSize: {
                        width,
                        height,
                    },
                    stage: {
                        stageScale: 1,
                        stageX: width / 2 - (showingNodes[0].props.x + 300 / 2),
                        stageY: height / 10 - (showingNodes[0].props.y + 30 / 2),
                    },
                });
            }
        }
    }

    componentDidUpdate(prevProps: CanvasPropsAndRedux) {
        const { showingNodes, showingEdges } = this.state;
        // If the proof changed
        if (prevProps.proof !== this.props.proof) {
            // Update edges
            this.props.proof.forEach((node) => {
                if (showingNodes[node.parents[0]]) {
                    showingEdges[`${node.id}->${node.parents[0]}`] = Line(
                        this.LineProps(
                            `${node.id}->${parent[0]}`,
                            showingNodes[node.id].props,
                            showingNodes[node.parents[0]].props,
                        ),
                    );
                }
            });
            Object.keys(showingNodes).forEach((nodeId: string) => {
                // Make sure a function is updated once
                if (!showingNodes[parseInt(nodeId)].props.setNodeOnFocus.length) {
                    const { openDrawer } = this.props;

                    // Set the node functions
                    showingNodes[parseInt(nodeId)] = new Node({
                        ...showingNodes[parseInt(nodeId)].props,
                        setNodeOnFocus: this.setNodeOnFocus,
                        toggleNodeSelection: this.toggleNodeSelection,
                        updateNodePosition: this.updateNodePosition,
                        openDrawer: openDrawer,
                        onDragEnd: this.saveNodePosition,
                    });
                }
            });

            this.setState({ showingEdges: showingEdges });
        }
    }

    hiddenNodesTree = (list: Array<TreeNode>): Array<TreeNode> => {
        const map: { [n: number]: number } = {},
            roots: Array<TreeNode> = [];
        let node, i;

        for (i = 0; i < list.length; i += 1) {
            map[list[i].id] = i;
            list[i].childNodes = [];
        }

        for (i = 0; i < list.length; i += 1) {
            node = list[i];
            if (node.parentId !== NaN && list[map[node.parentId]]) {
                list[map[node.parentId]].childNodes.push(node);
            } else {
                roots.push(node);
            }
        }
        return roots;
    };

    /* NODE MENU ACTIONS */
    foldAllDescendants = (): void => {
        const { nodeOnFocus } = this.state;
        const { foldAllDescendants } = this.props;

        Canvas.reRender();
        foldAllDescendants(nodeOnFocus);
        this.setState({ nodesSelected: [] });
    };

    foldSelectedNodes = (): void => {
        const { nodesSelected } = this.state;
        const { hideNodes } = this.props;

        Canvas.reRender();
        hideNodes(nodesSelected);
        this.setState({ nodesSelected: [] });
    };

    unfold = (): void => {
        const { nodeOnFocus, proof } = this.state;
        const { unhideNodes } = this.props;

        // Get the pi node (to be unfold)
        const obj = proof.find((node) => node.id === nodeOnFocus);
        // Get the hidden nodes and their ids
        const hiddenNodes = obj ? (obj.hiddenNodes ? obj.hiddenNodes : []) : [];
        const hiddenIds = hiddenNodes ? hiddenNodes.map((node) => node.id) : [];

        Canvas.reRender();
        unhideNodes({ pi: nodeOnFocus, hiddens: hiddenIds });

        this.setState({ nodesSelected: [] });
    };

    changeNodeColor = (color: string): void => {
        const { showingNodes, nodesSelected, nodeOnFocus } = this.state;
        let { visualInfo } = this.props;

        // Save the current position
        nodesSelected.forEach((nodeId) => {
            visualInfo = {
                ...visualInfo,
                [nodeId]: {
                    ...visualInfo[nodeId],
                    color: color,
                    selected: false,
                },
            };
        });
        if (!nodesSelected.length && showingNodes[nodeOnFocus]) {
            visualInfo = {
                ...visualInfo,
                [nodeOnFocus]: { ...visualInfo[nodeOnFocus], color: color, selected: false },
            };
        }

        this.props.setVisualInfo(visualInfo);
        this.setState({ nodesSelected: [] });
    };

    toggleNodeSelection = (id: number): void => {
        let { nodesSelected } = this.state;
        const { visualInfo } = this.props;

        if (this.props.visualInfo[id].selected) {
            nodesSelected = nodesSelected.filter((nodeId) => nodeId !== id);
        } else {
            nodesSelected.push(id);
        }

        // Save the current position
        this.props.setVisualInfo({
            ...visualInfo,
            [id]: {
                ...visualInfo[id],
                selected: !visualInfo[id].selected,
            },
        });

        this.setState({ nodesSelected });
    };

    /* PROOF I/O */
    // CV sobre isso
    downloadProof = (dot: string, proofName: string): void => {
        // Cv dps
        const link = document.createElement('a');
        link.download = proofName + '.json';
        link.href = `data:attachment/text,${encodeURIComponent(JSON.stringify(this.exportProof(dot)))}`;
        link.click();
    };

    exportProof = (dot = ''): { dot: string } => {
        //Apg
        // TODO
        return {
            dot: dot,
        };
    };

    /* UTILS */
    setNodeOnFocus = (id: number): void => {
        this.setState({ nodeOnFocus: id });
    };

    LineProps = (key: string, from: NodeProps, to: NodeProps): LineProps => ({
        key,
        points: [from.x + 150, from.y, to.x + 150, to.y + 105],
    });

    saveNodePosition = (): void => {
        const { visualInfo, setVisualInfo } = this.props;
        const { showingNodes } = this.state;

        // Get the current position of the nodes and create a proofState with them included
        setVisualInfo(Canvas.copyNodePosition(visualInfo, showingNodes));
    };

    updateNodePosition = (key: number, x: number, y: number): void => {
        const { showingNodes, showingEdges } = this.state;

        showingNodes[key] = new Node({ ...showingNodes[key].props, x, y });

        Object.keys(showingEdges)
            .filter((edgeKey) => edgeKey.indexOf(key.toString()) !== -1)
            .forEach((edge) => {
                const [from, to] = edge.split('->').map((x) => parseInt(x));
                showingEdges[edge] = Line(this.LineProps(edge, showingNodes[from].props, showingNodes[to].props));
            });
        this.setState({ showingNodes, showingEdges });
    };

    // newTree = (piId: number): TreeNode[] => {
    //     const { proofNodes } = this.state;

    //     return this.hiddenNodesTree(
    //         proofNodes[piId].hidedNodes
    //             .sort((a, b) => a - b)
    //             .map((nodeId) => {
    //                 return {
    //                     id: nodeId,
    //                     icon: 'graph',
    //                     parentId: proofNodes[nodeId].parent,
    //                     label: proofNodes[nodeId].rule + ' => ' + proofNodes[nodeId].conclusion,
    //                     descendants: proofNodes[nodeId].descendants,
    //                     childNodes: [],
    //                     rule: proofNodes[nodeId].rule,
    //                     conclusion: proofNodes[nodeId].conclusion,
    //                     args: proofNodes[nodeId].args,
    //                 };
    //             }),
    //     );
    // };

    render(): JSX.Element {
        const { canvasSize, stage, showingNodes, showingEdges, nodesSelected, nodeOnFocus, proof } = this.state;
        const color = showingNodes[nodeOnFocus] ? showingNodes[nodeOnFocus].props.color : '';

        return (
            <div>
                <Menu
                    unfold={this.unfold}
                    foldSelectedNodes={this.foldSelectedNodes}
                    foldAllDescendants={this.foldAllDescendants}
                    changeNodeColor={this.changeNodeColor}
                    options={{
                        unfold: showingNodes[nodeOnFocus] ? showingNodes[nodeOnFocus].props.rule === 'π' : false,
                        foldSelected: nodesSelected.length && nodesSelected.includes(nodeOnFocus) ? true : false,
                        foldAllDescendants: Boolean(proof.find((o) => o.id === nodeOnFocus)?.children.length),
                    }}
                    currentColor={color}
                ></Menu>
                <Stage
                    draggable
                    width={canvasSize.width}
                    height={canvasSize.height}
                    onWheel={(e) => this.setState({ stage: handleWheel(e) })}
                    scaleX={stage.stageScale}
                    scaleY={stage.stageScale}
                    x={stage.stageX}
                    y={stage.stageY}
                    onContextMenu={(e) => e.evt.preventDefault()}
                >
                    <Layer>
                        {Object.keys(showingEdges).length > 0 &&
                            Object.keys(showingEdges).map(function (key) {
                                return showingEdges[key];
                            })}
                        {Object.keys(showingNodes).length > 0 &&
                            Object.keys(showingNodes).map(
                                (value: string): JSX.Element => showingNodes[parseInt(value)].render(),
                            )}
                    </Layer>
                </Stage>
            </div>
        );
    }
}

function mapStateToProps(state: ReduxState, ownProps: CanvasProps) {
    return {
        proof: selectProof(state),
        visualInfo: selectVisualInfo(state),
        myView: state.proof.view,
        ...ownProps,
        view: ownProps.view ? ownProps.view : undefined,
    };
}

const mapDispatchToProps = { hideNodes, unhideNodes, foldAllDescendants, applyView, setVisualInfo };

export default connect(mapStateToProps, mapDispatchToProps)(Canvas);
