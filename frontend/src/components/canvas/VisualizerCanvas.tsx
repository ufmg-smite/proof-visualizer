import React, { Component } from 'react';
import { Stage, Layer } from 'react-konva';
import Konva from 'konva';
import dagre from 'dagre';
import Node from './VisualizerNode';
import Line from './VisualizerLine';
import Menu from './VisualizerMenu';

import { NodeInterface, NodeProps, LineProps } from '../interfaces';

import '../../scss/VisualizerCanvas.scss';

import { CanvasProps, CanvasState } from '../interfaces';

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

export default class Canvas extends Component<CanvasProps, CanvasState> {
    constructor(props: CanvasProps) {
        super(props);

        const { proofNodes } = this.props;
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
            proofNodes,
            showingNodes: {},
            showingEdges: {},
            nodeOnFocus: NaN,
            nodesSelected: [],
        };
    }

    componentDidMount(): void {
        const { showingNodes, proofNodes } = this.state;

        this.basicView();
        this.updatePosition();
        showingNodes[0] = new Node(this.nodeProps(proofNodes[0]));
        this.addNodes(0);

        const [width, height] = [window.innerWidth, window.innerHeight - 50];

        this.setState({
            showingNodes,
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

    basicView = (): void => {
        const { proofNodes } = this.state;
        proofNodes.forEach((node) => {
            if (node.views.indexOf('basic') === -1) this.hideNode(node.id);
        });
    };

    foldSelectedNodes = (): void => {
        const { proofNodes, nodesSelected, showingNodes } = this.state;
        this.removeNodes(0);
        nodesSelected.sort().forEach((nodeId) => {
            if (proofNodes[nodeId].rule === 'π' || nodeId === 0) {
                alert("You can't fold the root node or a hiding node.");
            } else {
                this.hideNode(nodeId);
            }
        });
        this.updatePosition();
        this.updateNodeState(0, proofNodes[0].x, proofNodes[0].y);
        showingNodes[0] = new Node({ ...showingNodes[0].props, selected: false });
        this.addNodes(0);
        this.setState({ nodesSelected: [] });
    };

    unfold = (view: string): void => {
        const { proofNodes, nodeOnFocus } = this.state;
        const parentId = proofNodes[nodeOnFocus].parent;
        this.removeNodes(parentId);
        const nodesToUnhide = [...proofNodes[nodeOnFocus].hidedNodes];
        nodesToUnhide.forEach((nodeId) => this.unhideNode(nodeId));
        switch (view) {
            case 'propositional':
                nodesToUnhide.forEach((nodeId) => {
                    if (proofNodes[nodeId].views.indexOf('propositional') === -1) {
                        this.hideNode(nodeId);
                    }
                });
                break;
            default:
        }
        this.updatePosition();
        this.updateNodeState(0, proofNodes[0].x, proofNodes[0].y);
        this.addNodes(parentId);
        this.setNodeOnFocus(0);
    };

    nodeProps = (node: NodeInterface): NodeProps => {
        const { setFocusText } = this.props;
        return {
            id: node.id,
            rule: node.rule,
            conclusion: node.conclusion,
            onClick: this.onClick,
            updateNodeState: this.updateNodeState,
            setFocusText,
            setNodeOnFocus: this.setNodeOnFocus,
            toggleNodeSelection: this.toggleNodeSelection,
            x: node.x,
            y: node.y,
            hasChildren: node.children.length > 0,
            hidingNode: node.hidedNodes.length ? true : false,
            showingChildren: false,
            selected: false,
        };
    };

    toggleNodeSelection = (id: number): void => {
        const { showingNodes } = this.state;
        let { nodesSelected } = this.state;
        if (showingNodes[id].props.selected) {
            showingNodes[id] = new Node({ ...showingNodes[id].props, selected: false });
            nodesSelected = nodesSelected.filter((nodeId) => nodeId !== id);
        } else {
            showingNodes[id] = new Node({ ...showingNodes[id].props, selected: true });
            nodesSelected.push(id);
        }
        this.setState({ showingNodes, nodesSelected });
    };

    setNodeOnFocus = (id: number): void => {
        this.setState({ nodeOnFocus: id });
    };

    LineProps = (key: string, from: NodeProps, to: NodeProps): LineProps => ({
        key,
        points: [from.x + 150, from.y, to.x + 150, to.y + 71],
    });

    onClick = (e: { id: number; x: number; y: number }): void => {
        const { id } = e;
        const { proofNodes } = this.state;
        if (proofNodes[id].showingChildren) {
            this.removeNodes(id);
        } else {
            this.addNodes(id);
        }
    };

    addNodes = (id: number): void => {
        const { proofNodes, showingNodes } = this.state;
        proofNodes[id].children.forEach((child) => {
            this.addNode(proofNodes[child], proofNodes[id]);
            if (proofNodes[child].showingChildren) {
                this.addNodes(child);
            }
        });
        proofNodes[id].showingChildren = true;
        showingNodes[id] = new Node({ ...showingNodes[id].props, showingChildren: true });
        this.setState({ proofNodes, showingNodes });
    };

    addNode = (node: NodeInterface, parent: NodeInterface): void => {
        const { showingNodes, showingEdges } = this.state;

        showingNodes[node.id] = new Node(this.nodeProps(node));
        showingEdges[`${node.id}->${parent.id}`] = Line(
            this.LineProps(`${node.id}->${parent.id}`, showingNodes[node.id].props, showingNodes[parent.id].props),
        );
    };

    removeNodes = (id: number): void => {
        const { proofNodes, showingNodes } = this.state;
        this.recursivelyGetChildren(id).forEach((node) => {
            this.removeNode(node);
        });
        showingNodes[id] = new Node({ ...showingNodes[id].props, showingChildren: false });
        proofNodes[id].showingChildren = false;
        this.setState({ showingNodes, proofNodes });
    };

    removeNode = (id: number): void => {
        const { showingNodes, showingEdges } = this.state;
        Object.keys(showingEdges)
            .filter((edgeKey) => {
                const edges = edgeKey.split('->');
                return id === parseInt(edges[0]) || id === parseInt(edges[1]);
            })
            .forEach((edge) => {
                delete showingEdges[edge];
            });

        delete showingNodes[id];
        this.setState({ showingNodes, showingEdges });
    };

    hideNode = (id: number): void => {
        const { proofNodes } = this.state;
        const parentId = proofNodes[id].parent;
        let piId;
        if (proofNodes[parentId].hided) {
            // if the parent node is hided in some node
            piId = proofNodes[parentId].hidedIn;
            proofNodes[piId].children.push(...proofNodes[id].children);
            proofNodes[piId].children = proofNodes[piId].children.filter((nodeId) => nodeId !== id);
        } else if (proofNodes[parentId].hideMyChildNode) {
            // if the parent node has some node as child that hides node
            piId = proofNodes[parentId].hideMyChildNode;
            proofNodes[piId].conclusion =
                proofNodes[piId].conclusion.slice(0, -1) + "','" + proofNodes[id].conclusion + "']";
            proofNodes[piId].children.push(...proofNodes[id].children);
        } else {
            piId = proofNodes.length;
            proofNodes[piId] = {
                id: piId,
                conclusion: "['" + proofNodes[id].conclusion + "']",
                rule: 'π',
                children: [...proofNodes[id].children],
                x: NaN,
                y: NaN,
                showingChildren: true,
                parent: parentId,
                hided: false,
                hidedNodes: [],
                views: [],
                hideMyChildNode: NaN,
                hidedIn: NaN,
                positionCache: false,
            };
            proofNodes[parentId].hideMyChildNode = piId;
            proofNodes[parentId].children.push(piId);
        }
        proofNodes[piId].hidedNodes.push(id);
        proofNodes[id].hided = true;
        proofNodes[id].hidedIn = piId;
        proofNodes[parentId].children = proofNodes[parentId].children.filter((nodeId) => nodeId !== id);
        this.setState({ proofNodes });
    };

    unhideNode = (id: number): void => {
        const { proofNodes } = this.state;
        const parentId = proofNodes[id].parent;
        const piId = proofNodes[id].hidedIn;
        proofNodes[id].hided = false;
        proofNodes[parentId].children.push(id);
        proofNodes[piId].hidedNodes = proofNodes[piId].hidedNodes.filter((nodeId) => nodeId !== id);
        proofNodes[piId].children = proofNodes[piId].children.filter(
            (nodeId) => !proofNodes[id].children.some((child) => child === nodeId),
        );
        if (proofNodes[piId].hidedNodes.length === 0) {
            proofNodes[proofNodes[piId].parent].children = proofNodes[proofNodes[piId].parent].children.filter(
                (nodeId) => nodeId !== piId,
            );
            proofNodes[proofNodes[piId].parent].hideMyChildNode = NaN;
            delete proofNodes[piId];
        }
    };

    updatePosition = (): void => {
        const { proofNodes } = this.state;
        const g = new dagre.graphlib.Graph();
        g.setGraph({ rankdir: 'BT', ranker: 'tight-tree' });
        g.setDefaultEdgeLabel(function () {
            return {};
        });
        proofNodes.forEach((node) => {
            if (!node.hided) {
                g.setNode(node.id.toString(), { width: 300, height: 130 });
                proofNodes[node.id].children.forEach((child) => {
                    g.setEdge(child.toString(), node.id.toString());
                });
            }
        });
        dagre.layout(g);
        const xOffset = g.node(g.nodes()[0]).x - (proofNodes[0].x ? proofNodes[0].x : 0);
        const yOffset = g.node(g.nodes()[0]).y - (proofNodes[0].y ? proofNodes[0].y : 0);
        g.nodes().forEach(function (v) {
            const { x, y } = g.node(v);
            proofNodes[parseInt(v)].x = x - xOffset;
            proofNodes[parseInt(v)].y = y - yOffset;
        });
        this.setState({ proofNodes });
    };

    updateNodeState = (key: number, x: number, y: number): void => {
        const { showingNodes, showingEdges, proofNodes } = this.state;
        showingNodes[key] = new Node({ ...showingNodes[key].props, x, y });

        if (!proofNodes[key].showingChildren) {
            const [xOffset, yOffset] = [x - proofNodes[key].x, y - proofNodes[key].y];
            this.recursivelyGetChildren(key).forEach((node) => {
                proofNodes[node].x += xOffset;
                proofNodes[node].y += yOffset;
            });
        }
        proofNodes[key].positionCache = true;
        proofNodes[key] = { ...proofNodes[key], x, y };

        Object.keys(showingEdges)
            .filter((edgeKey) => edgeKey.indexOf(key.toString()) !== -1)
            .forEach((edge) => {
                const [from, to] = edge.split('->').map((x) => parseInt(x));
                showingEdges[edge] = Line(this.LineProps(edge, showingNodes[from].props, showingNodes[to].props));
            });
        this.setState({ showingNodes, showingEdges });
    };

    recursivelyGetChildren = (nodeId: number): Array<number> => {
        const { proofNodes, showingNodes } = this.state;
        let nodes: Array<number> = [];
        proofNodes[nodeId].children.forEach((node) => {
            nodes = nodes.concat([node]);
            if (proofNodes[node].showingChildren || !showingNodes[node])
                nodes = nodes.concat(this.recursivelyGetChildren(node));
        });
        return nodes;
    };

    render(): JSX.Element {
        const { canvasSize, stage, showingNodes, showingEdges, nodesSelected, nodeOnFocus, proofNodes } = this.state;
        return (
            <>
                <Menu
                    unfold={this.unfold}
                    foldSelectedNodes={this.foldSelectedNodes}
                    options={{
                        unfold: nodeOnFocus ? proofNodes[nodeOnFocus].rule === 'π' : false,
                        foldSelected: nodesSelected.length && nodesSelected.includes(nodeOnFocus) ? true : false,
                    }}
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
            </>
        );
    }
}
