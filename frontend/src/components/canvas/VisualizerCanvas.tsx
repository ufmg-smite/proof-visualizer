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
        const { view } = this.props;

        this.applyView(view);

        this.updatePosition(0);
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

    applyView = (view: string | undefined): void => {
        const { proofNodes } = this.state;
        const nodesToHide = proofNodes.filter((node) => {
            switch (view) {
                case 'basic':
                    return node.views.indexOf('basic') === -1;
                case 'propositional':
                    return node.views.indexOf('basic') === -1 && node.views.indexOf('propositional') === -1;
                default:
                    return false;
            }
        });
        nodesToHide.forEach((node) => {
            if (!(proofNodes[node.id].rule === 'π' || node.id === 0)) {
                this.hideNode(node.id);
            }
        });
    };

    foldSelectedNodes = (): void => {
        const { proofNodes, nodesSelected, showingNodes } = this.state;
        this.removeNodes(0);
        nodesSelected
            .sort((a, b) => b - a)
            .forEach((nodeId) => {
                if (!(proofNodes[nodeId].rule === 'π' || nodeId === 0)) {
                    this.hideNode(nodeId);
                }
            });
        this.updatePosition(0);
        showingNodes[0] = new Node({ ...showingNodes[0].props, selected: false });
        this.addNodes(0);
        this.setState({ nodesSelected: [] });
    };

    unfold = (): void => {
        const { proofNodes, nodeOnFocus } = this.state;
        this.removeNodes(0);
        const nodesToUnhide = [...proofNodes[nodeOnFocus].hidedNodes];
        nodesToUnhide.forEach((nodeId) => this.unhideNode(nodeId));
        this.updatePosition(0);
        this.addNodes(0);
        this.setNodeOnFocus(0);
        this.setState({ nodesSelected: [] });
    };

    unfoldOnClick = (id: number): void => {
        this.setNodeOnFocus(id);
        setTimeout(() => this.unfold(), 10);
    };

    nodeProps = (node: NodeInterface): NodeProps => {
        const { openDrawer } = this.props;
        return {
            id: node.id,
            rule: node.rule,
            conclusion: node.conclusion,
            args: node.args,
            updateNodeState: this.updateNodeState,
            setNodeOnFocus: this.setNodeOnFocus,
            toggleNodeSelection: this.toggleNodeSelection,
            unfoldOnClick: this.unfoldOnClick,
            openDrawer: openDrawer,
            x: node.x,
            y: node.y,
            selected: false,
            nHided: node.hidedNodes.length,
            nDescendants: node.descendants,
            topHidedNodes: node.topHidedNodes ? node.topHidedNodes : undefined,
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
        points: [from.x + 150, from.y, to.x + 150, to.y + 105],
    });

    addNodes = (id: number): void => {
        const { proofNodes, showingNodes } = this.state;
        proofNodes[id].children.forEach((child) => {
            this.addNode(proofNodes[child], proofNodes[id]);
            this.addNodes(child);
        });
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

    ancestors = (id: number): Array<number> => {
        const { proofNodes } = this.state;
        const ancestorsId: Array<number> = [];
        let currentId = id;
        while (currentId) {
            currentId = proofNodes[currentId].parent;
            ancestorsId.push(currentId);
        }
        return ancestorsId;
    };

    hideNode = (id: number): void => {
        const { proofNodes } = this.state;
        const parentId = proofNodes[id].parent;
        let piId: number;
        if (parentId && proofNodes[parentId].hided) {
            // if the parent node is hided in some node
            piId = proofNodes[parentId].hidedIn;
            proofNodes[piId].children.push(...proofNodes[id].children);
            proofNodes[piId].children = proofNodes[piId].children.filter((nodeId) => nodeId !== id);
            if (proofNodes[piId].topHidedNodes) {
                proofNodes[piId].topHidedNodes = proofNodes[piId].topHidedNodes?.map((node) => {
                    if (this.ancestors(id).indexOf(node[0]) !== -1)
                        return [node[0], node[1], node[2], node[3] - 1, node[4] + 1];
                    return node;
                });
            }
        } else if (parentId && proofNodes[parentId].hideMyChildNode) {
            // if the parent node has some node as child that hides node
            piId = proofNodes[parentId].hideMyChildNode;
            let nH: number | undefined = 1,
                nD: number | undefined = 0;
            if (proofNodes[id].children.length === 1 && proofNodes[proofNodes[id].children[0]].rule === 'π') {
                proofNodes[proofNodes[id].children[0]].hidedNodes.forEach(
                    (child) => (proofNodes[child].hidedIn = piId),
                );
                proofNodes[piId].hidedNodes.push(...proofNodes[proofNodes[id].children[0]].hidedNodes);
                nD = proofNodes[proofNodes[id].children[0]].topHidedNodes?.reduce(
                    (accumulator, node) => accumulator + node[3],
                    0,
                );
                nH = proofNodes[proofNodes[id].children[0]].topHidedNodes?.reduce(
                    (accumulator, node) => accumulator + node[4],
                    0,
                );
                delete proofNodes[proofNodes[id].children[0]];
                proofNodes[id].children = [];
                proofNodes[id].hideMyChildNode = NaN;
            }
            proofNodes[piId].children.push(...proofNodes[id].children);
            proofNodes[piId].topHidedNodes?.push([
                id,
                proofNodes[id].rule,
                proofNodes[id].conclusion,
                nD ? nD : 0,
                nH ? nH : 0,
            ]);
            proofNodes[piId].descendants = nD ? nD : 0;
            proofNodes[piId].hidedIn = nH ? nH : 0;
        } else if (proofNodes[id].children.length === 1 && proofNodes[proofNodes[id].children[0]].rule === 'π') {
            piId = proofNodes[id].children[0];
            proofNodes[id].children = [];
            proofNodes[parentId].children.push(piId);
            proofNodes[parentId].hideMyChildNode = piId;
            proofNodes[piId].parent = parentId;
            proofNodes[piId].replace = id;
            proofNodes[piId].descendants = proofNodes[id].descendants;
            const nD = proofNodes[piId].topHidedNodes?.reduce((accumulator, node) => accumulator + node[3], 0);
            const nH = proofNodes[piId].topHidedNodes?.reduce((accumulator, node) => accumulator + node[4], 0);
            proofNodes[piId].topHidedNodes = [
                [id, proofNodes[id].rule, proofNodes[id].conclusion, nD ? nD : 0, nH ? nH + 1 : 0],
            ];
        } else {
            piId = proofNodes.length;
            proofNodes[piId] = {
                id: piId,
                conclusion: '∴',
                rule: 'π',
                args: '',
                children: [...proofNodes[id].children],
                x: NaN,
                y: NaN,
                parent: parentId,
                hided: false,
                hidedNodes: [],
                views: [],
                hideMyChildNode: NaN,
                hidedIn: NaN,
                positionCache: false,
                replace: id,
                descendants: 0,
                topHidedNodes: [
                    [id, proofNodes[id].rule, proofNodes[id].conclusion, proofNodes[id].descendants - 1, 1],
                ],
                rank: proofNodes[parentId].rank + 1,
            };
            proofNodes[parentId].hideMyChildNode = piId;
            proofNodes[parentId].children.push(piId);
            proofNodes[piId].descendants = proofNodes[id].descendants - 1;
        }
        proofNodes[piId].hidedNodes.push(id);
        proofNodes[id].hided = true;
        proofNodes[id].hidedIn = piId;
        proofNodes[parentId].children = proofNodes[parentId].children.filter((nodeId) => nodeId !== id);
        proofNodes[id].hideMyChildNode = NaN;
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

    updatePosition = (id: number): void => {
        const { proofNodes } = this.state;
        const g = new dagre.graphlib.Graph();
        g.setGraph({ rankdir: 'BT', ranker: 'tight-tree' });
        g.setDefaultEdgeLabel(function () {
            return {};
        });
        proofNodes.forEach((node) => {
            if (!node.hided) {
                if (node.rule !== 'π') {
                    g.setNode(node.id.toString(), { width: 300, height: 130 });
                    proofNodes[node.id].children.sort().forEach((child) => {
                        if (proofNodes[child].rule !== 'π') g.setEdge(child.toString(), node.id.toString());
                        else {
                            const childNode = proofNodes[child];
                            g.setEdge(
                                (childNode.replace ? childNode.replace : childNode.id).toString(),
                                node.id.toString(),
                            );
                        }
                    });
                } else {
                    g.setNode((node.replace ? node.replace : node.id).toString(), { width: 300, height: 130 });
                    proofNodes[node.id].children.forEach((child) => {
                        g.setEdge(child.toString(), (node.replace ? node.replace : node.id).toString());
                    });
                }
            }
        });
        dagre.layout(g);
        const xOffset = g.node(id.toString()).x - (proofNodes[id].x ? proofNodes[id].x : 0);
        const yOffset = g.node(id.toString()).y - (proofNodes[id].y ? proofNodes[id].y : 0);
        g.nodes().forEach(function (v) {
            const { x, y } = g.node(v);
            if (!proofNodes[parseInt(v)].hided) {
                proofNodes[parseInt(v)].x = x - xOffset;
                proofNodes[parseInt(v)].y = y - yOffset;
            } else {
                proofNodes[proofNodes[parseInt(v)].hidedIn].x = x - xOffset;
                proofNodes[proofNodes[parseInt(v)].hidedIn].y = y - yOffset;
            }
        });
        this.setState({ proofNodes });
    };

    updateNodeState = (key: number, x: number, y: number): void => {
        const { showingNodes, showingEdges, proofNodes } = this.state;
        showingNodes[key] = new Node({ ...showingNodes[key].props, x, y });

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
        const { proofNodes } = this.state;
        let nodes: Array<number> = [];
        proofNodes[nodeId].children.forEach((node) => {
            nodes = nodes.concat([node]);
            nodes = nodes.concat(this.recursivelyGetChildren(node));
        });
        return nodes;
    };

    foldAllDescendants = (): void => {
        const { nodeOnFocus } = this.state;
        this.setState({ nodesSelected: [nodeOnFocus, ...this.recursivelyGetChildren(nodeOnFocus)] }, () =>
            this.foldSelectedNodes(),
        );
    };

    render(): JSX.Element {
        const { canvasSize, stage, showingNodes, showingEdges, nodesSelected, nodeOnFocus, proofNodes } = this.state;
        return (
            <>
                <Menu
                    unfold={this.unfold}
                    foldSelectedNodes={this.foldSelectedNodes}
                    foldAllDescendants={this.foldAllDescendants}
                    options={{
                        unfold: proofNodes[nodeOnFocus] ? proofNodes[nodeOnFocus].rule === 'π' : false,
                        foldSelected: nodesSelected.length && nodesSelected.includes(nodeOnFocus) ? true : false,
                        foldAllDescendants: proofNodes[nodeOnFocus] && proofNodes[nodeOnFocus].children.length > 0,
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
