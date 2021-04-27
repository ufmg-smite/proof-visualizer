import React, { Component } from 'react';
import { Stage, Layer } from 'react-konva';
import PropTypes from 'prop-types';
import dagre from 'dagre';
import Node from './Node';
import Line from './Line';

function handleWheel(e) {
  e.evt.preventDefault();

  const scaleBy = 1.08;
  const stage = e.target.getStage();
  const oldScale = stage.scaleX();
  const mousePointTo = {
    x: stage.getPointerPosition().x / oldScale - stage.x() / oldScale,
    y: stage.getPointerPosition().y / oldScale - stage.y() / oldScale,
  };

  const newScale = e.evt.deltaY > 0 ? oldScale * scaleBy : oldScale / scaleBy;

  return {
    stageScale: newScale,
    stageX:
      -(mousePointTo.x - stage.getPointerPosition().x / newScale) * newScale,
    stageY:
      -(mousePointTo.y - stage.getPointerPosition().y / newScale) * newScale,
  };
}

export default class Canvas extends Component {
  constructor(props) {
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
      nodeOnFocus: null,
    };
  }

  componentDidMount() {
    const { showingNodes, proofNodes } = this.state;

    this.basicView();
    this.updatePosition();
    showingNodes[0] = new Node(this.nodeProps(proofNodes[0]));
    this.addNodes(0);

    const [width, height] = [
      document.getElementsByClassName('visualizer')[0].offsetWidth - 30,
      window.innerHeight -
        (document.getElementsByClassName('navbar')[0].offsetHeight +
          20 +
          document.getElementsByClassName('proof-name')[0].offsetHeight +
          document.getElementsByClassName('node-text')[0].offsetHeight +
          50),
    ];

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

  basicView = () => {
    const { proofNodes } = this.state;
    proofNodes.forEach((node) => {
      if (node.views.indexOf('basic') === -1) this.hideNode(node.id);
    });
  };

  unfoldPropositionalView = () => {
    const { proofNodes, showingNodes, nodeOnFocus } = this.state;
    const parentId = proofNodes[nodeOnFocus].parent;
    this.removeNodes(parentId);
    const nodesToUnhide = [...proofNodes[nodeOnFocus].hidedNodes];
    nodesToUnhide.forEach((nodeId) => this.unhideNode(nodeId));
    nodesToUnhide.forEach((nodeId) => {
      if (proofNodes[nodeId].views.indexOf('propositional') === -1) {
        this.hideNode(nodeId);
      }
    });
    this.updatePosition();
    this.addNodes(parentId);
    delete showingNodes[nodeOnFocus];
    this.setState({ proofNodes });
  };

  unfoldTotalView = () => {
    const { proofNodes, nodeOnFocus } = this.state;
    const parentId = proofNodes[nodeOnFocus].parent;
    this.removeNodes(parentId);
    const nodesToUnhide = [...proofNodes[nodeOnFocus].hidedNodes];
    nodesToUnhide.forEach((nodeId) => this.unhideNode(nodeId));
    this.updatePosition();
    this.addNodes(parentId);
    this.setState({ proofNodes });
  };

  nodeProps = (node) => {
    const { setCurrentText, setFocusText } = this.props;
    return {
      id: node.id,
      rule: node.rule,
      conclusion: node.conclusion,
      onClick: this.onClick,
      updateNodeState: this.updateNodeState,
      setFocusText,
      setCurrentText,
      setNodeOnFocus: this.setNodeOnFocus,
      x: node.x,
      y: node.y,
      hasChildren: node.children.length > 0,
      piNode: node.piNode,
    };
  };

  setNodeOnFocus = (id) => {
    this.setState({ nodeOnFocus: id });
  };

  lineProps = (key, from, to) => ({
    key,
    points: [from.x + 150, from.y, to.x + 150, to.y + 71],
  });

  onClick = (e) => {
    const { id } = e;
    const { proofNodes } = this.state;
    if (proofNodes[id].showingChildren) {
      this.removeNodes(id);
    } else {
      this.addNodes(id);
    }
  };

  addNodes = (id) => {
    const { proofNodes, showingNodes } = this.state;
    proofNodes[id].children.forEach((child) => {
      this.addNode(proofNodes[child], proofNodes[id]);
      if (proofNodes[child].showingChildren) {
        this.addNodes(child);
      }
    });
    proofNodes[id].showingChildren = true;
    showingNodes[id].props.showingChildren = true;
    this.setState({ proofNodes, showingNodes });
  };

  addNode = (node, parent) => {
    const { showingNodes, showingEdges } = this.state;

    showingNodes[node.id] = new Node(this.nodeProps(node));
    showingEdges[`${node.id}->${parent.id}`] = new Line(
      this.lineProps(
        `${node.id}->${parent.id}`,
        showingNodes[node.id].props,
        showingNodes[parent.id].props
      )
    );
  };

  removeNodes = (id) => {
    const { proofNodes, showingNodes } = this.state;
    this.recursivelyGetChildren(id).forEach((node) => {
      this.removeNode(node);
    });
    showingNodes[id].props.showingChildren = false;
    proofNodes[id].showingChildren = false;
    this.setState({ showingNodes, proofNodes });
  };

  removeNode = (id) => {
    const { proofNodes, showingNodes, showingEdges } = this.state;
    Object.keys(showingEdges)
      .filter((edgeKey) => {
        const edges = edgeKey.split('->');
        return id === parseInt(edges[0]) || id === parseInt(edges[1]);
      })
      .forEach((edge) => {
        delete showingEdges[edge];
      });

    delete showingNodes[id];
    this.setState({ showingNodes, proofNodes, showingEdges });
  };

  hideNode = (id) => {
    const { proofNodes } = this.state;
    const parentId = proofNodes[id].parent;
    let piId;
    if (proofNodes[parentId].hided) {
      piId = proofNodes[parentId].hidedIn;
      proofNodes[piId].conclusion += proofNodes[id].conclusion;
      proofNodes[piId].children.push(...proofNodes[id].children);
      proofNodes[piId].children = proofNodes[piId].children.filter(
        (nodeId) => nodeId !== id
      );
    } else if (proofNodes[parentId].foldedNode) {
      piId = proofNodes[parentId].foldedNode;
      proofNodes[piId].conclusion += proofNodes[id].conclusion;
      proofNodes[piId].children.push(...proofNodes[id].children);
    } else {
      piId = proofNodes.length;
      proofNodes[piId] = {
        id: piId,
        conclusion: proofNodes[id].conclusion,
        rule: 'π',
        views: ['basic'],
        children: [...proofNodes[id].children],
        x: NaN,
        y: NaN,
        showingChildren: true,
        parent: parentId,
        hided: false,
        hidedNodes: [],
        piNode: true,
      };
      proofNodes[parentId].foldedNode = piId;
      proofNodes[parentId].children.push(piId);
    }
    proofNodes[piId].hidedNodes.push(id);
    proofNodes[id].hided = true;
    proofNodes[id].hidedIn = piId;
    proofNodes[parentId].children = proofNodes[parentId].children.filter(
      (nodeId) => nodeId !== id
    );
    this.setState({ proofNodes });
  };

  unhideNode = (id) => {
    const { proofNodes } = this.state;
    const parentId = proofNodes[id].parent;
    const piId = proofNodes[id].hidedIn;
    proofNodes[id].hided = false;
    proofNodes[parentId].children.push(id);
    proofNodes[piId].hidedNodes = proofNodes[piId].hidedNodes.filter(
      (nodeId) => nodeId !== id
    );
    proofNodes[piId].children = proofNodes[piId].children.filter(
      (nodeId) => !proofNodes[id].children.some((child) => child === nodeId)
    );
    if (proofNodes[piId].hidedNodes.length === 0) {
      proofNodes[proofNodes[piId].parent].children = proofNodes[
        proofNodes[piId].parent
      ].children.filter((nodeId) => nodeId !== piId);
      proofNodes[parentId].foldedNode = null;
      delete proofNodes[piId];
    }
  };

  updatePosition = () => {
    const { proofNodes } = this.state;
    const g = new dagre.graphlib.Graph();
    g.setGraph({ rankdir: 'BT' });
    g.setDefaultEdgeLabel(function () {
      return {};
    });
    proofNodes.forEach((node) => {
      if (!node.hided) {
        g.setNode(node.id, { width: 300, height: 130 });
        proofNodes[node.id].children.forEach((child) => {
          g.setEdge(child, node.id);
        });
      }
    });
    dagre.layout(g);
    g.nodes().forEach(function (v) {
      const { x, y } = g.node(v);
      proofNodes[v].x = x;
      proofNodes[v].y = y;
    });
    this.setState({ proofNodes });
  };

  updateNodeState = (key, x, y) => {
    const { showingNodes, showingEdges, proofNodes } = this.state;
    showingNodes[key].props.x = x;
    showingNodes[key].props.y = y;

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
      .filter((edgeKey) => edgeKey.indexOf(key) !== -1)
      .forEach((edge) => {
        const [from, to] = edge.split('->');
        showingEdges[edge] = new Line(
          this.lineProps(edge, showingNodes[from].props, showingNodes[to].props)
        );
      });
    this.setState({ showingNodes, showingEdges });
  };

  recursivelyGetChildren = (nodeId) => {
    const { proofNodes, showingNodes } = this.state;
    let nodes = [];
    proofNodes[nodeId].children.forEach((node) => {
      nodes = nodes.concat([node]);
      if (proofNodes[node].showingChildren || !showingNodes[node])
        nodes = nodes.concat(this.recursivelyGetChildren(node));
    });
    return nodes;
  };

  render() {
    const { canvasSize, stage, showingNodes, showingEdges } = this.state;
    return (
      <>
        <div id="menu">
          <div>
            <button
              onClick={(e) => this.unfoldTotalView(e)}
              type="button"
              id="pulse-button"
            >
              Unfold All Nodes
            </button>
            <button
              onClick={(e) => this.unfoldPropositionalView(e)}
              type="button"
              id="delete-button"
            >
              Unfold Propositional View
            </button>
          </div>
        </div>
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
              Object.keys(showingNodes).map(function (key) {
                return showingNodes[key].render();
              })}
          </Layer>
        </Stage>
      </>
    );
  }
}

Canvas.propTypes = {
  proofNodes: PropTypes.array,
  setCurrentText: PropTypes.func,
  setFocusText: PropTypes.func,
};
