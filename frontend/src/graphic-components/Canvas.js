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
    };
  }

  componentDidMount() {
    const { showingNodes, proofNodes } = this.state;

    this.setLayer('0', 0);
    this.nodeXPosition();

    showingNodes['0c'] = new Node(
      this.nodeProps(
        proofNodes[0].conclusion,
        true,
        `${proofNodes[0].id}c`,
        proofNodes['0'].x,
        10
      )
    );

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
        stageX: width / 2 - (proofNodes['0'].conclusionPosition.x + 300 / 2),
        stageY: 10,
      },
    });
  }

  nodeProps = (children, conclusion, id) => {
    const { setCurrentText, setFocusText } = this.props;
    const { proofNodes } = this.state;
    return {
      children,
      conclusion,
      id,
      onClick: this.onClick,
      updateParentState: this.updateParentState,
      setFocusText,
      setCurrentText,
      x: conclusion
        ? proofNodes[id.replace('c', '')].conclusionPosition.x
        : proofNodes[id.replace('c', '')].rulePosition.x,
      y: conclusion
        ? proofNodes[id.replace('c', '')].conclusionPosition.y
        : proofNodes[id.replace('c', '')].rulePosition.y,
    };
  };

  lineProps = (key, from, to) => ({
    key,
    points: [from.x + 150, from.y, to.x + 150, to.y + 36],
  });

  onClick = (e) => {
    let { id, conclusion } = e.target.parent.attrs;
    const { proofNodes } = this.state;
    id = id.replace('c', '');

    if (conclusion && proofNodes[id].showingChildren) {
      this.removeNodes(id);
    } else if (conclusion) {
      this.addNodes(id);
    }
  };

  addNodes = (id) => {
    const { proofNodes, showingNodes } = this.state;
    this.addNode(proofNodes[id], proofNodes[id], false);
    proofNodes[id].children.forEach((child) => {
      this.addNode(proofNodes[child], proofNodes[id], true);
      if (proofNodes[child].showingChildren) {
        this.addNodes(child);
      }
    });
    proofNodes[id].showingChildren = true;
    showingNodes[`${id}c`].props.showingChildren = true;
    this.setState({ showingNodes, proofNodes });
  };

  addNode = (from, to, fromConclusion) => {
    const { showingNodes, showingEdges } = this.state;
    const fromKey = fromConclusion ? `${from.id}c` : from.id;
    const toKey = fromConclusion ? to.id : `${to.id}c`;

    showingNodes[fromKey] = new Node(
      this.nodeProps(
        fromConclusion ? from.conclusion : from.rule,
        fromConclusion,
        fromKey
      )
    );
    showingEdges[`${fromKey}->${toKey}`] = new Line(
      this.lineProps(
        `${fromKey}->${toKey}`,
        showingNodes[fromKey].props,
        showingNodes[toKey].props
      )
    );
  };

  removeNodes = (id) => {
    this.recursivelyGetChildren(id).forEach((node) => {
      this.removeNode(node, true);
    });
    this.removeNode(id, false);
  };

  removeNode = (id, deleteConclusion) => {
    const { proofNodes, showingNodes, showingEdges } = this.state;
    delete showingNodes[id];
    if (deleteConclusion) {
      delete showingNodes[`${id}c`];
      Object.keys(showingEdges)
        .filter((edgeKey) => {
          const edges = edgeKey.split('->');
          return (
            id === edges[0] ||
            `${id}c` === edges[0] ||
            id === edges[1] ||
            `${id}c` === edges[1]
          );
        })
        .forEach((edge) => {
          delete showingEdges[edge];
        });
    } else {
      showingNodes[`${id}c`].props.showingChildren = false;
      proofNodes[id].showingChildren = false;
      delete showingEdges[`${id}->${id}c`];
    }
    this.setState({ showingNodes, proofNodes, showingEdges });
  };

  updateParentState = (key, x, y) => {
    const { showingNodes, showingEdges, proofNodes } = this.state;
    showingNodes[key].props.x = x;
    showingNodes[key].props.y = y;
    if (key.indexOf('c') === -1) {
      proofNodes[key].rulePosition = { x, y };
    } else {
      if (!proofNodes[key.replace('c', '')].showingChildren) {
        const [xOffset, yOffset] = [
          x - proofNodes[key.replace('c', '')].conclusionPosition.x,
          y - proofNodes[key.replace('c', '')].conclusionPosition.y,
        ];
        proofNodes[key.replace('c', '')].rulePosition.x += xOffset;
        proofNodes[key.replace('c', '')].rulePosition.y += yOffset;
        this.recursivelyGetChildren(key.replace('c', '')).forEach((node) => {
          proofNodes[node].conclusionPosition.x += xOffset;
          proofNodes[node].conclusionPosition.y += yOffset;
          proofNodes[node].rulePosition.x += xOffset;
          proofNodes[node].rulePosition.y += yOffset;
        });
      }
      proofNodes[key.replace('c', '')].conclusionPosition = { x, y };
    }
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
    const { proofNodes } = this.state;
    let nodes = [];
    proofNodes[nodeId].children.forEach((node) => {
      nodes = nodes.concat([node]);
      if (proofNodes[node].showingChildren)
        nodes = nodes.concat(this.recursivelyGetChildren(node));
    });
    return nodes;
  };

  setLayer = (nodeId, layerNumber) => {
    const { proofNodes } = this.state;
    proofNodes[nodeId].layer = layerNumber;
    proofNodes[nodeId].children.forEach((node) => {
      this.setLayer(node, layerNumber + 1);
    });
    this.setState({ proofNodes });
  };

  nodeXPosition = () => {
    const { proofNodes } = this.state;
    const g = new dagre.graphlib.Graph();
    g.setGraph({ rankdir: 'BT' });
    g.setDefaultEdgeLabel(function () {
      return {};
    });

    proofNodes.forEach((node, i) => {
      g.setNode(i, { width: 300, height: 165, rank: node.layer });
      node.children.forEach((child) => {
        g.setEdge(child, node.id);
      });
    });

    dagre.layout(g);

    g.nodes().forEach(function (v) {
      const { x, y } = g.node(v);
      proofNodes[v].conclusionPosition = { x, y };
      proofNodes[v].rulePosition = { x, y: y + 100 };
    });
    this.setState({ proofNodes });
  };

  render() {
    const { canvasSize, stage, showingNodes, showingEdges } = this.state;
    return (
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
          {Object.keys(showingNodes).length > 0 &&
            Object.keys(showingNodes).map(function (key) {
              return showingNodes[key].render();
            })}
          {Object.keys(showingEdges).length > 0 &&
            Object.keys(showingEdges).map(function (key) {
              return showingEdges[key];
            })}
        </Layer>
      </Stage>
    );
  }
}

Canvas.propTypes = {
  proofNodes: PropTypes.array,
  setCurrentText: PropTypes.func,
  setFocusText: PropTypes.func,
};
