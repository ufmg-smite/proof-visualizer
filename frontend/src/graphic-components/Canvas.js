import React, { Component } from 'react';
import { Stage, Layer } from 'react-konva';
import PropTypes from 'prop-types';
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

    showingNodes[0] = new Node(this.nodeProps(proofNodes[0], 0, 0));
    this.updateNodeState(0, 0, 0);

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

  nodeProps = (node, x, y) => {
    const { setCurrentText, setFocusText } = this.props;
    return {
      id: node.id,
      rule: node.rule,
      conclusion: node.conclusion,
      onClick: this.onClick,
      updateNodeState: this.updateNodeState,
      setFocusText,
      setCurrentText,
      x,
      y,
      hasChildren: node.children.length > 0,
    };
  };

  lineProps = (key, from, to) => ({
    key,
    points: [from.x + 150, from.y, to.x + 150, to.y + 71],
  });

  onClick = (e) => {
    const { id, x, y } = e;
    const { proofNodes } = this.state;
    if (proofNodes[id].showingChildren) {
      this.removeNodes(id);
    } else {
      this.addNodes(id, x, y);
    }
  };

  addNodes = (id, x, y) => {
    const { proofNodes, showingNodes } = this.state;
    const lenChildren = proofNodes[id].children.length - 1;
    proofNodes[id].children.forEach((child, i) => {
      this.addNode(
        proofNodes[child],
        proofNodes[id],
        x + (i - lenChildren / 2) * 350,
        y + 100
      );
      if (proofNodes[child].showingChildren) {
        this.addNodes(child, x + (i - lenChildren / 2) * 350, y + 100);
      }
    });
    proofNodes[id].showingChildren = true;
    showingNodes[id].props.showingChildren = true;
    this.setState({ proofNodes, showingNodes });
  };

  addNode = (node, parent, x, y) => {
    const { showingNodes, showingEdges, proofNodes } = this.state;

    showingNodes[node.id] = new Node(this.nodeProps(node, x, y));
    showingEdges[`${node.id}->${parent.id}`] = new Line(
      this.lineProps(
        `${node.id}->${parent.id}`,
        showingNodes[node.id].props,
        showingNodes[parent.id].props
      )
    );

    if (proofNodes[node.id].positionCache) {
      this.updateNodeState(
        node.id,
        proofNodes[node.id].position.x,
        proofNodes[node.id].position.y
      );
      return 0;
    }

    this.updateNodeState(node.id, x, y);
  };

  findNodesToBeUpdated = (nodeKey, right) => {
    const { proofNodes, showingNodes } = this.state;
    const nodesToBeUpdated = new Set();
    nodesToBeUpdated.add(nodeKey);
    const { x } = showingNodes[nodeKey].props;
    let parentKey = proofNodes[nodeKey].parent;
    const parents = [parentKey];
    while (showingNodes[parentKey]) {
      nodesToBeUpdated.add(parentKey);
      proofNodes[parentKey].children.forEach((childKey) => {
        if (parents.indexOf(childKey) !== -1) return true;
        if (right) {
          if (showingNodes[childKey] && showingNodes[childKey].props.x >= x) {
            nodesToBeUpdated.add(childKey);
            this.recursivelyGetChildren(childKey).forEach((descendantKey) => {
              nodesToBeUpdated.add(descendantKey);
              nodesToBeUpdated.add(`${descendantKey}c`);
            });
          }
          if (
            showingNodes[`${childKey}c`] &&
            showingNodes[`${childKey}c`].props.x >= x
          ) {
            nodesToBeUpdated.add(`${childKey}c`);
          }
        } else {
          if (showingNodes[childKey] && showingNodes[childKey].props.x < x) {
            nodesToBeUpdated.add(childKey);
            this.recursivelyGetChildren(childKey).forEach((descendantKey) => {
              nodesToBeUpdated.add(descendantKey);
              nodesToBeUpdated.add(`${descendantKey}c`);
            });
          }
          if (
            showingNodes[`${childKey}c`] &&
            showingNodes[`${childKey}c`].props.x < x
          ) {
            nodesToBeUpdated.add(`${childKey}c`);
          }
        }
      });
      parentKey = proofNodes[parentKey].parent;
      parents.push(parentKey);
    }
    return nodesToBeUpdated;
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

  updateNodeState = (key, x, y) => {
    const { showingNodes, showingEdges, proofNodes } = this.state;
    showingNodes[key].props.x = x;
    showingNodes[key].props.y = y;

    if (!proofNodes[key].showingChildren) {
      const [xOffset, yOffset] = [
        x - proofNodes[key].position.x,
        y - proofNodes[key].position.y,
      ];
      this.recursivelyGetChildren(key).forEach((node) => {
        proofNodes[node].position.x += xOffset;
        proofNodes[node].position.y += yOffset;
      });
    }
    proofNodes[key].positionCache = true;
    proofNodes[key].position = { x, y };

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
