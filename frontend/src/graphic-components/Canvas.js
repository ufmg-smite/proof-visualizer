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

    showingNodes['0c'] = new Node(
      this.nodeProps(
        proofNodes[0].conclusion,
        true,
        `${proofNodes[0].id}c`,
        0,
        0
      )
    );
    this.updateNodeState('0c', 0, 0);

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
        stageX: width / 2 - (showingNodes['0c'].props.x + 300 / 2),
        stageY: height / 10 - (showingNodes['0c'].props.y + 30 / 2),
      },
    });
  }

  nodeProps = (children, conclusion, id, x, y) => {
    const { setCurrentText, setFocusText } = this.props;
    return {
      children,
      conclusion,
      id,
      onClick: this.onClick,
      updateNodeState: this.updateNodeState,
      setFocusText,
      setCurrentText,
      x,
      y,
    };
  };

  lineProps = (key, from, to) => ({
    key,
    points: [from.x + 150, from.y, to.x + 150, to.y + 36],
  });

  onClick = (e) => {
    let { id, conclusion, x, y } = e.target.parent.attrs;
    const { proofNodes } = this.state;
    id = id.replace('c', '');

    if (conclusion && proofNodes[id].showingChildren) {
      this.removeNodes(id);
    } else if (conclusion) {
      this.addNodes(id, x, y);
    }
  };

  addNodes = (id, x, y) => {
    const { proofNodes, showingNodes } = this.state;
    this.addNode(proofNodes[id], proofNodes[id], false, x, y + 100);
    const lenChildren = proofNodes[id].children.length - 1;
    let xOffset = 0;
    proofNodes[id].children.forEach((child, i) => {
      xOffset += this.addNode(
        proofNodes[child],
        proofNodes[id],
        true,
        x + (i - lenChildren / 2) * 350 + xOffset,
        y + 200
      );
      if (proofNodes[child].showingChildren) {
        this.addNodes(child, x + (i - lenChildren / 2) * 350, y + 200);
      }
    });
    proofNodes[id].showingChildren = true;
    showingNodes[`${id}c`].props.showingChildren = true;
    this.setState({ showingNodes, proofNodes });
    return xOffset;
  };

  addNode = (node, parent, nodeConclusion, x, y) => {
    const { showingNodes, showingEdges, proofNodes } = this.state;
    const nodeKey = nodeConclusion ? `${node.id}c` : node.id;
    const parentKey = nodeConclusion ? parent.id : `${parent.id}c`;

    if (
      (nodeConclusion && proofNodes[node.id].conclusionPositionCache) ||
      (!nodeConclusion && proofNodes[node.id].rulePositionCache)
    ) {
      showingNodes[nodeKey] = new Node(
        this.nodeProps(
          nodeConclusion ? node.conclusion : node.rule,
          nodeConclusion,
          nodeKey,
          nodeConclusion
            ? proofNodes[node.id].conclusionPosition.x
            : proofNodes[node.id].rulePosition.x,
          nodeConclusion
            ? proofNodes[node.id].conclusionPosition.y
            : proofNodes[node.id].rulePosition.y
        )
      );
      showingEdges[`${nodeKey}->${parentKey}`] = new Line(
        this.lineProps(
          `${nodeKey}->${parentKey}`,
          showingNodes[nodeKey].props,
          showingNodes[parentKey].props
        )
      );
      return 0;
    }
    showingNodes[nodeKey] = new Node(
      this.nodeProps(
        nodeConclusion ? node.conclusion : node.rule,
        nodeConclusion,
        nodeKey,
        x,
        y
      )
    );
    showingEdges[`${nodeKey}->${parentKey}`] = new Line(
      this.lineProps(
        `${nodeKey}->${parentKey}`,
        showingNodes[nodeKey].props,
        showingNodes[parentKey].props
      )
    );
    this.updateNodeState(nodeKey, x, y);
    return this.checkOverlapAndPush(nodeKey);
  };

  checkOverlapAndPush = (nodeKey) => {
    const { showingNodes, proofNodes } = this.state;
    const parentNodeKey = proofNodes[nodeKey.replace('c', '')].parent;
    const parentX = parentNodeKey ? showingNodes[parentNodeKey].props.x : 0;
    let xOffset = 0;
    Object.keys(showingNodes).some((showingNodeKey) => {
      if (showingNodeKey !== nodeKey) {
        if (showingNodes[nodeKey].overlap(showingNodes[showingNodeKey])) {
          const parentShowingNodeKey =
            proofNodes[showingNodeKey.replace('c', '')].parent;
          const parentShowingNodeX = showingNodes[parentShowingNodeKey]
            ? showingNodes[parentShowingNodeKey].props.x
            : parentX;
          const parentOnRight = parentX >= parentShowingNodeX;
          xOffset = parentOnRight
            ? showingNodes[showingNodeKey].props.x +
              325 -
              showingNodes[nodeKey].props.x
            : showingNodes[showingNodeKey].props.x -
              25 -
              (showingNodes[nodeKey].props.x + 325);
          return true;
        }
      }
      return false;
    });

    if (xOffset) {
      this.findNodesToBeUpdated(nodeKey, xOffset > 0).forEach(
        (nodeToUpdateKey) => {
          if (showingNodes[nodeToUpdateKey]) {
            this.updateNodeState(
              nodeToUpdateKey,
              showingNodes[nodeToUpdateKey].props.x + xOffset,
              showingNodes[nodeToUpdateKey].props.y
            );
          }
        }
      );
    }
    return xOffset;
  };

  findNodesToBeUpdated = (nodeKey, right) => {
    const { proofNodes, showingNodes } = this.state;
    const nodesToBeUpdated = new Set();
    nodesToBeUpdated.add(nodeKey);
    const { x } = showingNodes[nodeKey].props;
    let parentKey = proofNodes[nodeKey.replace('c', '')].parent;
    const parents = [parentKey];
    while (showingNodes[parentKey]) {
      nodesToBeUpdated.add(parentKey);
      nodesToBeUpdated.add(`${parentKey}c`);
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

  updateNodeState = (key, x, y) => {
    const { showingNodes, showingEdges, proofNodes } = this.state;
    showingNodes[key].props.x = x;
    showingNodes[key].props.y = y;
    if (key.indexOf('c') === -1) {
      proofNodes[key].rulePositionCache = true;
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
      proofNodes[key.replace('c', '')].conclusionPositionCache = true;
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
