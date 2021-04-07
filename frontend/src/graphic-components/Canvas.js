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
      layer: [],
    };
  }

  componentDidMount() {
    const { showingNodes, proofNodes, canvasSize } = this.state;

    this.nodeXPosition('0', canvasSize.width * 0.5, 0);
    this.nodeFixXPosition('0', 0);

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
        stageX: width - (proofNodes['0'].x + 600),
        stageY: 10,
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
      updateParentState: this.updateParentState,
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
    let { id, x, y, conclusion } = e.target.parent.attrs;
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
    let [nodeX, nodeY] = [null, null];
    this.addNode(proofNodes[id], proofNodes[id], false, x, y);
    proofNodes[id].children.forEach((child) => {
      [nodeX, nodeY] = this.addNode(
        proofNodes[child],
        proofNodes[id],
        true,
        x,
        y
      );
      if (proofNodes[child].showingChildren) {
        this.addNodes(child, nodeX, nodeY);
      }
    });
    proofNodes[id].showingChildren = true;
    showingNodes[`${id}c`].props.showingChildren = true;
    this.setState({ showingNodes, proofNodes });
  };

  addNode = (from, to, fromConclusion, x, y) => {
    const { showingNodes, showingEdges } = this.state;
    const fromKey = fromConclusion ? `${from.id}c` : from.id;
    const toKey = fromConclusion ? to.id : `${to.id}c`;
    const [nodeX, nodeY] = [
      from.x + (x - to.x),
      y + 100 + (fromConclusion ? 100 : 0),
    ];
    showingNodes[fromKey] = new Node(
      this.nodeProps(
        fromConclusion ? from.conclusion : from.rule,
        fromConclusion,
        fromKey,
        nodeX,
        nodeY
      )
    );
    showingEdges[`${fromKey}->${toKey}`] = new Line(
      this.lineProps(
        `${fromKey}->${toKey}`,
        showingNodes[fromKey].props,
        showingNodes[toKey].props
      )
    );
    return [nodeX, nodeY];
  };

  removeNodes = (id) => {
    this.removeNode(id, false);
    this.recursivelyGetChildren(id).forEach((node) => {
      this.removeNode(node, true);
    });
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
    const { showingNodes, showingEdges } = this.state;
    showingNodes[key].props.x = x;
    showingNodes[key].props.y = y;
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

  nodeXPosition = (nodeId, x, layerNumber) => {
    const { proofNodes, layer } = this.state;
    proofNodes[nodeId].layer = layerNumber;
    layer[layerNumber] = 0;
    proofNodes[nodeId].x = x;
    const lenChildren = proofNodes[nodeId].children.length - 1;
    proofNodes[nodeId].children.forEach((node, i) => {
      this.nodeXPosition(
        node,
        proofNodes[nodeId].x + (i - lenChildren / 2) * 350,
        layerNumber + 1
      );
    });
    this.setState({ proofNodes, layer });
  };

  nodeFixXPosition = (nodeId, offsetFromParent) => {
    const { proofNodes, layer } = this.state;
    let offset = 0;
    if (
      proofNodes[nodeId].x + offsetFromParent <
      layer[proofNodes[nodeId].layer]
    ) {
      offset +=
        layer[proofNodes[nodeId].layer] -
        (proofNodes[nodeId].x + offsetFromParent);
    }
    proofNodes[nodeId].children.forEach((node) => {
      offset += this.nodeFixXPosition(node, offset + offsetFromParent);
    });
    if (proofNodes[nodeId].children.length) {
      proofNodes[nodeId].x =
        (proofNodes[proofNodes[nodeId].children[0]].x +
          proofNodes[
            proofNodes[nodeId].children[proofNodes[nodeId].children.length - 1]
          ].x) /
        2;
    } else {
      proofNodes[nodeId].x += offset + offsetFromParent;
    }
    layer[proofNodes[nodeId].layer] = proofNodes[nodeId].x + 350;
    return offset;
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
