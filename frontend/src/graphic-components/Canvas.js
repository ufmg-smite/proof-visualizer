import React, { Component } from 'react';
import { Stage, Layer } from 'react-konva';
import PropTypes from 'prop-types';
import Node from './Node';
import Line from './Line';

export default class Canvas extends Component {
  constructor(props) {
    super(props);

    const { dot, setCurrentText, setFocusText } = this.props;

    const nodes = this.processDot(dot);

    this.state = {
      canvasWidth: 520,
      canvasHeight: 300,
      stageScale: 1,
      stageX: 0,
      stageY: 0,
      proofNodes: nodes,
      showingNodes: {},
      showingEdges: {},
      setCurrentText,
      setFocusText,
    };
  }

  componentDidMount() {
    const { showingNodes, proofNodes, canvasWidth } = this.state;
    showingNodes['0c'] = new Node({
      id: `${proofNodes[0].id}c`,
      onClick: (e) => this.onClick(e),
      name: proofNodes[0].id,
      x: canvasWidth * 0.5,
      y: 10,
      conclusion: true,
      children: proofNodes[0].conclusion,
      updateParentState: this.updateParentState,
      showingChildren: false,
      onMouseIn: this.onMouseIn,
      onMouseOut: this.onMouseOut,
    });
    this.setState({
      showingNodes,
      canvasWidth:
        document.getElementsByClassName('visualizer')[0].offsetWidth - 30,
      canvasHeight:
        window.innerHeight -
        (document.getElementsByClassName('navbar')[0].offsetHeight +
          20 +
          document.getElementsByClassName('proof-name')[0].offsetHeight +
          document.getElementsByClassName('node-text')[0].offsetHeight +
          50),
    });
  }

  onClick = (e) => {
    const {
      proofNodes,
      showingNodes,
      showingEdges,
      setCurrentText,
    } = this.state;
    const { id, x, y, conclusion } = e.target.parent.attrs;

    if (e.evt.button === 2) {
      setCurrentText(e.target.attrs.text);
      return;
    }

    if (!conclusion) return;
    if (proofNodes[id].showingChildren) {
      proofNodes[id].showingChildren = false;
      delete showingNodes[id];
      delete showingEdges[`${id}->${id}c`];
      const nodesToBeRemoved = this.recursivelyGetChildren(id);
      nodesToBeRemoved.forEach((node) => {
        proofNodes[node].showingChildren = false;
        delete showingNodes[node.toString()];
        delete showingNodes[`${node}c`];
        Object.keys(showingEdges)
          .filter((edgeKey) => {
            const edges = edgeKey.split('->');
            return (
              node.toString() === edges[0] ||
              `${node}c` === edges[0] ||
              node.toString() === edges[1] ||
              `${node}c` === edges[1]
            );
          })
          .forEach((edge) => {
            delete showingEdges[edge];
          });
      });
      showingNodes[`${id}c`].props.showingChildren = false;
      this.setState({ showingNodes, showingEdges });
      return;
    }

    const rule = new Node({
      id: proofNodes[id].id,
      name: proofNodes[id].id,
      x,
      y: y + 100,
      children: proofNodes[id].rule,
      onClick: this.onClick,
      updateParentState: this.updateParentState,
      onMouseIn: this.onMouseIn,
      onMouseOut: this.onMouseOut,
    });

    showingNodes[proofNodes[id].id.toString()] = rule;

    showingEdges[`${proofNodes[id].id}->${proofNodes[id].id}c`] = new Line({
      key: Math.random(),
      points: [
        showingNodes[proofNodes[id].id.toString()].props.x + 150,
        showingNodes[proofNodes[id].id.toString()].props.y,
        showingNodes[`${proofNodes[id].id.toString()}c`].props.x + 150,
        showingNodes[`${proofNodes[id].id.toString()}c`].props.y + 36,
      ],
    });

    let i = 0;
    const lenChildren = proofNodes[id].children.length - 1;
    proofNodes[id].children.map((child) => {
      const childNode = proofNodes[child];
      showingNodes[`${childNode.id}c`] = new Node({
        onClick: this.onClick,
        id: `${childNode.id}c`,
        name: childNode.id,
        x: x + (i - lenChildren / 2) * 350,
        y: y + 200,
        conclusion: true,
        children: childNode.conclusion,
        updateParentState: this.updateParentState,
        onMouseIn: this.onMouseIn,
        onMouseOut: this.onMouseOut,
      });
      i += 1;
      showingEdges[`${childNode.id}c->${proofNodes[id].id}`] = new Line({
        key: Math.random(),
        points: [
          showingNodes[`${childNode.id}c`].props.x + 150,
          showingNodes[`${childNode.id}c`].props.y,
          showingNodes[proofNodes[id].id.toString()].props.x + 150,
          showingNodes[proofNodes[id].id.toString()].props.y + 36,
        ],
      });
      return true;
    });
    proofNodes[id].showingChildren = true;
    showingNodes[`${id}c`].props.showingChildren = true;
    this.setState({ showingNodes, proofNodes, showingEdges });
  };

  handleWheel = (e) => {
    e.evt.preventDefault();

    const scaleBy = 1.08;
    const stage = e.target.getStage();
    const oldScale = stage.scaleX();
    const mousePointTo = {
      x: stage.getPointerPosition().x / oldScale - stage.x() / oldScale,
      y: stage.getPointerPosition().y / oldScale - stage.y() / oldScale,
    };

    const newScale = e.evt.deltaY > 0 ? oldScale * scaleBy : oldScale / scaleBy;

    this.setState({
      stageScale: newScale,
      stageX:
        -(mousePointTo.x - stage.getPointerPosition().x / newScale) * newScale,
      stageY:
        -(mousePointTo.y - stage.getPointerPosition().y / newScale) * newScale,
    });
  };

  onMouseIn = (text) => {
    const { setFocusText } = this.state;
    setFocusText(text);
  };

  onMouseOut = () => {
    const { setFocusText } = this.state;
    setFocusText('');
  };

  processDot = (dot) => {
    const numberOfNodes = (dot.match(/label/g) || []).length / 2;
    const nodes = new Array(numberOfNodes);
    const lines = dot
      .slice(dot.indexOf('{') + 1, dot.indexOf('}') - 2)
      .replace(/(\n|\t)/gm, '')
      .split(';');
    lines.forEach((line) => {
      if (line.search('label') !== -1) {
        const id = line.split('[')[0].trim().slice(1, -1);
        const text = line.slice(
          line.indexOf('label') + 9,
          line.lastIndexOf('"')
        );
        if (line.split('[')[0].search('c') === -1) {
          const node = {
            id,
            rule: text,
            children: [],
            showingChildren: false,
          };
          nodes[parseInt(node.id)] = node;
        } else {
          nodes[parseInt(id)].conclusion = text;
        }
      } else if (line.search('->') !== -1) {
        const edgeNodes = line
          .split('->')
          .map((element) =>
            element.trim().replaceAll('"', '').replace('c', '')
          );
        if (edgeNodes[0] !== edgeNodes[1]) {
          nodes[edgeNodes[1]].children.push(edgeNodes[0]);
        }
      }
    });
    return nodes;
  };

  updateParentState = (key, x, y) => {
    const { showingNodes, showingEdges } = this.state;
    showingNodes[key].props.x = x;
    showingNodes[key].props.y = y;
    Object.keys(showingEdges)
      .filter((edgeKey) => edgeKey.indexOf(key) !== -1)
      .forEach((edge) => {
        const [from, to] = edge.split('->');
        showingEdges[edge] = new Line({
          key: Math.random(),
          points: [
            showingNodes[from].props.x + 150,
            showingNodes[from].props.y,
            showingNodes[to].props.x + 150,
            showingNodes[to].props.y + 36,
          ],
        });
      });
    this.setState({ showingNodes, showingEdges });
  };

  recursivelyGetChildren(nodeId) {
    const { proofNodes } = this.state;
    let nodes = [];
    proofNodes[nodeId].children.forEach((node) => {
      nodes = nodes.concat([node]);
      if (proofNodes[node].showingChildren)
        nodes = nodes.concat(this.recursivelyGetChildren(node));
    });
    return nodes;
  }

  render() {
    const {
      canvasWidth,
      canvasHeight,
      stageScale,
      stageX,
      stageY,
      showingNodes,
      showingEdges,
    } = this.state;
    return (
      <Stage
        draggable
        width={canvasWidth}
        height={canvasHeight}
        onWheel={this.handleWheel}
        scaleX={stageScale}
        scaleY={stageScale}
        x={stageX}
        y={stageY}
        onContextMenu={(e) => e.evt.preventDefault()}
      >
        <Layer>
          {Object.keys(showingNodes).length === 0
            ? []
            : Object.keys(showingNodes).map(function (key) {
                return showingNodes[key].render();
              })}
          {Object.keys(showingEdges).length === 0
            ? []
            : Object.keys(showingEdges).map(function (key) {
                return showingEdges[key];
              })}
        </Layer>
      </Stage>
    );
  }
}

Canvas.propTypes = {
  dot: PropTypes.any,
  setCurrentText: PropTypes.func,
  setFocusText: PropTypes.func,
};
