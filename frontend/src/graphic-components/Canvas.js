import React, { Component } from 'react';
import { Stage, Layer } from 'react-konva';
import PropTypes from 'prop-types';
import Node from './Node';

export default class Canvas extends Component {
  constructor(props) {
    super(props);

    const { dot } = this.props;

    const numberOfNodes = (dot.match(/label/g) || []).length / 2;
    const nodes = new Array(numberOfNodes);
    const edges = [];
    const lines = dot
      .slice(dot.indexOf('{') + 1, dot.indexOf('}') - 2)
      .replace(/(\n|\t)/gm, '')
      .split(';');
    lines.map((i) => {
      const line = i;
      if (line.search('label') !== -1) {
        if (line.split('[')[0].search('c') === -1) {
          const node = {
            id: line.split('[')[0].trim().slice(1, -1),
            rule: line.slice(line.indexOf('label') + 9, line.lastIndexOf('"')),
            ref: React.createRef(),
            children: [],
            clicked: false,
          };
          nodes[parseInt(node.id)] = node;
        } else {
          const id = line.split('[')[0].trim().slice(1, -1);
          nodes[parseInt(id)].conclusion = line.slice(
            line.indexOf('label') + 9,
            line.lastIndexOf('"')
          );
        }
      } else if (line.search('->') !== -1) {
        const edgeNodes = line
          .split('->')
          .map((element) =>
            element.trim().replaceAll('"', '').replace('c', '')
          );
        edges.push({ from: edgeNodes[0], to: edgeNodes[1] });
        if (edgeNodes[0] !== edgeNodes[1]) {
          nodes[edgeNodes[1]].children.push(edgeNodes[0]);
        }
      }
      return true;
    });

    this.state = {
      stageScale: 1,
      stageX: 0,
      stageY: 0,
      // dot,
      proofNodes: nodes,
      // proofEdges: edges,
      showingNodes: [],
    };
  }

  componentDidMount() {
    const { proofNodes } = this.state;
    this.setState({
      showingNodes: [
        <Node
          ref={proofNodes[0].ref}
          key={`${proofNodes[0].id}c`}
          id={`${proofNodes[0].id}c`}
          onClick={(e) => this.onClick(e)}
          name={proofNodes[0].id}
          y={10}
          x={window.innerWidth * 0.35}
          conclusion
        >
          {proofNodes[0].conclusion}
        </Node>,
      ],
    });
  }

  onClick = (e) => {
    const { proofNodes, showingNodes } = this.state;
    const myIndex = e.target.parent.attrs.id;
    if (proofNodes[myIndex].clicked) return;
    const newNodes = [
      <Node
        ref={proofNodes[myIndex].ref}
        key={proofNodes[myIndex].id}
        id={proofNodes[myIndex].id}
        name={proofNodes[myIndex].id}
        x={e.target.parent.attrs.x}
        y={e.target.parent.attrs.y + 42}
      >
        {proofNodes[myIndex].rule}
      </Node>,
    ];
    console.log(proofNodes);
    proofNodes[myIndex].children.map((child) => {
      console.log(child);
      const index = child;
      console.log(index);
      console.log(proofNodes[index]);
      newNodes.push(
        <Node
          ref={proofNodes[child].ref}
          onClick={(e2) => this.onClick(e2)}
          id={index}
          name={index}
          key={index}
          y={e.target.parent.attrs.y + 84}
          x={e.target.parent.attrs.x + child * 200}
          conclusion
        >
          {proofNodes[index].conclusion}
        </Node>
      );
      return true;
    });
    this.setState({
      showingNodes: [...showingNodes, ...newNodes],
    });
    const newProofNodes = proofNodes;
    newProofNodes[myIndex].clicked = true;
    this.setState({ proofNodes: newProofNodes });
  };

  handleWheel = (e) => {
    e.evt.preventDefault();

    const scaleBy = 1.02;
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

  render() {
    const { stageScale, stageX, stageY, showingNodes } = this.state;
    return (
      <Stage
        draggable
        width={window.innerWidth * 0.9}
        height={window.innerHeight * 0.7}
        onWheel={this.handleWheel}
        scaleX={stageScale}
        scaleY={stageScale}
        x={stageX}
        y={stageY}
      >
        <Layer>{showingNodes.map((element) => element)}</Layer>
      </Stage>
    );
  }
}

Canvas.propTypes = {
  dot: PropTypes.any,
};
