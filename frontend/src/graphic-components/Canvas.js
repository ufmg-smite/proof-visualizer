import React, { useState, useEffect } from 'react';
import { Stage, Layer } from 'react-konva';
import PropTypes from 'prop-types';
import Node from './Node';
import Line from './Line';

function processDot(dot) {
  const numberOfNodes = (dot.match(/label/g) || []).length / 2;
  const nodes = new Array(numberOfNodes);
  const lines = dot
    .slice(dot.indexOf('{') + 1, dot.indexOf('}') - 2)
    .replace(/(\n|\t)/gm, '')
    .split(';');
  lines.forEach((line) => {
    if (line.search('label') !== -1) {
      const id = line.split('[')[0].trim().slice(1, -1);
      const text = line.slice(line.indexOf('label') + 9, line.lastIndexOf('"'));
      if (line.split('[')[0].search('c') === -1) {
        const node = {
          id,
          rule: text,
          children: [],
          showingChildren: false,
        };
        nodes[node.id] = node;
      } else {
        nodes[id.replace('c', '')].conclusion = text;
      }
    } else if (line.search('->') !== -1) {
      const edgeNodes = line
        .split('->')
        .map((element) => element.trim().replaceAll('"', '').replace('c', ''));
      if (edgeNodes[0] !== edgeNodes[1]) {
        nodes[edgeNodes[1]].children.push(edgeNodes[0]);
      }
    }
  });
  return nodes;
}

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

export default function Canvas(props) {
  const { dot } = props;
  const [canvasWidth, setCanvasWidth] = useState(520);
  const [canvasHeight, setCanvasHeight] = useState(300);
  const [stage, setStage] = useState({
    stageScale: 1,
    stageX: 0,
    stageY: 0,
  });
  const [proofNodes, setProofNodes] = useState(processDot(dot));
  const [showingNodes, setShowingNodes] = useState({});
  const [showingEdges, setShowingEdges] = useState({});

  const recursivelyGetChildren = (nodeId) => {
    let nodes = [];
    proofNodes[nodeId].children.forEach((node) => {
      nodes = nodes.concat([node]);
      if (proofNodes[node].showingChildren)
        nodes = nodes.concat(recursivelyGetChildren(node));
    });
    return nodes;
  };

  const onMouse = (text) => {
    const { setFocusText } = props;
    setFocusText(text);
  };

  const updateParentState = (key, x, y) => {
    const cpShowingNodes = { ...showingNodes };
    const cpShowingEdges = { ...showingEdges };
    cpShowingNodes[key].props.x = x;
    cpShowingNodes[key].props.y = y;
    Object.keys(cpShowingEdges)
      .filter((edgeKey) => edgeKey.indexOf(key) !== -1)
      .forEach((edge) => {
        const [from, to] = edge.split('->');
        cpShowingEdges[edge] = new Line({
          key: Math.random(),
          points: [
            cpShowingNodes[from].props.x + 150,
            cpShowingNodes[from].props.y,
            cpShowingNodes[to].props.x + 150,
            cpShowingNodes[to].props.y + 36,
          ],
        });
      });
    setShowingNodes(cpShowingNodes);
    setShowingEdges(cpShowingEdges);
  };

  const onClick = (e) => {
    const { setCurrentText } = props;
    let { id, x, y, conclusion } = e.target.parent.attrs;
    id = id.replace('c', '');

    if (e.evt.button === 2) {
      setCurrentText(e.target.attrs.text);
      return;
    }

    if (!conclusion) return;

    const cpShowingNodes = { ...showingNodes };
    const cpShowingEdges = { ...showingEdges };

    if (proofNodes[id].showingChildren) {
      proofNodes[id].showingChildren = false;
      cpShowingNodes[id] = null;
      cpShowingEdges[`${id}->${id}c`] = null;
      const nodesToBeRemoved = recursivelyGetChildren(id);
      nodesToBeRemoved.forEach((node) => {
        proofNodes[node].showingChildren = false;
        cpShowingNodes[node.toString()] = null;
        cpShowingNodes[`${node}c`] = null;
        Object.keys(cpShowingEdges)
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
            cpShowingEdges[edge] = null;
          });
      });
      cpShowingNodes[`${id}c`] = new Node({
        id: `${id}c`,
        conclusion,
        children: proofNodes[id].conclusion,
        showingChildren: false,
        onClick,
        onMouse,
        updateParentState,
        x,
        y,
      });
      setShowingNodes(Object.assign(showingNodes, cpShowingNodes));
      setShowingEdges(Object.assign(showingEdges, cpShowingEdges));
      return;
    }

    const rule = new Node({
      children: proofNodes[id].rule,
      id: proofNodes[id].id,
      onClick,
      onMouse,
      updateParentState,
      x,
      y: y + 100,
    });

    cpShowingNodes[proofNodes[id].id.toString()] = rule;

    cpShowingEdges[`${proofNodes[id].id}->${proofNodes[id].id}c`] = new Line({
      key: Math.random(),
      points: [
        cpShowingNodes[proofNodes[id].id.toString()].props.x + 150,
        cpShowingNodes[proofNodes[id].id.toString()].props.y,
        cpShowingNodes[`${proofNodes[id].id.toString()}c`].props.x + 150,
        cpShowingNodes[`${proofNodes[id].id.toString()}c`].props.y + 36,
      ],
    });

    let i = 0;
    const lenChildren = proofNodes[id].children.length - 1;
    proofNodes[id].children.map((child) => {
      const childNode = proofNodes[child];
      console.log({ ...cpShowingNodes[`${id}c`].props });
      cpShowingNodes[`${childNode.id}c`] = new Node({
        children: childNode.conclusion,
        conclusion: true,
        id: `${childNode.id}c`,
        onClick,
        onMouse,
        updateParentState,
        x: x + (i - lenChildren / 2) * 350,
        y: y + 200,
      });
      i += 1;
      cpShowingEdges[`${childNode.id}c->${proofNodes[id].id}`] = new Line({
        key: Math.random(),
        points: [
          cpShowingNodes[`${childNode.id}c`].props.x + 150,
          cpShowingNodes[`${childNode.id}c`].props.y,
          cpShowingNodes[proofNodes[id].id.toString()].props.x + 150,
          cpShowingNodes[proofNodes[id].id.toString()].props.y + 36,
        ],
      });
      return true;
    });
    proofNodes[id].showingChildren = true;
    cpShowingNodes[`${id}c`] = new Node({
      id: `${id}c`,
      conclusion,
      children: proofNodes[id].conclusion,
      showingChildren: true,
      onClick,
      onMouse,
      updateParentState,
      x,
      y,
    });
    setShowingNodes(Object.assign(showingNodes, cpShowingNodes));
    setShowingEdges(Object.assign(showingEdges, cpShowingEdges));
    setProofNodes(proofNodes);
  };

  useEffect(() => {
    const cpShowingNodes = showingNodes;
    cpShowingNodes['0c'] = new Node({
      children: proofNodes[0].conclusion,
      conclusion: true,
      id: `${proofNodes[0].id}c`,
      onClick: (e) => onClick(e),
      onMouse,
      showingChildren: false,
      updateParentState,
      x: canvasWidth * 0.5,
      y: 10,
    });
    setShowingNodes(cpShowingNodes);
    setCanvasHeight(
      window.innerHeight -
        (document.getElementsByClassName('navbar')[0].offsetHeight +
          20 +
          document.getElementsByClassName('proof-name')[0].offsetHeight +
          document.getElementsByClassName('node-text')[0].offsetHeight +
          50)
    );
    setCanvasWidth(
      document.getElementsByClassName('visualizer')[0].offsetWidth - 30
    );
  }, []);

  return (
    <Stage
      draggable
      width={canvasWidth}
      height={canvasHeight}
      onWheel={(e) => setStage(handleWheel(e))}
      scaleX={stage.stageScale}
      scaleY={stage.stageScale}
      x={stage.stageX}
      y={stage.stageY}
      onContextMenu={(e) => e.evt.preventDefault()}
    >
      <Layer>
        {Object.keys(showingNodes).length === 0
          ? []
          : Object.keys(showingNodes).map(function (key) {
              return showingNodes[key];
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

Canvas.propTypes = {
  dot: PropTypes.any,
  setCurrentText: PropTypes.func,
  setFocusText: PropTypes.func,
};
