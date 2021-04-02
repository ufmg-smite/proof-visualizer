import React, { useEffect, useState } from 'react';
import PropTypes from 'prop-types';
import axios from 'axios';
import Canvas from '../graphic-components/Canvas';

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

export default function VisualizeProof(props) {
  const { location } = props;
  const [dot, setDot] = useState(location.state.dot);
  const [label, setLabel] = useState(location.state.label);
  const [currentText, setCurrentText] = useState(
    'right-click in a node to show the text here'
  );
  const [textOfFocusNode, setTextOfFocusNode] = useState('');

  useEffect(() => {
    if (location.state) return;
    const proofId = location.pathname.split('/').slice(-1)[0];
    axios
      .get(`http://localhost:5000/proof/${proofId}`)
      .then((response) => {
        const { dotCp, labelCp } = JSON.parse(response.request.response);
        setDot(dotCp);
        setLabel(labelCp);
      })
      .catch((error) => {
        console.log(error);
      });
  }, []);

  const canvasContainerProps =
    textOfFocusNode !== '' ? { title: textOfFocusNode } : {};

  return (
    <div className="visualizer">
      <h3 className="proof-name">{label}</h3>
      {dot ? (
        // eslint-disable-next-line react/jsx-props-no-spreading
        <div className="canvas-container" {...canvasContainerProps}>
          {' '}
          <Canvas
            proofNodes={processDot(dot)}
            setCurrentText={setCurrentText}
            setFocusText={setTextOfFocusNode}
          />
        </div>
      ) : null}
      <div className="node-text">
        <p>{currentText}</p>
      </div>
    </div>
  );
}

VisualizeProof.propTypes = {
  location: PropTypes.any,
};
