import React, { useEffect, useState } from 'react';
import PropTypes, { node } from 'prop-types';
import axios from 'axios';
import { DropdownButton, Dropdown } from 'react-bootstrap';
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
        if (!node[node.id]) nodes[id] = {};
        nodes[id].id = id;
        nodes[id].rule = text;
        nodes[id].children = [];
        nodes[id].showingChildren = false;
      } else {
        nodes[id.replace('c', '')].conclusion = text;
      }
    } else if (line.search('->') !== -1) {
      const edgeNodes = line
        .split('->')
        .map((element) => element.trim().replaceAll('"', '').replace('c', ''));
      if (edgeNodes[0] !== edgeNodes[1]) {
        const [child, parent] = edgeNodes;
        nodes[parent].children.push(child);
        if (!node[node.id]) nodes[child] = {};
        nodes[child].parent = parent;
      }
    }
  });
  return nodes;
}

export default function VisualizeProof(props) {
  const { location } = props;
  const [dot, setDot] = useState(location.state ? location.state.dot : false);
  const [problem, setProblem] = useState(
    location.state ? location.state.problem : null
  );
  const [label, setLabel] = useState(
    location.state ? location.state.label : null
  );
  const [currentText, setCurrentText] = useState(
    'right-click in a node to show the text here'
  );
  const [textOfFocusNode, setTextOfFocusNode] = useState('');

  useEffect(() => {
    if (location.state.dot) return;
    const proofId = location.pathname.split('/').slice(-1)[0];

    axios
      .get(`http://localhost:5000/proof/${proofId}`)
      .then((response) => {
        const proof = JSON.parse(response.request.response);
        setDot(proof.dot);
        setLabel(proof.label);
        setProblem(
          `%%% ${`${proof.options} --dump-proof --proof-format-mode=dot --proof`}\n${
            proof.problem
          }`
        );
      })
      .catch((error) => {
        console.log(error);
      });
  }, []);

  const canvasContainerProps =
    textOfFocusNode !== '' ? { title: textOfFocusNode } : {};

  return (
    <div className="visualizer">
      <h3 className="proof-name">
        <span>{label}</span>
        <DropdownButton title="Download" id="bg-vertical-dropdown-3">
          <Dropdown.Item
            eventKey="1"
            href={`data:attachment/text,${encodeURIComponent(dot)}`}
            download={label ? `${label.replaceAll(' ', '_')}.dot` : ''}
          >
            dot
          </Dropdown.Item>
          <Dropdown.Item
            eventKey="2"
            href={`data:attachment/text,${encodeURIComponent(problem)}`}
            download={label ? `${label.replaceAll(' ', '_')}.smt2` : null}
          >
            problem
          </Dropdown.Item>
          <Dropdown.Item
            eventKey="3"
            onClick={(e) => {
              e.preventDefault();
              const link = document.createElement('a');
              link.download = label
                ? `${label.replaceAll(' ', '_')}.png`
                : null;
              link.href = document
                .getElementsByClassName('konvajs-content')[0]
                .children[0].toDataURL('image/png');
              link.click();
            }}
          >
            png
          </Dropdown.Item>
        </DropdownButton>
      </h3>

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
