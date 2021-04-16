import React, { useEffect, useState } from 'react';
import PropTypes from 'prop-types';
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
        if (!nodes[id]) nodes[id] = {};
        nodes[id].id = id;
        nodes[id].rule = text;
        nodes[id].children = [];
        nodes[id].showingChildren = false;
        nodes[id].conclusionPosition = { x: NaN, y: NaN };
        nodes[id].rulePosition = { x: NaN, y: NaN };
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
        if (!nodes[child]) nodes[child] = {};
        nodes[child].parent = parent;
      }
    }
  });
  return nodes;
}

const filterNodesByVision = (nodes, visionName) => {
  const filter = ['ASSUME', 'SCOPE'];
  let piNumber = 0;
  switch (visionName) {
    case 'normal':
      return nodes;
    case 'propositional':
      filter.push('CHAIN_RESOLUTION');
      break;
    default:
  }
  nodes.forEach((node) => {
    if (!filter.some((f) => node.rule.indexOf(f) !== -1)) {
      node.inVision = false;
    } else {
      node.inVision = true;
    }
  });
  nodes.forEach((node) => {
    if (!node.inVision) {
      if (nodes[node.parent].pi) {
        const index = nodes[node.parent].children.indexOf(node.id);
        if (index > -1) {
          nodes[node.parent].children.splice(index, 1);
        }
        node.children.forEach((child) => (nodes[child].parent = node.parent));
        nodes[node.parent].children.push(...node.children);
        delete nodes[node.id];
      } else {
        node.rule = `π${piNumber}`;
        node.pi = true;
        node.inVision = true;
        piNumber += 1;
      }
    }
  });
  return nodes;
};

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
  const [vision, setVision] = useState('normal');

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
        <span>
          <DropdownButton title="Vision" id="bg-vertical-dropdown-3">
            <Dropdown.Item
              eventKey="1"
              onClick={(e) => {
                e.preventDefault();
                setVision('normal');
              }}
            >
              normal
            </Dropdown.Item>
            <Dropdown.Divider />
            <Dropdown.Item
              eventKey="2"
              onClick={(e) => {
                e.preventDefault();
                setVision('basic');
              }}
            >
              basic
            </Dropdown.Item>
            <Dropdown.Item
              eventKey="3"
              onClick={(e) => {
                e.preventDefault();
                setVision('propositional');
              }}
            >
              propositional
            </Dropdown.Item>
          </DropdownButton>
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
        </span>
      </h3>

      {dot ? (
        // eslint-disable-next-line react/jsx-props-no-spreading
        <div className="canvas-container" {...canvasContainerProps}>
          {' '}
          <Canvas
            key={vision}
            proofNodes={filterNodesByVision(processDot(dot), vision)}
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
