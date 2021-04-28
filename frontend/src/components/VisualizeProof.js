import React, { useEffect, useState } from 'react';
import PropTypes from 'prop-types';
import axios from 'axios';
import { DropdownButton, Dropdown } from 'react-bootstrap';
import Canvas from '../graphic-components/Canvas';

function removeEscapedCharacters(s) {
  let newS = '';
  for (let i = 0; i < s.length; i += 1) {
    if (
      !(
        s[i] === '\\' &&
        (s[i + 1] === '"' ||
          s[i + 1] === '>' ||
          s[i + 1] === '<' ||
          s[i + 1] === '{' ||
          s[i + 1] === '}' ||
          s[i + 1] === '|')
      )
    ) {
      newS += s[i];
    }
  }

  return newS;
}

function processDot(dot) {
  const nodes = [];
  const lines = dot
    .slice(dot.indexOf('{') + 1, dot.lastIndexOf('}') - 2)
    .replace(/(\n|\t)/gm, '')
    .split(';');
  lines.forEach((line) => {
    if (line.search('label') !== -1) {
      let [id, attributes] = [
        parseInt(line.slice(0, line.indexOf('[')).trim()),
        line.slice(line.indexOf('[') + 1, line.lastIndexOf(']')).trim(),
      ];

      let label = attributes.slice(attributes.search(/(?<!\\)"/) + 2);
      label = label.slice(0, label.search(/(?<!\\)"/) - 1);
      const [conclusion, rule] = label.split(/(?<!\\)\|/);

      attributes = attributes.slice(
        attributes.indexOf(', class = ') + ', class = '.length
      );
      const views = attributes
        .slice(attributes.indexOf('"') + 1, attributes.lastIndexOf('"'))
        .trim()
        .split(' ');

      if (!nodes[id]) nodes[id] = {};
      nodes[id].id = id;
      nodes[id].conclusion = removeEscapedCharacters(conclusion);
      nodes[id].rule = removeEscapedCharacters(rule);
      nodes[id].views = views;
      nodes[id].children = [];
      nodes[id].x = NaN;
      nodes[id].y = NaN;
      nodes[id].foldedNode = null;
      nodes[id].showingChildren = true;
      nodes[id].hided = false;
    } else if (line.search('->') !== -1) {
      let [child, parent] = line.split('->');
      [child, parent] = [parseInt(child.trim()), parseInt(parent.trim())];
      nodes[parent].children.push(child);
      if (!nodes[child]) nodes[child] = {};
      nodes[child].parent = parseInt(parent);
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
  const [view, setView] = useState('normal');

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
          <DropdownButton title="View" id="bg-vertical-dropdown-3">
            <Dropdown.Item
              eventKey="1"
              onClick={(e) => {
                e.preventDefault();
                setView('normal');
              }}
            >
              normal
            </Dropdown.Item>
            <Dropdown.Divider />
            <Dropdown.Item
              eventKey="2"
              onClick={(e) => {
                e.preventDefault();
                setView('basic');
              }}
            >
              basic
            </Dropdown.Item>
            <Dropdown.Item
              eventKey="3"
              onClick={(e) => {
                e.preventDefault();
                setView('propositional');
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
            key={view}
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
