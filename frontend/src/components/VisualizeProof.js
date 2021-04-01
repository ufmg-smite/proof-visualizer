import React, { useEffect, useState } from 'react';
import PropTypes from 'prop-types';
import axios from 'axios';
import Canvas from '../graphic-components/Canvas';

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
            dot={dot}
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
