import React, { Component } from 'react';
import PropTypes from 'prop-types';
import axios from 'axios';
import Canvas from '../graphic-components/Canvas';

export default class VisualizeProof extends Component {
  constructor(props) {
    super(props);

    const { location } = this.props;

    let dot = null;
    let label = null;

    if (location.state) {
      dot = location.state.dot;
      label = location.state.label;
    }

    this.setCurrentText = this.setCurrentText.bind(this);
    this.setFocusText = this.setFocusText.bind(this);

    this.state = {
      dot,
      label,
      currentText: 'right-click in a node to show the text here',
      textOfFocusNode: '',
    };
  }

  componentDidMount() {
    const { location } = this.props;
    if (location.state) return;
    const proofId = location.pathname.split('/').slice(-1)[0];
    axios
      .get(`http://localhost:5000/proof/${proofId}`)
      .then((response) => {
        const { dot, label } = JSON.parse(response.request.response);
        this.setState({
          dot,
          label,
        });
      })
      .catch((error) => {
        console.log(error);
      });
  }

  setCurrentText(text) {
    this.setState({
      currentText: text,
    });
  }

  setFocusText(text) {
    this.setState({
      textOfFocusNode: text,
    });
  }

  render() {
    const { label, dot, currentText, textOfFocusNode } = this.state;
    const props = textOfFocusNode !== '' ? { title: textOfFocusNode } : {};

    return (
      <div className="visualizer">
        <h3>{label}</h3>
        {dot ? (
          // eslint-disable-next-line react/jsx-props-no-spreading
          <div {...props}>
            {' '}
            <Canvas
              dot={dot}
              setCurrentText={this.setCurrentText}
              setFocusText={this.setFocusText}
            />
          </div>
        ) : null}
        <div className="node-text">
          <p>{currentText}</p>
        </div>
      </div>
    );
  }
}

VisualizeProof.propTypes = {
  location: PropTypes.any,
};
