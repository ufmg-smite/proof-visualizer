import React, { Component } from 'react';
import PropTypes from 'prop-types';
import Canvas from '../graphic-components/Canvas';

export default class VisualizeProof extends Component {
  constructor(props) {
    super(props);

    const {
      location: {
        state: { dot, label },
      },
    } = this.props;

    this.setCurrentText = this.setCurrentText.bind(this);

    this.state = {
      dot,
      label,
      currentText: 'click in a node to show the text here',
    };
  }

  setCurrentText(text) {
    this.setState({
      currentText: text,
    });
  }

  render() {
    const { label, dot, currentText } = this.state;
    return (
      <div className="visualizer">
        <h3>My proof - {label}</h3>
        <p>{currentText}</p>
        <Canvas dot={dot} setCurrentText={this.setCurrentText} />
      </div>
    );
  }
}

VisualizeProof.propTypes = {
  location: PropTypes.any,
};
