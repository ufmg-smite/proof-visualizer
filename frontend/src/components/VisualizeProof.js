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

    this.state = {
      dot,
      label,
    };
  }

  render() {
    const { label, dot } = this.state;
    return (
      <div className="visualizer">
        <h3>My proof - {label}</h3>
        <Canvas dot={dot} />
      </div>
    );
  }
}

VisualizeProof.propTypes = {
  location: PropTypes.any,
};
