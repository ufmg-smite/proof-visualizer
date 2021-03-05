import React, { Component } from 'react';
import Canvas from '../graphic-components/Canvas'


export default class VisualizeProof extends Component {
  constructor(props) {
    super(props);

    this.state = {
      dot: this.props.location.state.dot,
    }
  }

  render() {
    return (
    <div className="visualizer">
      <h3>My proof - {this.props.location.state.label}</h3>
      <Canvas dot={this.state.dot}></Canvas>
    </div>
    )
  }
}