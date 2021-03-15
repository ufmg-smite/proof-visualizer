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

    if (location.state.dot) {
      dot = location.state.dot;
      label = location.state.label;
    }

    this.setCurrentText = this.setCurrentText.bind(this);

    this.state = {
      dot,
      label,
      currentText: 'click in a node to show the text here',
    };
  }

  componentDidMount() {
    const { location } = this.props;
    if (location.state.label) return;
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

  render() {
    const { label, dot, currentText } = this.state;
    return (
      <div className="visualizer">
        <h3>My proof - {label}</h3>
        <p>{currentText}</p>
        {dot ? <Canvas dot={dot} setCurrentText={this.setCurrentText} /> : null}
      </div>
    );
  }
}

VisualizeProof.propTypes = {
  location: PropTypes.any,
};
