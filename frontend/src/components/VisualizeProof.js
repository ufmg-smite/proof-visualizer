import React, { Component } from 'react';
import axios from 'axios';

export default class VisualizeProof extends Component {
  constructor(props) {
    super(props);

    this.state = {
      svg: this.props.location.state.svg,
      svgReady: false
    }
  }

  componentDidMount(){
    if (!this.state.svg){
      axios.get('http://localhost:5000/proof/process-dot/'+this.props.match.params.id).then((response) => this.setState({svg: response.data}))
    }
  }

  render() {
    return (
    <div>
      <h3>My proof - {this.props.match.params.id}</h3>
      <div dangerouslySetInnerHTML={{__html : this.state.svg }}></div>
    </div>
    )
  }
}