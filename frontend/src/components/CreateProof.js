import React, { Component } from 'react';
import axios from 'axios';

export default class CreateProof extends Component {
  constructor(props) {
    super(props);

    this.state = {
      problem: '',
    }
  }

  onChangeProblem(e) {
    this.setState({
      problem: e.target.value,
      id: ''
    })
  }

  async onSubmit(e) {
    e.preventDefault();

    const proof = {
      problem: this.state.problem,
    }

    console.log(proof);

    await axios.post('http://localhost:5000/proof/add/', proof)
      .then(res => this.setState({id: res.data}));
    await axios.get('http://localhost:5000/proof/process-proof/'+this.state.id);
    window.location = '/';
  }

  render() {
    return (
    <div>
      <h3>Create New Proof</h3>
      <form onSubmit={this.onSubmit.bind(this)}>
        <div className="form-group"> 
          <label>Problem: </label>
          <input type='text'
              required
              height={'100px'}
              className="form-control"
              value={this.state.problem}
              onChange={this.onChangeProblem.bind(this)}>
          </input>
        </div>
        
        <div className="form-group">
          <input type="submit" value="Create Proof Log" className="btn btn-primary" />
        </div>
      </form>
    </div>
    )
  }
}