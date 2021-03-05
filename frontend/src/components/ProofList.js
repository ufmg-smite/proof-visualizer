import React, { Component } from 'react';
import { Link } from 'react-router-dom';
import axios from 'axios';
import { Spinner } from 'react-bootstrap';

const Proof = props => (
  <tr>
    <td>{props.proof.label}</td>
    <td>
      <Link to={{
            pathname: "/visualize/"+props.proof._id,
            state: {
              label: props.proof.label,
              dot: props.proof.dot ? props.proof.dot : false
            }}}
      >visualize</Link> | <a href="#" onClick={() => { props.deleteProof(props.proof._id) }}>delete</a>
    </td>
  </tr>
)

export default class ProofList extends Component {
  constructor(props) {
    super(props);

    this.deleteProof = this.deleteProof.bind(this)

    this.state = {proofs: [], loadingProofs: true};
  }

  componentDidMount() {
    axios.get('http://localhost:5000/proof/')
      .then(response => {
        this.setState({ proofs: response.data, loadingProofs: false })
      })
      .catch((error) => {
        console.log(error);
      })
  }

  deleteProof(id) {
    axios.delete('http://localhost:5000/proof/'+id)
      .then(response => { console.log(response.data)});

    this.setState({
        proofs: this.state.proofs.filter(el => el._id !== id)
    })
  }

  proofList() {
    return this.state.proofs.map(currentproof => {
      return <Proof proof={currentproof} deleteProof={this.deleteProof} key={currentproof._id}/>;
    })
  }

  render() {
    return (
      <div>
        <h3>Logged Proofs</h3>
        <table className="table">
          <thead className="thead-dark">
            <tr>
              <th>Label</th>
              <th>Actions</th>
            </tr>
          </thead>
          <tbody>
            { this.proofList() }
          </tbody>
        </table>
        {this.state.loadingProofs ? 
        <div className="spinner-container"><Spinner animation="border" role="status">
          <span className="sr-only">Loading...</span>
        </Spinner></div>: null}
      </div>
    )
  }
}