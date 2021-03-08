import React, { Component } from 'react';
import { Link } from 'react-router-dom';
import axios from 'axios';
import { Spinner } from 'react-bootstrap';
import PropTypes from 'prop-types';

const Proof = (props) => {
  const { proof, deleteProof } = props;
  return (
    <tr>
      <td>{proof.label}</td>
      <td>
        <Link
          to={{
            pathname: `/visualize/${proof._id}`,
            state: {
              label: proof.label,
              dot: proof.dot ? proof.dot : false,
            },
          }}
        >
          visualize
        </Link>{' '}
        |{' '}
        <a
          href="/"
          onClick={() => {
            deleteProof(props.proof._id);
          }}
        >
          delete
        </a>
      </td>
    </tr>
  );
};

export default class ProofList extends Component {
  constructor(props) {
    super(props);

    this.deleteProof = this.deleteProof.bind(this);

    this.state = { proofs: [], loadingProofs: true };
  }

  componentDidMount() {
    axios
      .get('http://localhost:5000/proof/')
      .then((response) => {
        this.setState({ proofs: response.data, loadingProofs: false });
      })
      .catch((error) => {
        console.log(error);
      });
  }

  deleteProof(id) {
    axios.delete(`http://localhost:5000/proof/${id}`).then((response) => {
      console.log(response.data);
    });

    const { proofs } = this.state;

    this.setState({
      proofs: proofs.filter((el) => el._id !== id),
    });
  }

  proofList() {
    const { proofs } = this.state;

    return proofs.map((currentproof) => (
      <Proof
        proof={currentproof}
        deleteProof={this.deleteProof}
        key={currentproof._id}
      />
    ));
  }

  render() {
    const { loadingProofs } = this.state;
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
          <tbody>{this.proofList()}</tbody>
        </table>
        {loadingProofs ? (
          <div className="spinner-container">
            <Spinner animation="border" role="status">
              <span className="sr-only">Loading...</span>
            </Spinner>
          </div>
        ) : null}
      </div>
    );
  }
}

Proof.propTypes = {
  label: PropTypes.any,
  proof: PropTypes.any,
  deleteProof: PropTypes.any,
};
