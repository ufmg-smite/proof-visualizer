import React, { useEffect, useState } from 'react';
import { Link } from 'react-router-dom';
import axios from 'axios';
import { Spinner, Badge } from 'react-bootstrap';
import PropTypes from 'prop-types';

const Proof = (props) => {
  const { proof, deleteProof } = props;
  return (
    <tr>
      <td>
        {proof.label}{' '}
        {proof.state === 'error' ? (
          <Badge className="bg-danger" variant="danger">
            error
          </Badge>
        ) : null}
      </td>
      <td>
        {proof.state !== 'error' ? (
          <Link
            to={{
              pathname: `/visualize/${proof._id}`,
              state: {
                label: proof.label,
                dot: proof.dot ? proof.dot : false,
                problem: `%%% ${proof.options} --dump-proof --proof-format-mode=dot --proof\n${proof.problem}`,
              },
            }}
          >
            visualize
          </Link>
        ) : (
          <a
            href="/"
            onClick={(e) => {
              e.preventDefault();
            }}
          >
            view error
          </a>
        )}{' '}
        |{' '}
        <a
          href="/"
          onClick={(e) => {
            e.preventDefault();
            deleteProof(props.proof._id);
          }}
        >
          delete
        </a>
      </td>
    </tr>
  );
};

export default function ProofList() {
  const [proofs, setProofs] = useState([]);
  const [loadingProofs, setLoadingProofs] = useState(true);

  useEffect(() => {
    axios
      .get('http://localhost:5000/proof/')
      .then((response) => {
        setProofs(response.data.reverse());
        setLoadingProofs(false);
      })
      .catch((error) => {
        console.log(error);
      });
  }, []);

  const deleteProof = (id) => {
    axios.delete(`http://localhost:5000/proof/${id}`).then((response) => {
      console.log(response.data);
    });

    setProofs(proofs.filter((el) => el._id !== id));
  };

  const proofList = () =>
    proofs.map((currentproof) => (
      <Proof
        proof={currentproof}
        deleteProof={deleteProof}
        key={currentproof._id}
      />
    ));

  return (
    <div>
      <h3>Proofs</h3>
      <table className="table">
        <thead className="thead-dark">
          <tr>
            <th>Name</th>
            <th>Actions</th>
          </tr>
        </thead>
        <tbody>{proofList()}</tbody>
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

Proof.propTypes = {
  label: PropTypes.any,
  proof: PropTypes.any,
  deleteProof: PropTypes.any,
};
