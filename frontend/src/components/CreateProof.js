import React from 'react';
import axios from 'axios';
import ProofForm from './ProofForm';

export default function CreateProof() {
  const onSubmit = async (proof) => {
    await axios
      .post('http://localhost:5000/proof/add/', proof)
      .then((res) =>
        axios.get(`http://localhost:5000/proof/process-proof/${res.data}`)
      )
      .then(() => (window.location = '/'));
  };

  return <ProofForm onSubmit={onSubmit} />;
}
