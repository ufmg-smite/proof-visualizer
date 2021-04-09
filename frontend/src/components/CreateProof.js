import React, { useState } from 'react';
import axios from 'axios';
import ProofForm from './ProofForm';

export default function CreateProof() {
  const [label, setLabel] = useState('');
  const [problem, setProblem] = useState('');
  const [options, setOptions] = useState('');

  const onSubmit = async (e) => {
    e.preventDefault();

    const proof = {
      label,
      problem,
      options,
    };
    await axios
      .post('http://localhost:5000/proof/add/', proof)
      .then((res) =>
        axios.get(`http://localhost:5000/proof/process-proof/${res.data}`)
      )
      .then(() => (window.location = '/'));
  };

  return (
    <ProofForm
      label={label}
      setLabel={setLabel}
      onSubmit={onSubmit}
      options={options}
      setOptions={setOptions}
      problem={problem}
      setProblem={setProblem}
    />
  );
}
