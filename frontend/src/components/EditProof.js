import React, { useState } from 'react';
import PropTypes from 'prop-types';
import axios from 'axios';
import ProofForm from './ProofForm';

export default function EditProof(props) {
  const { location } = props;
  if (!location.state) {
    window.location = '/';
  }
  const { id, error } = location.state;
  const [label, setLabel] = useState(location.state.label);
  const [problem, setProblem] = useState(location.state.problem);
  const [options, setOptions] = useState(location.state.options);

  const onSubmit = async (e) => {
    e.preventDefault();

    const proof = {
      label,
      problem,
      options,
    };
    await axios
      .post(`http://localhost:5000/proof/edit/${id}`, proof)
      .then((res) =>
        axios.get(`http://localhost:5000/proof/process-proof/${res.data}`)
      )
      .then(() => (window.location = '/'));
  };

  return (
    <ProofForm
      edit
      error={error}
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

EditProof.propTypes = {
  location: PropTypes.any,
};
