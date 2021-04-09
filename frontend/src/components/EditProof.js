import React from 'react';
import PropTypes from 'prop-types';
import axios from 'axios';
import ProofForm from './ProofForm';

export default function EditProof(props) {
  const { location } = props;
  if (!location.state) {
    window.location = '/';
  }
  const { id, error, label, problem, options } = location.state;

  const onSubmit = async (proof) => {
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
      options={options}
      problem={problem}
      onSubmit={onSubmit}
    />
  );
}

EditProof.propTypes = {
  location: PropTypes.any,
};
