import React from 'react';
import PropTypes from 'prop-types';
import ProofForm from './ProofForm';

export default function EditProof(props) {
  const { location } = props;
  if (!location.state) {
    window.location = '/';
  }
  const { id, error, label, problem, options } = location.state;

  return (
    <ProofForm
      edit
      id={id}
      error={error}
      label={label}
      options={options}
      problem={problem}
    />
  );
}

EditProof.propTypes = {
  location: PropTypes.any,
};
