import React, { useState } from 'react';
import PropTypes from 'prop-types';
import { Badge, Button, Form } from 'react-bootstrap';

export default function ProofForm(props) {
  const { edit, error, label, onSubmit, options, problem } = props;

  const [labelForm, setLabel] = useState(label);
  const [problemForm, setProblem] = useState(problem);
  const [optionsForm, setOptions] = useState(options);
  return (
    <Form
      onSubmit={(e) => {
        e.preventDefault();
        onSubmit({
          label: labelForm,
          problem: problemForm,
          options: optionsForm,
        });
      }}
    >
      <Form.Group>
        <Form.Label>Proof name </Form.Label>{' '}
        {error ? (
          <Badge className="bg-danger" variant="danger" title={error}>
            error
          </Badge>
        ) : null}
        <Form.Control
          name="label"
          type="text"
          placeholder="proof-a-and-not-a"
          value={labelForm}
          onChange={(evt) => setLabel(evt.target.value)}
        />
      </Form.Group>
      <Form.Group>
        <Form.Label>CVC4 Options</Form.Label>
        <Form.Control
          name="options"
          type="text"
          placeholder="Default options: --proof --dump-proof --proof-format-mode=dot"
          value={optionsForm}
          onChange={(evt) => setOptions(evt.target.value)}
        />
      </Form.Group>

      <Form.Group>
        <Form.Label>Problem</Form.Label>

        <Form.Control
          name="problem"
          as="textarea"
          rows={10}
          placeholder="(set-logic QF_UF)
(declare-fun a () Bool)
(assert (not a))
(assert a)
(check-sat)"
          value={problemForm}
          onChange={(evt) => setProblem(evt.target.value)}
        />
      </Form.Group>
      <Button variant="primary" type="submit">
        {edit ? 'Edit' : 'Generate'} proof
      </Button>
    </Form>
  );
}

ProofForm.propTypes = {
  edit: PropTypes.bool,
  error: PropTypes.any,
  label: PropTypes.string,
  onSubmit: PropTypes.func,
  options: PropTypes.string,
  problem: PropTypes.string,
};

ProofForm.defaultProps = {
  label: '',
  options: '',
  problem: '',
};
