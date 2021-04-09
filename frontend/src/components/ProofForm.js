import React from 'react';
import PropTypes from 'prop-types';
import { Badge, Button, Form } from 'react-bootstrap';

export default function ProofForm(props) {
  const {
    edit,
    error,
    label,
    setLabel,
    onSubmit,
    options,
    setOptions,
    problem,
    setProblem,
  } = props;
  return (
    <Form onSubmit={onSubmit}>
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
          value={label}
          onChange={(evt) => setLabel(evt.target.value)}
        />
      </Form.Group>
      <Form.Group>
        <Form.Label>CVC4 Options</Form.Label>
        <Form.Control
          name="options"
          type="text"
          placeholder="Default options: --proof --dump-proof --proof-format-mode=dot"
          value={options}
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
          value={problem}
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
  setLabel: PropTypes.func,
  onSubmit: PropTypes.func,
  options: PropTypes.string,
  setOptions: PropTypes.func,
  problem: PropTypes.string,
  setProblem: PropTypes.func,
};
