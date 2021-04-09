import React, { useState } from 'react';
import PropTypes from 'prop-types';
import axios from 'axios';
import { Badge, Button, Form } from 'react-bootstrap';

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
        Edit proof
      </Button>
    </Form>
  );
}

EditProof.propTypes = {
  location: PropTypes.any,
};
