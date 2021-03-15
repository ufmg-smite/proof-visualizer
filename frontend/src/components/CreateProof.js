import React, { Component } from 'react';
import axios from 'axios';
import { Form, Button } from 'react-bootstrap';

export default class CreateProof extends Component {
  constructor(props) {
    super(props);

    this.onSubmit = this.onSubmit.bind(this);
    this.handleChange = this.handleChange.bind(this);

    this.state = {
      label: '',
      problem: '',
      inputLanguage: '',
      options: '',
    };
  }

  handleChange(evt) {
    this.setState({ [evt.target.name]: evt.target.value });
  }

  async onSubmit(e) {
    e.preventDefault();

    let { label, problem, inputLanguage, id, options } = this.state;

    const proof = {
      label,
      problem,
      inputLanguage,
      options,
    };
    await axios
      .post('http://localhost:5000/proof/add/', proof)
      .then((res) =>
        this.setState({ id: res.data }, () => ({ id } = this.state))
      );
    await axios.get(`http://localhost:5000/proof/process-proof/${id}`);
    window.location = '/';
  }

  render() {
    return (
      <Form onSubmit={this.onSubmit}>
        <Form.Group>
          <Form.Label>Problem label</Form.Label>
          <Form.Control
            name="label"
            type="text"
            placeholder="proof-a-and-not-a"
            onChange={this.handleChange}
          />
        </Form.Group>
        <Form.Group>
          <Form.Label>CVC4 Options</Form.Label>
          <Form.Control
            name="options"
            type="text"
            placeholder="Default options: --proof --dump-proof --proof-format-mode=dot"
            onChange={this.handleChange}
          />
        </Form.Group>
        <Form.Group onChange={this.handleChange}>
          <Form.Label>Input language</Form.Label>
          <Form.Control
            name="inputLanguage"
            onChange={this.handleChange}
            as="select"
          >
            <option>SMT-LIB v2</option>
            <option>CVC4 Native Input Language</option>
            <option>SyGuS-IF</option>
            <option>TPTP</option>
          </Form.Control>
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
            onChange={this.handleChange}
          />
        </Form.Group>
        <Button variant="primary" type="submit">
          Submit
        </Button>
      </Form>
    );
  }
}
