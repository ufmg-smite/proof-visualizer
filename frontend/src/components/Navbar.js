import React, { Component } from 'react';
import { Link } from 'react-router-dom';
import { Navbar, Nav } from 'react-bootstrap';

export default class MyNavbar extends Component {

  render() {
    return (
      <Navbar bg="light" expand="lg">
        <Navbar.Brand href="/">Proof Visualizer</Navbar.Brand>
        <Navbar.Toggle aria-controls="basic-navbar-nav" />
        <Navbar.Collapse id="basic-navbar-nav">
          <Nav className="mr-auto">
            <Nav.Link href="/" className="nav-link">Proofs</Nav.Link>
            <Nav.Link href="/create" className="nav-link">New Proof</Nav.Link>
          </Nav>
        </Navbar.Collapse>
      </Navbar>
    );
  }
}