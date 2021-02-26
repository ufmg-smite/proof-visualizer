import React, { Component } from 'react';
import { Link } from 'react-router-dom';
import 'bootstrap/dist/css/bootstrap.min.css'

export default class Navbar extends Component {

  render() {
    return (
      <nav class="navbar navbar-dark bg-dark">
          <Link to="/" className="navbar-brand">Proof Viewer</Link>
        <div class="collapse navbar-collapse" id="navbarNavAltMarkup">
          <div class="navbar-nav">
            <Link to="/" className="nav-link">Proofs</Link>
            <Link to="/create" className="nav-link">New Proof</Link>
          </div>
        </div>
      </nav>
    );
  }
}