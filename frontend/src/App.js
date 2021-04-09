import React from 'react';
import { BrowserRouter as Router, Route } from 'react-router-dom';
import './App.scss';
import 'bootstrap/dist/css/bootstrap.css';

import MyNavbar from './components/Navbar';
import ProofList from './components/ProofList';
import ProofForm from './components/ProofForm';
import EditProof from './components/EditProof';
import VisualizeProof from './components/VisualizeProof';

function App() {
  return (
    <Router>
      <div className="container">
        <MyNavbar />
        <Route path="/" exact component={ProofList} />
        <Route path="/create" exact component={ProofForm} />
        <Route path="/edit/:id" exact component={EditProof} />
        <Route path="/visualize/:id" exact component={VisualizeProof} />
      </div>
    </Router>
  );
}

export default App;
