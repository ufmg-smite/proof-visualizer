import React from 'react';
import { BrowserRouter as Router, Route} from 'react-router-dom';
import './App.css';
import 'bootstrap/dist/css/bootstrap.css';

import MyNavbar from './components/Navbar';
import ProofList from './components/ProofList';
import CreateProof from './components/CreateProof';
import VisualizeProof from './components/VisualizeProof';

function App() {
  return (
    <Router>
      <div className="container">
        <MyNavbar />
        <br />
        <Route path="/" exact component={ProofList} />
        <Route path="/create" exact component={CreateProof} />
        <Route path="/visualize/:id" exact component={VisualizeProof} />
      </div>
    </Router>
  );
}

export default App;
