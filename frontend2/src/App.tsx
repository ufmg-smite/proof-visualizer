import React, { useState } from 'react';
import VisualizerNavbar from './components/VisualizerNavbar';

const App: React.FC = () => {
    const [darkTheme, setDarkTheme] = useState(true);

    return (
        <div className={darkTheme ? ' bp3-dark' : ''}>
            <VisualizerNavbar darkTheme={darkTheme} setDarkTheme={setDarkTheme}></VisualizerNavbar>
        </div>
    );
};

export default App;
