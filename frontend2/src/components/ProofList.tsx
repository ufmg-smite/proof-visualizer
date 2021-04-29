import React, { useState, useEffect } from 'react';

import axios from 'axios';
import { Spinner } from '@blueprintjs/core';

import ProofElementList from './ProofElementList';

const ProofList: React.FC = () => {
    const [proofs, setProofs] = useState([]);
    const [loadingProofs, setLoadingProofs] = useState(true);

    useEffect(() => {
        axios
            .get('http://localhost:5000/proof/')
            .then((response) => {
                setProofs(response.data.reverse());
                setLoadingProofs(false);
            })
            .catch((error) => {
                console.log(error);
            });
    }, []);

    return (
        <>
            {loadingProofs ? (
                <Spinner size={30} />
            ) : (
                <div>
                    {proofs.map((proof, i) => (
                        <ProofElementList key={i} proof={proof} />
                    ))}
                </div>
            )}
        </>
    );
};

export default ProofList;
