import React, { useState, useEffect } from 'react';

import axios from 'axios';
import { Spinner } from '@blueprintjs/core';
import { ObjectID } from 'mongodb';

import ProofElementList from './ProofElementList';
import proof from './ProofInterface';

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

    const deleteProof = (id: ObjectID) => {
        axios.delete(`http://localhost:5000/proof/${id}`).then((response) => {
            console.log(response.data);
        });

        setProofs(proofs.filter((el: proof) => el._id !== id));
    };

    return (
        <>
            {loadingProofs ? (
                <Spinner size={30} />
            ) : (
                <div>
                    {proofs.map((proof, i) => (
                        <ProofElementList key={i} proof={proof} deleteProof={deleteProof} />
                    ))}
                </div>
            )}
        </>
    );
};

export default ProofList;
