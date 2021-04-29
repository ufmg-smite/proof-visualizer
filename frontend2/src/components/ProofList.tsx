import React, { useState, useEffect } from 'react';

import axios from 'axios';
import { Spinner } from '@blueprintjs/core';
import { ObjectID } from 'mongodb';

import ElementProofList from './ElementProofList';
import proof from './ProofInterface';

interface ProofListProps {
    addDeleteToast: (err: string) => void;
}

const ProofList: React.FC<ProofListProps> = ({ addDeleteToast }: ProofListProps) => {
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

    const deleteProof = (id: ObjectID | undefined, name: string) => {
        axios.delete(`http://localhost:5000/proof/${id}`).then(() => {
            addDeleteToast(name);
        });

        setProofs(proofs.filter((el: proof) => el._id !== id));
    };

    return (
        <>
            {loadingProofs ? (
                <div style={{ height: '200px', paddingTop: '50px' }}>
                    <Spinner size={30} />
                </div>
            ) : (
                <div>
                    {proofs.map((proof, i) => (
                        <ElementProofList key={i} proof={proof} deleteProof={deleteProof} />
                    ))}
                </div>
            )}
        </>
    );
};

export default ProofList;
