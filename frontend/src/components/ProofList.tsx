import React, { useState, useEffect, Dispatch, SetStateAction } from 'react';

import axios from 'axios';
import { Icon, Intent, Spinner } from '@blueprintjs/core';
import { ObjectID } from 'mongodb';

import ElementProofList from './ElementProofList';
import proof from './ProofInterface';
import { useDispatch } from 'react-redux';

interface ProofListProps {
    addDeleteToast: (err: string) => void;
    setDialogIsOpen: Dispatch<SetStateAction<boolean>>;
}

const ProofList: React.FC<ProofListProps> = ({ addDeleteToast, setDialogIsOpen }: ProofListProps) => {
    const [proofs, setProofs] = useState([]);
    const [loadingProofs, setLoadingProofs] = useState(true);
    const [error, setError] = useState(false);
    const dispatch = useDispatch();

    const setDot = (dot: string | undefined) => {
        dispatch({ type: 'SET_DOT', payload: dot });
        setDialogIsOpen(false);
    };

    useEffect(() => {
        axios
            .get('http://localhost:5000/proof/')
            .then((response) => {
                setProofs(response.data.reverse());
                setLoadingProofs(false);
            })
            .catch(() => {
                setError(true);
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
            {error ? (
                <div style={{ textAlign: 'center', height: '200px', paddingTop: 50 }}>
                    <Icon icon="error" intent={Intent.DANGER} iconSize={40}></Icon>
                    <br></br>
                    <br></br>
                    <p>It looks like we are facing some issues, please contact the developers.</p>
                </div>
            ) : loadingProofs ? (
                <div style={{ height: '200px', paddingTop: '50px' }}>
                    <Spinner size={30} />
                </div>
            ) : (
                <div>
                    {proofs.map((proof, i) => (
                        <ElementProofList key={i} proof={proof} deleteProof={deleteProof} setDot={setDot} />
                    ))}
                </div>
            )}
        </>
    );
};

export default ProofList;
