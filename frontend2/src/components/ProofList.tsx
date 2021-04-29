import React, { useState } from 'react';

import { Spinner } from '@blueprintjs/core';

import ProofElementList from './ProofElementList';

const ProofList: React.FC = () => {
    const [loadingProofList, setLoadingProofList] = useState(false);
    return (
        <>
            {loadingProofList ? (
                <Spinner size={30} />
            ) : (
                <div>
                    <ProofElementList title={'a-and-not-a'} problem={'bla ble bli'} />
                    <ProofElementList title={'a-and-not-a'} problem={'bla ble bli'} />
                    <ProofElementList title={'a-and-not-a'} problem={'bla ble bli'} />
                    <ProofElementList title={'a-and-not-a'} problem={'bla ble bli'} />
                    <ProofElementList title={'a-and-not-a'} problem={'bla ble bli'} />
                    <ProofElementList title={'a-and-not-a'} problem={'bla ble bli'} />
                    <ProofElementList title={'a-and-not-a'} problem={'bla ble bli'} />
                    <ProofElementList title={'a-and-not-a'} problem={'bla ble bli'} />
                </div>
            )}
        </>
    );
};

export default ProofList;
