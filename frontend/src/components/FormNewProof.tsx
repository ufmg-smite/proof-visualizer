import React, { Dispatch, SetStateAction, useEffect, useState } from 'react';

import { FormGroup, InputGroup, TextArea } from '@blueprintjs/core';

interface proof {
    name: string;
    options: string;
    problem: string;
}

interface FormNewProofProps {
    proof: proof;
    setProof: Dispatch<SetStateAction<proof>>;
}

const FormNewProof: React.FC<FormNewProofProps> = ({ proof, setProof }: FormNewProofProps) => {
    const [name, setName] = useState(proof.name);
    const [options, setOptions] = useState(proof.options);
    const [problem, setProblem] = useState(proof.problem);

    useEffect(() => {
        setProof({
            name,
            options,
            problem,
        });
    }, [name, options, problem]);

    return (
        <>
            <FormGroup label="Proof name" labelFor="text-input" labelInfo="(required)">
                <InputGroup
                    placeholder="proof-a-and-not-a"
                    autoFocus={true}
                    value={name}
                    onChange={(e) => setName(e.target.value)}
                />
            </FormGroup>

            <FormGroup
                label="CVC4 Options"
                helperText="Default options: --proof --dump-proof --proof-format-mode=dot"
                labelFor="text-input"
                labelInfo="(optional)"
            >
                <InputGroup
                    placeholder="--simplification=none --dag-thresh=0"
                    value={options}
                    onChange={(e) => setOptions(e.target.value)}
                />
            </FormGroup>

            <FormGroup label="Problem" labelFor="text-area" labelInfo="(required)">
                <TextArea
                    className="bp3-fill"
                    growVertically={true}
                    large={true}
                    placeholder="(set-logic QF_UF)
(declare-fun a () Bool)
(assert (not a))
(assert a)
(check-sat)"
                    value={problem}
                    onChange={(e) => setProblem(e.target.value)}
                />
            </FormGroup>
        </>
    );
};

export default FormNewProof;
