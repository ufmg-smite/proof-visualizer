import React from 'react';
import { FormGroup, InputGroup, TextArea } from '@blueprintjs/core';

const FormNewProof: React.FC = () => {
    return (
        <>
            <FormGroup label="Proof name" labelFor="text-input" labelInfo="(required)">
                <InputGroup id="text-input" placeholder="proof-a-and-not-a" autoFocus={true} />
            </FormGroup>
            <FormGroup
                label="CVC4 Options"
                helperText="Default options: --proof --dump-proof --proof-format-mode=dot"
                labelFor="text-input"
                labelInfo="(optional)"
            >
                <InputGroup id="text-input" placeholder="--simplification=none --dag-thresh=0" />
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
                />
            </FormGroup>
        </>
    );
};

export default FormNewProof;
