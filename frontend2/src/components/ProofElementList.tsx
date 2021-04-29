import React from 'react';

import { Button, ButtonGroup, Card, Elevation, Intent } from '@blueprintjs/core';

import '../scss/ProofElementList.scss';

interface proof {
    label: string;
    problem: string;
}

interface ProofElementList {
    proof: proof;
}

const ProofElementList: React.FC<ProofElementList> = ({ proof }: ProofElementList) => {
    return (
        <Card className="proof-element-card" elevation={Elevation.TWO}>
            <div className="left">
                <p className="title" title={proof.label}>
                    {proof.label.slice(0, 35) + (proof.label.length > 35 ? '...' : '')}
                </p>
                <p title={proof.problem}>{proof.problem.slice(0, 35) + (proof.problem.length > 35 ? '...' : '')}</p>
            </div>

            <div className="right">
                <ButtonGroup vertical={true}>
                    <Button icon="diagram-tree" intent={Intent.PRIMARY}>
                        Visualize
                    </Button>

                    <Button icon="delete" intent={Intent.DANGER}>
                        Delete
                    </Button>
                </ButtonGroup>
            </div>
        </Card>
    );
};

export default ProofElementList;
