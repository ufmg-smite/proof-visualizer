import React from 'react';

import { Button, ButtonGroup, Card, Elevation, Intent } from '@blueprintjs/core';

import '../scss/ProofElementList.scss';

interface ProofElementList {
    title: string;
    problem: string;
}

const ProofElementList: React.FC<ProofElementList> = ({ title, problem }: ProofElementList) => {
    return (
        <Card className="proof-element-card" elevation={Elevation.TWO}>
            <div className="left">
                <p className="title">{title}</p>
                <p>{problem}</p>
            </div>

            <div className="right">
                <ButtonGroup>
                    <Button icon="diagram-tree" intent={Intent.PRIMARY}>
                        Show
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
