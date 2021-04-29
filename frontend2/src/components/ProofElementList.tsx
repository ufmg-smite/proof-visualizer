import React from 'react';
import { Button, ButtonGroup, Card, Elevation, Intent } from '@blueprintjs/core';
interface ProofElementList {
    title: string;
    problem: string;
}

const ProofElementList: React.FC<ProofElementList> = ({ title, problem }: ProofElementList) => {
    return (
        <Card elevation={Elevation.TWO} style={{ height: 100, marginBottom: 10, marginRight: 5 }}>
            <div style={{ float: 'left' }}>
                <p style={{ fontWeight: 'bold' }}>{title}</p>
                <p>{problem}</p>
            </div>
            <div style={{ float: 'right' }}>
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
