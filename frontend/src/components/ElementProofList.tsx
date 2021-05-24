import React from 'react';

import { Button, ButtonGroup, Card, Elevation, Intent } from '@blueprintjs/core';

import '../scss/ElementProofList.scss';
import { ElementProofListProps } from './interfaces';

const ElementProofList: React.FC<ElementProofListProps> = ({ proof, deleteProof, setDot }: ElementProofListProps) => {
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
                    <Button
                        onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                            e.preventDefault();
                            setDot(proof);
                        }}
                        icon="diagram-tree"
                        intent={Intent.PRIMARY}
                    >
                        Visualize
                    </Button>

                    <Button
                        onClick={(e: React.MouseEvent<HTMLElement, MouseEvent>) => {
                            e.preventDefault();
                            deleteProof(proof._id, proof.label);
                        }}
                        icon="delete"
                        intent={Intent.DANGER}
                    >
                        Delete
                    </Button>
                </ButtonGroup>
            </div>
        </Card>
    );
};

export default ElementProofList;
