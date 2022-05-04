import React, { useEffect, useRef, useState } from 'react';
import { Button, Classes } from '@blueprintjs/core';
import { selectTheoryLemmas } from '../../store/features/proof/proofSlice';
import { useAppSelector } from '../../store/hooks';

const font =
    '14px / 18px -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Oxygen, Ubuntu, Cantarell, "Open Sans", "Helvetica Neue", Icons16, sans-serif';

const VisualizerTheoryLemma: React.FC = () => {
    const theoryLemmas = useAppSelector(selectTheoryLemmas);

    return (
        <div className={Classes.DIALOG_BODY}>
            <table
                id="table-node-info-2"
                className="bp3-html-table bp3-html-table-bordered bp3-html-table-condensed bp3-html-table-striped"
                style={{ width: '100%', minWidth: '230px' }}
            >
                <thead>
                    <tr>
                        <th className="letMap-value-column">Value</th>
                    </tr>
                </thead>
                <tbody>
                    {theoryLemmas.map((tl, id) => {
                        return (
                            <tr key={id}>
                                <td style={{ width: '100%', whiteSpace: 'pre-wrap' }}>{tl}</td>
                            </tr>
                        );
                    })}
                </tbody>
            </table>
        </div>
    );
};

export default VisualizerTheoryLemma;
