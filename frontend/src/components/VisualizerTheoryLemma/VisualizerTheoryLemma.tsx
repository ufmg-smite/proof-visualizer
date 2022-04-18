import React, { useEffect, useRef, useState } from 'react';
import { Button, Classes } from '@blueprintjs/core';

const font =
    '14px / 18px -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Oxygen, Ubuntu, Cantarell, "Open Sans", "Helvetica Neue", Icons16, sans-serif';

const VisualizerTheoryLemma: React.FC = () => {
    const TheoryLemmas = [1, 2];
    return (
        <div className={Classes.DRAWER_BODY}>
            <div className={Classes.DIALOG_BODY}>
                <table
                    id="table-node-info"
                    className="bp3-html-table bp3-html-table-bordered bp3-html-table-condensed bp3-html-table-striped"
                    style={{ width: '100%' }}
                >
                    <thead>
                        <tr>
                            <th style={{ width: '100px' }}>Property</th>
                            <th className="letMap-value-column">Value</th>
                            <th style={{ width: '250px' }}>Action</th>
                        </tr>
                    </thead>
                    <tbody>
                        {TheoryLemmas.map((tl) => {
                            return (
                                <tr key={tl}>
                                    <td>
                                        <strong>{tl}</strong>
                                    </td>
                                    <td style={{ width: '100%', whiteSpace: 'pre-wrap' }}>{null}</td>
                                    <td style={{ width: '150px', height: '100%' }}>
                                        <Button
                                            onClick={() => null}
                                            className="bp3-minimal"
                                            icon="translate"
                                            text="Expand"
                                        />
                                        <Button
                                            onClick={() => null}
                                            className="bp3-minimal"
                                            icon="undo"
                                            text="Revert"
                                        />
                                    </td>
                                </tr>
                            );
                        })}
                    </tbody>
                </table>
            </div>
        </div>
    );
};

export default VisualizerTheoryLemma;