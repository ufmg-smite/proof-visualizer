import React, { useState } from 'react';
import { useSelector } from 'react-redux';

import { Icon, Collapse, Pre, TreeNodeInfo } from '@blueprintjs/core';
import { VisualizerTree } from './VisualizerTree';

import { stateInterface } from './interfaces';

const VisualizerFolderStyle: React.FC<{ proofTree: TreeNodeInfo[]; ruleHelper: (s: string) => string }> = ({
    proofTree,
    ruleHelper,
}: {
    proofTree: TreeNodeInfo[];
    ruleHelper: (s: string) => string;
}) => {
    const darkTheme = useSelector<stateInterface, boolean>((state: stateInterface) => state.darkThemeReducer.darkTheme);
    const [ruleHelperOpen, setRuleHelperOpen] = useState(false);
    const [nodeInfo, setNodeInfo] = useState<{
        rule: string;
        args: string;
        conclusion: string;
        nHided: number;
        nDescendants: number;
        topHidedNodes?: Array<[number, string, string, number, number]>;
    }>({
        rule: '',
        args: '',
        conclusion: '',
        nHided: 0,
        nDescendants: 0,
        topHidedNodes: undefined,
    });

    return (
        <div
            style={{
                backgroundColor: darkTheme ? 'rgb(57, 75, 89)' : 'white',
                height:
                    window.innerHeight - (document.getElementsByClassName('bp3-navbar')[0] as HTMLElement).offsetHeight,
            }}
        >
            <div
                style={{
                    width: '50%',
                    height: '100%',
                    float: 'left',
                    clear: 'none',
                    borderRight: '1px solid black',
                    overflow: 'auto',
                }}
            >
                <VisualizerTree
                    darkTheme={darkTheme}
                    content={proofTree}
                    setNodeInfo={setNodeInfo}
                    originalNodeInfo={{
                        rule: '',
                        args: '',
                        conclusion: '',
                        nHided: 0,
                        nDescendants: 0,
                        topHidedNodes: undefined,
                    }}
                ></VisualizerTree>
            </div>
            <div
                style={{
                    width: '50%',
                    height: '100%',
                    float: 'left',
                    clear: 'none',
                }}
            >
                <table
                    id="table-node-info"
                    className="bp3-html-table bp3-html-table-bordered bp3-html-table-condensed bp3-html-table-striped"
                    style={{ width: '100%' }}
                >
                    <thead>
                        <tr>
                            <th>Property</th>
                            <th>Value</th>
                        </tr>
                    </thead>
                    <tbody>
                        <tr>
                            <td>
                                <strong>RULE </strong>{' '}
                                <Icon
                                    id="rule-icon"
                                    icon="help"
                                    onClick={() => setRuleHelperOpen(!ruleHelperOpen)}
                                ></Icon>
                            </td>
                            <td>
                                {nodeInfo.rule}
                                <Collapse isOpen={ruleHelperOpen}>
                                    <Pre id="pre-rule">{ruleHelper(nodeInfo.rule)}</Pre>
                                </Collapse>
                            </td>
                        </tr>
                        {nodeInfo.args ? (
                            <tr>
                                <td>
                                    <strong>ARGS</strong>
                                </td>
                                <td>{nodeInfo.args}</td>
                            </tr>
                        ) : null}
                        <tr>
                            <td>
                                <strong>CONCLUSION</strong>
                            </td>
                            <td>{nodeInfo.conclusion}</td>
                        </tr>
                        {!nodeInfo.topHidedNodes ? (
                            <tr>
                                <td>
                                    <strong>#DESCENDANTS</strong>
                                </td>
                                <td>{nodeInfo.nDescendants}</td>
                            </tr>
                        ) : (
                            <tr>
                                <td>
                                    <strong>#DESCENDANTS</strong>
                                </td>
                                <td>[{nodeInfo.topHidedNodes.map((node) => node[3]).join(', ')}]</td>
                            </tr>
                        )}
                        {nodeInfo.nHided ? (
                            <tr>
                                <td>
                                    <strong>#HIDDEN</strong>
                                </td>
                                <td>
                                    [
                                    {nodeInfo.topHidedNodes
                                        ? nodeInfo.topHidedNodes.map((node) => node[4]).join(', ')
                                        : ''}
                                    ]
                                </td>
                            </tr>
                        ) : null}
                    </tbody>
                </table>
            </div>
        </div>
    );
};

export default VisualizerFolderStyle;
