import React, { useState } from 'react';

import { Icon, Collapse, Pre, TreeNodeInfo } from '@blueprintjs/core';
import VisualizerTree from '../../VisualizerTree/VisualizerTree';

import '../../../scss/VisualizerDirectoryStyle.scss';
import { useAppSelector } from '../../../store/hooks';
import { selectTheme } from '../../../store/features/theme/themeSlice';
import { NodeInfo } from '../../../interfaces/interfaces';

interface directoryStyleProps {
    proofTree: TreeNodeInfo[];
    ruleHelper: (s: string) => string;
    indent: (s: string) => string;
    translate: (s: string) => string;
}

const VisualizerDirectoryStyle: React.FC<directoryStyleProps> = ({
    proofTree,
    ruleHelper,
    indent,
    translate,
}: directoryStyleProps) => {
    const darkTheme = useAppSelector(selectTheme);
    const [ruleHelperOpen, setRuleHelperOpen] = useState(false);
    const [argsTranslatorOpen, setArgsTranslatorOpen] = useState(false);
    const [conclusionTranslatorOpen, setConclusionTranslatorOpen] = useState(false);
    const [nodeInfo, setNodeInfo] = useState<NodeInfo>({
        rule: '',
        args: '',
        conclusion: '',
        nHided: 0,
        nDescendants: 0,
        hiddenNodes: [],
        dependencies: [],
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
                        hiddenNodes: [],
                        dependencies: [],
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
                                <strong>RULE </strong>
                                <Icon
                                    id="rule-icon"
                                    icon="help"
                                    onClick={() => {
                                        setArgsTranslatorOpen(false);
                                        setConclusionTranslatorOpen(false);
                                        setRuleHelperOpen(!ruleHelperOpen);
                                    }}
                                ></Icon>
                            </td>
                            <td>
                                {nodeInfo.rule}
                                <Collapse isOpen={ruleHelperOpen}>
                                    <Pre style={{ maxHeight: '300px', overflow: 'auto' }} id="pre-rule">
                                        {ruleHelper(nodeInfo.rule)}
                                    </Pre>
                                </Collapse>
                            </td>
                        </tr>

                        {nodeInfo.args && (
                            <tr>
                                <td>
                                    <strong>ARGS</strong>{' '}
                                    {nodeInfo.args.indexOf('let') !== -1 ? (
                                        <Icon
                                            id="rule-icon"
                                            icon="translate"
                                            onClick={() => {
                                                setConclusionTranslatorOpen(false);
                                                setRuleHelperOpen(false);
                                                setArgsTranslatorOpen(!argsTranslatorOpen);
                                            }}
                                        ></Icon>
                                    ) : null}
                                </td>
                                <td style={{ maxHeight: '300px', overflow: 'auto' }}>
                                    {nodeInfo.args}
                                    {nodeInfo.args.indexOf('let') !== -1 ? (
                                        <Collapse isOpen={argsTranslatorOpen}>
                                            <Pre style={{ maxHeight: '300px', overflow: 'auto' }} id="pre-rule">
                                                {indent(translate(nodeInfo.args))}
                                            </Pre>
                                        </Collapse>
                                    ) : null}
                                </td>
                            </tr>
                        )}

                        <tr>
                            <td style={{ maxHeight: '300px', overflow: 'auto' }}>
                                <strong>CONCLUSION</strong>{' '}
                                {nodeInfo.conclusion.indexOf('let') !== -1 ? (
                                    <Icon
                                        id="rule-icon"
                                        icon="translate"
                                        onClick={() => {
                                            setArgsTranslatorOpen(false);
                                            setRuleHelperOpen(false);
                                            setConclusionTranslatorOpen(!conclusionTranslatorOpen);
                                        }}
                                    ></Icon>
                                ) : null}
                            </td>
                            <td style={{ maxHeight: '300px', overflow: 'auto' }}>
                                {nodeInfo.conclusion}
                                {nodeInfo.conclusion.indexOf('let') !== -1 ? (
                                    <Collapse isOpen={conclusionTranslatorOpen}>
                                        <Pre style={{ maxHeight: '300px', overflow: 'auto' }} id="pre-rule">
                                            {indent(translate(nodeInfo.conclusion))}
                                        </Pre>
                                    </Collapse>
                                ) : null}
                            </td>
                        </tr>

                        {nodeInfo.nDescendants ? (
                            <tr>
                                <td>
                                    <strong>#DESCENDANTS</strong>
                                </td>
                                <td>{nodeInfo.nDescendants}</td>
                            </tr>
                        ) : null}

                        {nodeInfo.nHided ? (
                            <tr>
                                <td>
                                    <strong>#HIDDEN</strong>
                                </td>
                                <td>{`[${nodeInfo.hiddenNodes.map((node) => ' ' + node)} ]`}</td>
                            </tr>
                        ) : null}
                    </tbody>
                </table>
            </div>
        </div>
    );
};

export default VisualizerDirectoryStyle;
