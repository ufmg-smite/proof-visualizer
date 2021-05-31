import React, { useState } from 'react';
import { useSelector } from 'react-redux';

import Canvas from './canvas/VisualizerCanvas';
import { NodeInterface, stateInterface } from './interfaces';

function removeEscapedCharacters(s: string): string {
    let newS = '';
    for (let i = 0; i < s.length; i += 1) {
        if (
            !(
                s[i] === '\\' &&
                (s[i + 1] === '"' ||
                    s[i + 1] === '>' ||
                    s[i + 1] === '<' ||
                    s[i + 1] === '{' ||
                    s[i + 1] === '}' ||
                    s[i + 1] === '|')
            )
        ) {
            newS += s[i];
        }
    }

    return newS;
}

function processDot(dot: string) {
    const nodes: Array<NodeInterface> = [];
    const lines = dot
        .slice(dot.indexOf('{') + 1, dot.lastIndexOf('}') - 2)
        .replace(/(\n|\t)/gm, '')
        .split(';');
    lines.forEach((line) => {
        if (line.search('label') !== -1) {
            const id = parseInt(line.slice(0, line.indexOf('[')).trim());
            let attributes = line.slice(line.indexOf('[') + 1, line.lastIndexOf(']')).trim();

            let label = attributes.slice(attributes.search(/(?<!\\)"/) + 2);
            label = label.slice(0, label.search(/(?<!\\)"/) - 1);
            const [conclusion, rule] = label.split(/(?<!\\)\|/);

            attributes = attributes.slice(attributes.indexOf(', class = ') + ', class = '.length);
            const views = attributes
                .slice(attributes.indexOf('"') + 1, attributes.lastIndexOf('"'))
                .trim()
                .split(' ');

            if (!nodes[id]) {
                nodes[id] = {
                    id: id,
                    conclusion: '',
                    rule: '',
                    views: [],
                    children: [],
                    parent: NaN,
                    x: NaN,
                    y: NaN,
                    hideMyChildNode: NaN,
                    hided: false,
                    hidedNodes: [],
                    hidedIn: NaN,
                    positionCache: false,
                };
            }
            nodes[id].conclusion = removeEscapedCharacters(conclusion);
            nodes[id].rule = removeEscapedCharacters(rule);
            nodes[id].views = views;
        } else if (line.search('->') !== -1) {
            const [child, parent] = line.split('->').map((x) => parseInt(x.trim()));
            nodes[parent].children.push(child);
            if (!nodes[child]) {
                nodes[child] = {
                    id: child,
                    conclusion: '',
                    rule: '',
                    views: [],
                    children: [],
                    parent: parent,
                    x: NaN,
                    y: NaN,
                    hideMyChildNode: NaN,
                    hided: false,
                    hidedNodes: [],
                    hidedIn: NaN,
                    positionCache: false,
                };
            }
            nodes[child].parent = parent;
        }
    });

    return nodes;
}

const VisualizerStage: React.FC = () => {
    const dot = useSelector<stateInterface, string | undefined>((state) => state.proofReducer.proof.dot);
    const view = useSelector<stateInterface, string | undefined>((state) => state.proofReducer.proof.view);
    const proof = processDot(dot ? dot : '');
    const [focusText, setFocusText] = useState('');

    return (
        <div title={focusText}>
            {proof.length ? (
                <Canvas key={dot} view={view} proofNodes={proof} setFocusText={setFocusText}></Canvas>
            ) : null}
        </div>
    );
};

export default VisualizerStage;
