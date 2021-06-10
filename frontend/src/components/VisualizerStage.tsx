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

function ruleHelper(rule: string) {
    switch (rule.split(' ')[0]) {
        case 'π':
            return 'This node hides some parts of the proof, you can left-click to unfold it.';
        case 'ASSUME':
            return (
                rule +
                '\n\n======== Assumption (a leaf)\nChildren: none\nArguments: (F)\n--------------\nConclusion: F\n\nThis rule has special status, in that an application of assume is an open leaf in a proof that is not (yet) justified. An assume leaf is analogous to a free variable in a term, where we say "F is a free assumption in proof P" if it contains an application of F that is not  bound by SCOPE.'
            );
        case 'SCOPE':
            return (
                rule +
                '\n\n======== Scope (a binder for assumptions)\nChildren: (P:F)\nArguments: (F1, ..., Fn)\n--------------\nConclusion: (=> (and F1 ... Fn) F) or (not (and F1 ... Fn)) if F is false\n\nThis rule has a dual purpose with ASSUME. It is a way to close assumptions in a proof. We require that F1 ... Fn are free assumptions in P and say that F1, ..., Fn are not free in (SCOPE P). In other words, they are bound by this application. For example, the proof node: (SCOPE (ASSUME F) :args F) has the conclusion (=> F F) and has no free assumptions. More generally, a proof with no free assumptions always concludes a valid formula.'
            );
        case 'SUBS':
            return (
                rule +
                '\n\n======== Substitution\nChildren: (P1:F1, ..., Pn:Fn)\nArguments: (t, (ids)?)\n---------------------------------------------------------------\nConclusion: (= t t*sigma{ids}(Fn)*...*sigma{ids}(F1)) where sigma{ids}(Fi) are substitutions, which notice are applied in reverse order. Notice that ids is a MethodId identifier, which determines how to convert the formulas F1, ..., Fn into substitutions.'
            );
        case 'REWRITE':
            return (
                rule +
                '\n\n======== Rewrite\nChildren: none\nArguments: (t, (idr)?)\n----------------------------------------\nConclusion: (= t Rewriter{idr}(t)) where idr is a MethodId identifier, which determines the kind of rewriter to apply, e.g. Rewriter::rewrite.'
            );
        case 'EVALUATE':
            return (
                rule +
                '\n\n======== Evaluate\nChildren: none\n\nArguments: (t)\n----------------------------------------\nConclusion: (= t Evaluator::evaluate(t))\nNote this is equivalent to: (REWRITE t MethodId::RW_EVALUATE)'
            );
        case 'MACRO_SR_EQ_INTRO':
            return (
                rule +
                "\n\nIn this rule, we provide a term t and conclude that it is equal to its rewritten form under a (proven) substitution.\n\nChildren: (P1:F1, ..., Pn:Fn)\nArguments: (t, (ids (ida (idr)?)?)?)\n---------------------------------------------------------------\nConclusion: (= t t') where t' is Rewriter{idr}(t*sigma{ids, ida}(Fn)*...*sigma{ids, ida}(F1))\n\nIn other words, from the point of view of Skolem forms, this rule transforms t to t' by standard substitution + rewriting.\n\nThe arguments ids, ida and idr are optional and specify the identifier of the substitution, the substitution application and rewriter respectively to be used."
            );
        case 'MACRO_SR_PRED_INTRO':
            return (
                rule +
                "\n\nIn this rule, we provide a formula F and conclude it, under the condition that it rewrites to true under a proven substitution.\n\nChildren: (P1:F1, ..., Pn:Fn)\nArguments: (F, (ids (ida (idr)?)?)?)\n---------------------------------------------------------------\nConclusion: F where Rewriter{idr}(F*sigma{ids, ida}(Fn)*...*sigma{ids, ida}(F1)) == true where ids and idr are method identifiers.\n\nMore generally, this rule also holds when: Rewriter::rewrite(toOriginal(F')) == true where F' is the result of the left hand side of the equality above. Here, notice that we apply rewriting on the original form of F', meaning that this rule may conclude an F whose Skolem form is justified by the definition of its (fresh) Skolem variables. For example, this rule may justify the conclusion (= k t) where k is the purification Skolem for t, e.g. where the original form of k is t.\n\nFurthermore, notice that the rewriting and substitution is applied only within the side condition, meaning the rewritten form of the original form of F does not escape this rule."
            );
        default:
            return rule;
    }
}

const VisualizerStage: React.FC = () => {
    const dot = useSelector<stateInterface, string | undefined>((state) => state.proofReducer.proof.dot);
    const view = useSelector<stateInterface, string | undefined>((state) => state.proofReducer.proof.view);
    const proof = processDot(dot ? dot : '');
    const [focusText, setFocusText] = useState('');

    return (
        <div title={ruleHelper(focusText)}>
            {proof.length ? (
                <Canvas key={dot} view={view} proofNodes={proof} setFocusText={setFocusText}></Canvas>
            ) : null}
        </div>
    );
};

export default VisualizerStage;
