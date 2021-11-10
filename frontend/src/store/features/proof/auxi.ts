import { NodeInterface } from '../../../interfaces/interfaces';

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

export function processDot(dot: string): [NodeInterface[], any] {
    const nodes: Array<NodeInterface> = [
        {
            id: 0,
            conclusion: '',
            rule: '',
            args: '',
            views: [],
            children: [],
            parents: [NaN],
            descendants: 0,
        },
    ];
    let comment: any = dot.slice(dot.indexOf('comment='));
    comment = comment
        ? removeEscapedCharacters(
              removeEscapedCharacters(comment.slice(comment.indexOf('=') + 2, comment.indexOf(';') - 1)),
          )
        : null;

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
            let [conclusion, rule, args] = ['', '', ''];
            [conclusion, rule] = label.split(/(?<!\\)\|/);
            [rule, args] = rule.indexOf(':args') != -1 ? rule.split(':args') : [rule, ''];

            attributes = attributes.slice(attributes.indexOf(', class = ') + ', class = '.length);
            attributes = attributes.slice(attributes.indexOf('"') + 1, attributes.slice(1).indexOf('"') + 1);
            const views = attributes.trim().split(' ');
            const comment: string = removeEscapedCharacters(line.slice(line.indexOf('comment'), line.lastIndexOf('"')));
            const commentJSON = JSON.parse(comment.slice(comment.indexOf('"') + 1).replace(/'/g, '"'));

            if (!nodes[id]) {
                nodes[id] = {
                    id: id,
                    conclusion: '',
                    rule: '',
                    args: '',
                    views: [],
                    children: [],
                    parents: [NaN],
                    descendants: 0,
                };
            }
            nodes[id].conclusion = removeEscapedCharacters(conclusion);
            nodes[id].rule = removeEscapedCharacters(rule);
            nodes[id].args = removeEscapedCharacters(args);
            nodes[id].views = views;
            nodes[id].descendants = commentJSON.subProofQty;
        } else if (line.search('->') !== -1) {
            const [child, parent] = line.split('->').map((x) => parseInt(x.trim()));
            nodes[parent].children.push(child);
            if (!nodes[child]) {
                nodes[child] = {
                    id: child,
                    conclusion: '',
                    rule: '',
                    args: '',
                    views: [],
                    children: [],
                    parents: [parent],
                    descendants: 0,
                };
            }
            nodes[child].parents = [parent];
        }
    });
    return comment ? [nodes, JSON.parse(comment)['letMap']] : [nodes, {}];
}

const ancestors = (proof: NodeInterface[], nodeId: number): number[] => {
    if (!isNaN(nodeId)) {
        return proof[nodeId].parents.concat(
            proof[nodeId].parents.reduce((acc: number[], parentId) => acc.concat(ancestors(proof, parentId)), []),
        );
    }
    return [];
};

export const piNodeParents = (proof: NodeInterface[], hiddenNodesArray: number[]): number[] => {
    const parents = hiddenNodesArray.reduce((acc: number[], hiddenNode) => acc.concat(proof[hiddenNode].parents), []);
    return parents.filter((nodeId) => !ancestors(proof, nodeId).some((ancestor) => parents.includes(ancestor)));
};

export const descendants = (proof: NodeInterface[], nodeId: number): number[] => {
    return proof[nodeId].children.concat(
        proof[nodeId].children.reduce((acc: number[], childId) => acc.concat(descendants(proof, childId)), []),
    );
};

export const piNodeChildren = (proof: NodeInterface[], hiddenNodesArray: number[]): number[] => {
    const children = hiddenNodesArray.reduce((acc: number[], hiddenNode) => acc.concat(proof[hiddenNode].children), []);
    return children.filter((nodeId) => !descendants(proof, nodeId).some((descendant) => children.includes(descendant)));
};
