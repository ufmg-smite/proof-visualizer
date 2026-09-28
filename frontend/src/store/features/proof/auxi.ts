import { ClusterKind } from '../../../interfaces/enum';
import { NodeInterface, ProofState } from '../../../interfaces/interfaces';
import { DotStatement, parseDot, subgraphNodes } from './dot';

interface ClusterColorMap {
    [type: number]: string;
}

interface ProcessedDot {
    nodes: NodeInterface[];
    letMap: ProofState['letMap'];
    clusterColors: ClusterColorMap;
    subproofs: ProofState['subproofs'];
}

const clusterKinds: { [label: string]: ClusterKind } = {
    SAT: ClusterKind.SAT,
    CNF: ClusterKind.CNF,
    TL: ClusterKind.TL,
    PP: ClusterKind.PP,
    IN: ClusterKind.IN,
};

// Splits a record label into its fields and removes the escapes of record labels from each field.
// Labels are either "{conclusion|rule}", as printed by cvc5, or "{step id|conclusion|rule}".
function splitRecordLabel(label: string): string[] {
    if (label.startsWith('{') && label.endsWith('}') && label[label.length - 2] !== '\\') {
        label = label.slice(1, -1);
    }
    const fields: string[] = [];
    let field = '';
    for (let i = 0; i < label.length; i++) {
        if (label[i] === '\\' && i + 1 < label.length) {
            const next = label[++i];
            field += 'lnr'.includes(next) ? '\n' : next;
        } else if (label[i] === '|') {
            fields.push(field);
            field = '';
        } else {
            field += label[i];
        }
    }
    fields.push(field);
    return fields.map((f) => f.trim());
}

function newNode(id: number): NodeInterface {
    return {
        id: id,
        conclusion: '',
        rule: '',
        args: '',
        children: [],
        parents: [],
        descendants: 0,
        dependencies: [],
        clusterType: ClusterKind.NONE,
    };
}

export function processDot(dot: string): ProcessedDot {
    const graph = parseDot(dot);
    const nodes: NodeInterface[] = [];
    let letMap: ProofState['letMap'] = {};
    const clusterColors: ClusterColorMap = {};
    // The nodes of each subproof cluster, with the index of the enclosing one
    const clusters: { members: number[]; parent: number }[] = [];

    const proofNodeId = (id: string): number => (/^[0-9]+$/.test(id) ? Number(id) : NaN);
    const getNode = (id: number): NodeInterface => {
        if (!nodes[id]) nodes[id] = newNode(id);
        return nodes[id];
    };

    const visit = (statements: DotStatement[], cluster: number): void => {
        statements.forEach((statement) => {
            if (statement.type === 'attribute') {
                // The graph comment carries the let map
                if (cluster === -1 && statement.target === 'graph' && statement.attributes.comment) {
                    const comment = JSON.parse(statement.attributes.comment);
                    if (comment.letMap) letMap = comment.letMap;
                }
            } else if (statement.type === 'node') {
                const id = proofNodeId(statement.id);
                // Nodes without a numeric ID, such as a legend, are not part of the proof
                if (isNaN(id)) return;
                const node = getNode(id);
                const { label, comment } = statement.attributes;
                if (label !== undefined) {
                    const fields = splitRecordLabel(label);
                    const [stepId, conclusion, rule] =
                        fields.length >= 3 ? fields : ['', fields[0], fields.length > 1 ? fields[1] : ''];
                    const argsIdx = rule.indexOf(' :args ');
                    if (stepId) node.stepId = stepId;
                    node.conclusion = conclusion;
                    node.rule = argsIdx === -1 ? rule : rule.slice(0, argsIdx);
                    node.args = argsIdx === -1 ? '' : rule.slice(argsIdx + ' :args '.length);
                }
                if (comment !== undefined) {
                    const subProofQty = JSON.parse(comment).subProofQty;
                    if (subProofQty !== undefined) node.descendants = subProofQty;
                }
            } else if (statement.type === 'edge') {
                // Edges go from a premise to the step that uses it
                for (let i = 0; i + 1 < statement.chain.length; i++) {
                    statement.chain[i].forEach((from) => {
                        statement.chain[i + 1].forEach((to) => {
                            const [premise, step] = [proofNodeId(from), proofNodeId(to)];
                            if (isNaN(premise) || isNaN(step)) return;
                            getNode(step).children.push(premise);
                            getNode(premise).parents.push(step);
                        });
                    });
                }
            } else {
                const label = statement.statements.reduce(
                    (acc: string | undefined, s) =>
                        s.type === 'attribute' && s.target === 'graph' && s.attributes.label !== undefined
                            ? s.attributes.label
                            : acc,
                    undefined,
                );
                const members = subgraphNodes(statement)
                    .map(proofNodeId)
                    .filter((id) => !isNaN(id));

                // cvc5 lists the nodes of each kind of cluster (SAT, CNF, ...) in a subgraph
                if (label !== undefined && clusterKinds[label] !== undefined) {
                    const kind = clusterKinds[label];
                    members.forEach((id) => (getNode(id).clusterType = kind));
                    const color = statement.statements.reduce(
                        (acc, s) => (s.type === 'attribute' && s.attributes.bgcolor ? s.attributes.bgcolor : acc),
                        '',
                    );
                    clusterColors[kind] = color;
                    visit(statement.statements, cluster);
                }
                // Other clusters are subproofs
                else if (statement.id?.startsWith('cluster')) {
                    clusters.push({ members: members, parent: cluster });
                    visit(statement.statements, clusters.length - 1);
                } else {
                    visit(statement.statements, cluster);
                }
            }
        });
    };
    visit(graph.statements, -1);

    for (let id = 0; id < nodes.length; id++) getNode(id);

    // Nodes that are not premises of any step have NaN as their parent
    nodes.forEach((node) => {
        if (!node.parents.length) node.parents = [NaN];
    });

    // If the tree sizes were not given, compute them
    if (nodes.some((node) => !node.descendants)) {
        const sizes: number[] = [];
        const treeSize = (id: number): number => {
            if (sizes[id] === undefined) {
                sizes[id] = 1;
                sizes[id] = nodes[id].children.reduce((acc, child) => acc + treeSize(child), 1);
            }
            return sizes[id];
        };
        nodes.forEach((node) => {
            if (!node.descendants) node.descendants = treeSize(node.id);
        });
    }

    // A subproof folds into all its nodes but the steps concluding it, which are the ones that no
    // other node of the subproof uses
    const subproofs = clusters.map(({ members, parent }) => {
        const memberSet = new Set(members);
        return {
            nodes: members.filter((id) => nodes[id].parents.some((p) => memberSet.has(p))).sort((a, b) => a - b),
            parent: parent,
        };
    });

    return { nodes, letMap, clusterColors, subproofs };
}

export const piNodeParents = (
    proof: NodeInterface[],
    hiddenNodesArray: number[],
    dependencies: { [parentId: number]: number[] } = {},
): number[] => {
    const parents = hiddenNodesArray
        // Concat all the parents
        .reduce((acc: number[], hiddenNode) => {
            let haveHiddenParent = false;

            proof[hiddenNode].parents.forEach((parent) => {
                // If this parent is a hidden node
                if (hiddenNodesArray.indexOf(parent) !== -1) {
                    haveHiddenParent = true;
                } else {
                    dependencies[parent]
                        ? dependencies[parent].push(hiddenNode)
                        : (dependencies[parent] = [hiddenNode]);
                }
            });

            if (haveHiddenParent) return acc;
            return acc.concat(proof[hiddenNode].parents);
        }, [])
        // Filter the duplicated elements
        .filter((parent, i, self) => self.indexOf(parent) === i)
        // Only the parents that aren't in he hidden nodes array remains
        .filter((parent) => hiddenNodesArray.indexOf(parent) === -1);

    // Removes the pi node parents from the dependencies
    Object.keys(dependencies).forEach((parent) => {
        const n = Number(parent);
        if (parents.indexOf(n) !== -1) delete dependencies[n];
    });

    return parents;
};

export const descendants = (proof: NodeInterface[], nodeId: number): number[] => {
    const validChildren = proof[nodeId].children.filter((node) => !proof[node].isHidden);
    return validChildren.concat(
        validChildren.reduce((acc: number[], childId) => {
            return acc.concat(descendants(proof, childId));
        }, []),
    );
};

export const piNodeChildren = (proof: NodeInterface[], hiddenNodesArray: number[]): number[] => {
    const children = hiddenNodesArray
        // Get all the childrens
        .reduce((acc: number[], hiddenNode) => acc.concat(proof[hiddenNode].children), [])
        // Exclude the childrens that are part of the hidden nodes
        .filter((child) => hiddenNodesArray.indexOf(child) === -1);
    return children;
};

export const findNodesClusters = (proof: NodeInterface[], hiddenNodesArray: number[]): number[][] => {
    const hiddenNodes = [...hiddenNodesArray];
    const clusters: number[][] = [];
    let clusteredNodes = 0;
    const parents = hiddenNodes.map((hiddenNode) => proof[hiddenNode].parents);

    // Cluster the nodes based on similiar parents
    parents.forEach((parent, clusterID) => {
        // If not all of the nodes where clustered and is a non empty cluster
        if (clusteredNodes !== parents.length && parents[clusterID].length) {
            clusters.push([]);
            parents.forEach((p, hiddenID) => {
                // If those nodes have some parent in commom and they weren't verified yet
                if (parents[hiddenID].length && parent.some((_p) => p.indexOf(_p) !== -1)) {
                    if (hiddenNodes[hiddenID]) clusters[clusters.length - 1].push(hiddenNodes[hiddenID]);
                    // Removes these parents from the array, making shure they will not get verified again (already clustered)
                    parents[hiddenID] = [];
                    // Increases the number o clustered nodes
                    clusteredNodes++;
                }
            });
        }
    });

    let pastCluster: number[][] = [];
    // Cluster the nodes until there aren't changes being made
    while (JSON.stringify(pastCluster) != JSON.stringify(clusters)) {
        pastCluster = [...clusters];
        clusters.forEach((cluster, clusterID) => {
            const clusterParents = proof[cluster[0]].parents;

            // For each cluster
            clusters.forEach((parentCluster, id) => {
                // If this parentCluster (cluster) is parent of the current cluster
                if (parentCluster.some((hiddenID) => clusterParents.indexOf(hiddenID) !== -1)) {
                    // Group the nodes couple in one single cluster (the parent cluster)
                    if (clusters[clusterID]) clusters[id] = clusters[id].concat(clusters[clusterID]);
                    clusters.splice(clusterID, 1);
                    clusterID--;
                }
            });
        });
    }

    // Filter the nodes with length 1
    return clusters.filter((cluster) => cluster.length > 1);
};

export const groupPiNodeDependencies = (
    proof: NodeInterface[],
    hiddenNodesArray: number[],
): NodeInterface['dependencies'] => {
    const piNodeDependencies: NodeInterface['dependencies'] = [];
    const depMap: { [piID: number]: number } = {};

    // Copy all the hidden nodes dependencies to the new pi node
    proof.forEach((node) => {
        // Search for all the hidden nodes that have deps
        if (hiddenNodesArray.indexOf(node.id) !== -1 && node.dependencies.length) {
            // For each dependence in this node
            node.dependencies.forEach((dep) => {
                // This pi node dependence wasn't inserted yet
                if (Object.keys(depMap).indexOf(String(dep.piId)) === -1) {
                    piNodeDependencies.push(dep);
                    depMap[dep.piId] = piNodeDependencies.length - 1;
                }
                // Concat the nodes inside the pi node already inserted
                else {
                    piNodeDependencies[depMap[dep.piId]].depsId = piNodeDependencies[depMap[dep.piId]].depsId.concat(
                        dep.depsId,
                    );
                }
            });
        }
    });
    return piNodeDependencies;
};

export const sliceNodesCluster = (
    proof: NodeInterface[],
    clusterMap: number[],
    nodeId = 0,
    slicedClusters: number[][] = [],
): number[][] => {
    const currentNode = proof[nodeId];

    // If the node id is valid and wasn't inserted yet
    if (nodeId && clusterMap[currentNode.id] === -1) {
        // Get all parents with the same type
        const parentsClusters: { [parentID: number]: number } = {};
        for (let i = 0; i < currentNode.parents.length; i++) {
            const p = currentNode.parents[i];
            if (proof[p].clusterType === currentNode.clusterType) {
                parentsClusters[p] = clusterMap[p];
                break;
            }
        }

        const keys = Object.keys(parentsClusters);

        // If the current node has the same type as (at least) one of it's parents
        if (keys.length) {
            // Put the current node in the cluster of the first parent with the same type
            const target = parentsClusters[Number(keys[0])];
            slicedClusters[target].push(currentNode.id);
            clusterMap[currentNode.id] = target;
        }
        // Parent with different type
        else {
            const clusterID = slicedClusters.length;
            clusterMap[currentNode.id] = clusterID;
            slicedClusters.push([currentNode.id]);

            // Add the brothers with the same type in the same cluster
            proof[currentNode.parents[0]].children.forEach((c) => {
                // If the brother node has the same type as the current one
                if (proof[c].clusterType === currentNode.clusterType && c !== currentNode.id) {
                    slicedClusters[clusterID].push(c);
                    clusterMap[c] = clusterID;
                }
            });
        }
    }

    currentNode.children.forEach((child) => {
        sliceNodesCluster(proof, clusterMap, child, slicedClusters);
    });
    return slicedClusters;
};

export const extractTheoryLemmas = (
    proof: NodeInterface[],
    clusters: ProofState['clustersInfos'],
    haveCluster: boolean,
): ProofState['theoryLemmaMap'] => {
    // If have clusters registered
    if (haveCluster) {
        return [proof[0].conclusion].concat(
            clusters.filter((c) => c.type === ClusterKind.TL).map((c) => proof[c.hiddenNodes[0]].conclusion),
        );
    } else {
        return proof.filter((n) => n.rule === 'SCOPE').map((n) => n.conclusion);
    }
};
