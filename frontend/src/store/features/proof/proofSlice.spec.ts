import { ClusterKind } from '../../../interfaces/enum';
import { ProofState } from '../../../interfaces/interfaces';
import proofReducer, { process, applyView, changeStyle } from './proofSlice';

describe('proof reducer', () => {
    const initialState: ProofState = {
        proof: [],
        view: 'full',
        style: 'graph',
        hiddenNodes: [],
        letMap: {},
        visualInfo: {},
        clustersInfos: [],
        nodesSelected: [],
        smt: '',
        theoryLemmaMap: [],
    };

    const proofExample: ProofState = {
        proof: [
            {
                id: 0,
                conclusion: 'SCOPE((not a), a)',
                rule: '(not (and (not a) a))',
                args: '',
                children: [1],
                parents: [NaN],
                descendants: 1,
                dependencies: [],
                clusterType: ClusterKind.NONE,
            },
            {
                id: 1,
                conclusion: 'CHAIN_RESOLUTION(true, a)',
                rule: 'false',
                args: '',
                children: [2, 3],
                parents: [0],
                descendants: 2,
                dependencies: [],
                clusterType: ClusterKind.NONE,
            },
            {
                id: 2,
                conclusion: 'ASSUME(a)',
                rule: 'a',
                args: '',
                children: [],
                parents: [1],
                descendants: 0,
                dependencies: [],
                clusterType: ClusterKind.NONE,
            },
            {
                id: 3,
                conclusion: 'ASSUME((not a))',
                rule: '(not a)',
                args: '',
                children: [],
                parents: [1],
                descendants: 0,
                dependencies: [],
                clusterType: ClusterKind.NONE,
            },
        ],
        view: 'full',
        style: 'graph',
        hiddenNodes: [[2]],
        letMap: {},
        visualInfo: [],
        clustersInfos: [],
        nodesSelected: [],
        smt: '',
        theoryLemmaMap: [],
    };

    it('should handle initial state', () => {
        const result = proofReducer(undefined, { type: 'unknown' });
        expect(result).toEqual({
            proof: [],
            view: 'full',
            style: 'graph',
            hiddenNodes: [],
            letMap: {},
            theoryLemmaMap: [],
            visualInfo: {},
            nodesSelected: [],
            clustersInfos: [],
            smt: '',
        });
    });

    it('should handle process', () => {
        const actual = proofReducer(
            initialState,
            process({
                proof: 'digraph proof {\n\trankdir="BT";\n\tnode [shape=record];\n\t0 [label="{SCOPE((not a), a)|(not (and (not a) a))}", class = " basic ", comment = "{\'subProofQty\':1}" ];\n\t1 [label="{CHAIN_RESOLUTION(true, a)|false}", class = " propositional ", comment = "{\'subProofQty\':2}" ];\n\t2 [label="{ASSUME(a)|a}", comment = "{\'subProofQty\':0}"];\n\t3 [label="{ASSUME((not a))|(not a)}", comment = "{\'subProofQty\':0}"];\n\t1->0;\n\t2->1;\n\t3->1;\n}',
                fileExtension: 'dot',
            }),
        );
        expect(actual.proof).toEqual(proofExample.proof);
    });

    it('should handle apply view - full', () => {
        const actual = proofReducer(proofExample, applyView('full'));
        expect(actual.view).toEqual('full');
        expect(actual.hiddenNodes).toEqual([]);
    });

    it('should handle change style - graph', () => {
        const actual = proofReducer(proofExample, changeStyle('graph'));
        expect(actual.style).toEqual('graph');
    });

    it('should handle change style - tree', () => {
        const actual = proofReducer(proofExample, changeStyle('directory'));
        expect(actual.style).toEqual('directory');
    });
});
