import { configureStore } from '@reduxjs/toolkit';
import proofReducer, { process, selectProof, unfoldNodes, undo, applyView } from './proofSlice';
import { processDot } from './auxi';
import { parseDot } from './dot';
import { findLets } from '../../../components/VisualizerLetDrawer/let';
import { RootState } from '../../store';
import examples from '../../../examples/proofs-examples';

// Printed by `carcara dot` for a proof with a subproof (t1) nested in another (t1.t1)
const nestedDot = String.raw`digraph proof {
	rankdir="BT";
	node [shape=record];
	comment="{\"letMap\" : {\"k\" : \"(or (not p) p)\"}}";
	definitions [ shape = Mrecord, label = "{k := (or (not p) p)\l}" ];
	7 [ label = "{a0|(not k)|ASSUME}", comment = "{\"subProofQty\":1}" ];
	subgraph cluster_0 {
		style=dashed;
		6 [ label = "{t1.a0|q|ASSUME}", comment = "{\"subProofQty\":1}" ];
		subgraph cluster_1 {
			style=dashed;
			5 [ label = "{t1.t1.a0|p|ASSUME}", comment = "{\"subProofQty\":1}" ];
			4 [ label = "{t1.t1.t1|p|reordering}", comment = "{\"subProofQty\":2}" ];
			3 [ label = "{t1.t1|(cl (not p) p)|subproof}", comment = "{\"subProofQty\":4}" ];
		}
		2 [ label = "{t1|(cl (not q) (not p) p)|subproof}", comment = "{\"subProofQty\":6}" ];
	}
	1 [ label = "{t2|(cl (not q) k)|resolution :args [ \"x\\y\", (=\> p q) ]}", comment = "{\"subProofQty\":7}" ];
	0 [ label = "{t3|(cl)|resolution}", comment = "{\"subProofQty\":9}" ];
	5 -> 4;
	5 -> 3;
	4 -> 3;
	6 -> 2;
	3 -> 2;
	2 -> 1;
	1 -> 0;
	7 -> 0;
}
`;

const newStore = () => configureStore({ reducer: { proof: proofReducer } });
const hiddenNodes = (store: ReturnType<typeof newStore>) => store.getState().proof.hiddenNodes;
const visibleSteps = (store: ReturnType<typeof newStore>) =>
    selectProof(store.getState() as RootState).map((node) => (node.stepId ? node.stepId : node.rule));

describe('parseDot', () => {
    it('parses statements, attributes and nested subgraphs', () => {
        const graph = parseDot('unsat\ndigraph g { a [x="1\\"2", y=3]; b -> c -> {d e}; subgraph s { f } // c\n }');
        expect(graph.directed).toBe(true);
        expect(graph.statements[0]).toEqual({ type: 'node', id: 'a', attributes: { x: '1"2', y: '3' } });
        expect(graph.statements[1]).toMatchObject({ type: 'subgraph' });
        expect(graph.statements[2]).toEqual({
            type: 'subgraph',
            id: 's',
            statements: [{ type: 'node', id: 'f', attributes: {} }],
        });
    });
});

describe('processDot', () => {
    it('reads step ids, rules, arguments and the let map', () => {
        const { nodes, letMap } = processDot(nestedDot);
        expect(nodes.length).toBe(8);
        expect(letMap).toEqual({ k: '(or (not p) p)' });
        expect(nodes[0]).toMatchObject({ stepId: 't3', conclusion: '(cl)', rule: 'resolution', descendants: 9 });
        expect(nodes[0].parents[0]).toBeNaN();
        expect(nodes[1]).toMatchObject({
            stepId: 't2',
            conclusion: '(cl (not q) k)',
            rule: 'resolution',
            args: '[ "x\\y", (=> p q) ]',
        });
        expect(nodes[2].children).toEqual([6, 3]);
    });

    it('finds the subproofs, without the steps that conclude them', () => {
        const { subproofs } = processDot(nestedDot);
        expect(subproofs).toEqual([
            { nodes: [3, 4, 5, 6], parent: -1 },
            { nodes: [4, 5], parent: 0 },
        ]);
    });

    it('reads cvc5 proofs as before', () => {
        const { nodes, letMap, clusterColors, subproofs } = processDot(examples.ex2.dot);
        expect(nodes.length).toBe(20);
        expect(nodes[0]).toMatchObject({
            conclusion: '(not (and let7 let6 let5 let3))',
            rule: 'SCOPE',
            args: '[ let7, let6, let5, let3 ]',
            descendants: 20,
        });
        expect(nodes[0].stepId).toBeUndefined();
        expect(Object.keys(letMap).length).toBe(9);
        expect(Object.keys(clusterColors).length).toBe(5);
        expect(subproofs).toEqual([]);
    });
});

describe('subproof folding', () => {
    it('starts with the outermost subproofs folded', () => {
        const store = newStore();
        store.dispatch(process(nestedDot));
        expect(store.getState().proof.view).toBe('clustered');
        expect(hiddenNodes(store)).toEqual([[3, 4, 5, 6]]);
        expect(visibleSteps(store)).toEqual(['t3', 't2', 't1', 'a0', '[ subproof, ASSUME ]']);
    });

    it('keeps inner subproofs folded when unfolding, and undoes it', () => {
        const store = newStore();
        store.dispatch(process(nestedDot));
        store.dispatch(unfoldNodes(8));
        expect(hiddenNodes(store)).toEqual([[4, 5]]);
        expect(visibleSteps(store)).toEqual(['t3', 't2', 't1', 't1.t1', 't1.a0', 'a0', ' reordering ']);

        store.dispatch(undo());
        expect(hiddenNodes(store)).toEqual([[3, 4, 5, 6]]);
        expect(
            store
                .getState()
                .proof.proof.filter((node) => node.isHidden)
                .map((node) => node.id),
        ).toEqual([3, 4, 5, 6]);
    });

    it('unfolds everything in the full view and folds again in the clustered view', () => {
        const store = newStore();
        store.dispatch(process(nestedDot));
        store.dispatch(applyView('full'));
        expect(hiddenNodes(store)).toEqual([]);
        store.dispatch(applyView('clustered'));
        expect(hiddenNodes(store)).toEqual([[3, 4, 5, 6]]);
    });
});

describe('findLets', () => {
    it('finds let names only as whole symbols', () => {
        const letMap = { k: '', k1: '', let1: '' };
        expect(findLets('(and k (f k1) kk k.2 let10 let1)', letMap)).toEqual({ 5: 'k', 10: 'k1', 27: 'let1' });
    });
});
