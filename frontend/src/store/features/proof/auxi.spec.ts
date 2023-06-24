import { processAlethe } from './auxi';

describe('auxi test suite', () => {
    describe('processAlethe', () => {
        test('should return an empty array if given an empty proof', () => {
            const result = processAlethe('');
            expect(result).toEqual([[], {}, {}]);
        });

        test('should return correct nodes for a single-line proof', () => {
            const result = processAlethe('(assume a0 (= a b))');
            const expectedOutput = [
                [
                    {
                        id: 0,
                        conclusion: '(= a b)',
                        rule: 'assume',
                        args: '',
                        children: [],
                        parents: [],
                        descendants: 0,
                        dependencies: [],
                        clusterType: 0,
                    },
                ],
                {},
                {},
            ];
            expect(result).toEqual(expectedOutput);
        });

        test('should return correct nodes for a multi-line proof with premises', () => {
            const proof = `(assume a0 (= a b))\n(assume a1 (= c d))\n(assume a2 (not (= a c)))\n(step a3 (= b d) :rule symm :premises (a0 a1))`;
            const result = processAlethe(proof);
            const expectedOutput = [
                [
                    {
                        id: 0,
                        conclusion: 'ep a3 (= b d) :rule symm :premises (a0 a1)',
                        rule: 'symm',
                        args: '',
                        children: [3, 2],
                        parents: [],
                        descendants: 2,
                        dependencies: [],
                        clusterType: 0,
                    },
                    {
                        id: 1,
                        conclusion: '(not (= a c))',
                        rule: 'assume',
                        args: '',
                        children: [],
                        parents: [],
                        descendants: 0,
                        dependencies: [],
                        clusterType: 0,
                    },
                    {
                        id: 2,
                        conclusion: '(= c d)',
                        rule: 'assume',
                        args: '',
                        children: [],
                        parents: [0],
                        descendants: 0,
                        dependencies: [],
                        clusterType: 0,
                    },
                    {
                        id: 3,
                        conclusion: '(= a b)',
                        rule: 'assume',
                        args: '',
                        children: [],
                        parents: [0],
                        descendants: 0,
                        dependencies: [],
                        clusterType: 0,
                    },
                ],
                {},
                {},
            ];
            expect(result).toEqual(expectedOutput);
        });

        test('should return correct nodes for a multi-line proof with discharge and subproof', () => {
            const proof = `(assume a0 (= a b))\n(assume a1 (= c d))\n(assume a2 (not (= a c)))\n(anchor :step t3)\n(assume t3.a0 (= a b))\n(assume t3.a1 (= c d))\n(step t3.t1 (cl (= b a)) :rule symm)\n(step t3 (= b d) :rule :rule subproof :discharge (t3.a0 t3.a1))`;
            const result = processAlethe(proof);
            const expectedOutput = [
                [
                    {
                        id: 0,
                        conclusion: 'ep t3 (= b d) :rule :rule subproof :discharge (t3.a0 t3.a1)',
                        rule: 'subproof',
                        args: 't3.a0 t3.a1',
                        children: [1],
                        parents: [],
                        descendants: 1,
                        dependencies: [],
                        clusterType: 0,
                    },
                    {
                        id: 1,
                        conclusion: '(= b a)',
                        rule: 'symm',
                        args: '',
                        children: [],
                        parents: [0],
                        descendants: 0,
                        dependencies: [],
                        clusterType: 0,
                    },
                    {
                        id: 2,
                        conclusion: '(= c d)',
                        rule: 'assume',
                        args: '',
                        children: [],
                        parents: [],
                        descendants: 0,
                        dependencies: [],
                        clusterType: 0,
                    },
                    {
                        id: 3,
                        conclusion: '(= a b)',
                        rule: 'assume',
                        args: '',
                        children: [],
                        parents: [],
                        descendants: 0,
                        dependencies: [],
                        clusterType: 0,
                    },
                    {
                        id: 4,
                        conclusion: '(not (= a c))',
                        rule: 'assume',
                        args: '',
                        children: [],
                        parents: [],
                        descendants: 0,
                        dependencies: [],
                        clusterType: 0,
                    },
                    {
                        id: 5,
                        conclusion: '(= c d)',
                        rule: 'assume',
                        args: '',
                        children: [],
                        parents: [],
                        descendants: 0,
                        dependencies: [],
                        clusterType: 0,
                    },
                    {
                        id: 6,
                        conclusion: '(= a b)',
                        rule: 'assume',
                        args: '',
                        children: [],
                        parents: [],
                        descendants: 0,
                        dependencies: [],
                        clusterType: 0,
                    },
                ],
                {},
                {},
            ];
            expect(result).toEqual(expectedOutput);
        });
    });
});
