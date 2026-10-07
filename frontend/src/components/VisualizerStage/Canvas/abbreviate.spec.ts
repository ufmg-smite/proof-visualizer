import { abbreviateTerm } from './abbreviate';

const atMost = (n: number) => (text: string) => text.length <= n;

describe('abbreviateTerm', () => {
    const clause =
        '(cl (not (= (store a1 i (select a2 i)) (store a2 i (select a1 i)))) (= i k) (= (select a1 k) (select a2 k)))';

    it('keeps terms that fit', () => {
        expect(abbreviateTerm(clause, atMost(clause.length))).toBe(clause);
    });

    it('collapses the deepest subterms, then shows again the ones that fit', () => {
        expect(abbreviateTerm(clause, atMost(40))).toBe('(cl (not (= … …)) (= i k) (= … …))');
        expect(abbreviateTerm(clause, atMost(60))).toBe('(cl (not (= … …)) (= i k) (= (select a1 k) (select a2 k)))');
    });

    it('collapses at most the arguments of the outermost term', () => {
        expect(abbreviateTerm(clause, atMost(10))).toBe('(cl … … …)');
        expect(abbreviateTerm(clause, atMost(5))).toBe('(cl … … …)');
    });

    it('ignores parentheses in quoted symbols and strings', () => {
        expect(abbreviateTerm('(f |a (b| "c)d" (g x))', atMost(12))).toBe('(f |a (b| "c)d" …)');
    });

    it('abbreviates the terms of a pi node', () => {
        expect(abbreviateTerm('[ (= a (f b)), q ]', atMost(14))).toBe('[ (= a …), q ]');
    });

    it('leaves unbalanced terms alone', () => {
        expect(abbreviateTerm('(f (g x)', atMost(3))).toBe('(f (g x)');
    });
});
