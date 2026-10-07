// A parenthesized subterm, as its span in the term
interface List {
    start: number;
    end: number;
    depth: number;
    children: List[];
}

// Finds the parenthesized subterms of a term, ignoring parentheses inside quoted symbols (|...|)
// and string literals ("..."). Returns null if the parentheses are unbalanced.
function findLists(term: string): List[] | null {
    const lists: List[] = [];
    const open: List[] = [];
    for (let i = 0; i < term.length; i++) {
        const c = term[i];
        if (c === '|' || c === '"') {
            // A "" inside a string literal is handled as the end of one string and start of another
            const close = term.indexOf(c, i + 1);
            if (close === -1) return null;
            i = close;
        } else if (c === '(') {
            const list = { start: i, end: -1, depth: open.length, children: [] };
            if (open.length) open[open.length - 1].children.push(list);
            open.push(list);
            lists.push(list);
        } else if (c === ')') {
            const list = open.pop();
            if (!list) return null;
            list.end = i + 1;
        }
    }
    return open.length ? null : lists;
}

// The term with each of the collapsed subterms replaced by '…'
function render(term: string, collapsed: List[]): string {
    let text = '';
    let pos = 0;
    [...collapsed]
        .sort((a, b) => a.start - b.start)
        .forEach((list) => {
            text += term.slice(pos, list.start) + '…';
            pos = list.end;
        });
    return text + term.slice(pos);
}

// Shortens a term until it fits, replacing its deepest subterms by '…' so that it stays well formed.
// Subterms are then shown again, outermost and leftmost first, wherever they still fit. If even the
// arguments of the outermost term don't fit, they are all collapsed and the result is still too long.
export function abbreviateTerm(term: string, fits: (text: string) => boolean): string {
    if (fits(term)) return term;
    const lists = findLists(term);
    if (!lists) return term;

    // Collapse the subterms below some depth, starting from the deepest. The term itself is kept.
    const maxDepth = lists.reduce((acc, list) => Math.max(acc, list.depth), 0);
    let collapsed: List[] = [];
    for (let depth = maxDepth; depth >= 1; depth--) {
        collapsed = lists.filter((list) => list.depth === depth);
        if (fits(render(term, collapsed))) break;
    }

    // Expand the collapsed subterms one level at a time while the term still fits
    const queue = [...collapsed].sort((a, b) => a.start - b.start);
    for (let list = queue.shift(); list; list = queue.shift()) {
        const expanded = collapsed.filter((l) => l !== list).concat(list.children);
        if (fits(render(term, expanded))) {
            collapsed = expanded;
            queue.push(...list.children);
        }
    }
    return render(term, collapsed);
}

let measureContext: CanvasRenderingContext2D | null | undefined;

// The width of a text in the nodes' font: 15px Arial, the default font of the canvas text. Returns
// 0 if it can't be measured.
export function nodeTextWidth(text: string): number {
    if (measureContext === undefined) measureContext = document.createElement('canvas').getContext('2d');
    if (!measureContext) return 0;
    measureContext.font = '15px Arial';
    return measureContext.measureText(text).width;
}

// Abbreviates a term to fit in one line of a node box, which is 300px wide with 10px of padding on
// each side
export function fitInNode(term: string): string {
    return abbreviateTerm(term, (text) => nodeTextWidth(text) <= 280);
}
