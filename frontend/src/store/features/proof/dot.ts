// A parser for the DOT language (https://graphviz.org/doc/info/lang.html). HTML strings are kept as
// raw text, and ports are parsed but dropped.

export interface DotAttributes {
    [name: string]: string;
}

export interface DotNodeStatement {
    type: 'node';
    id: string;
    attributes: DotAttributes;
}

export interface DotEdgeStatement {
    type: 'edge';
    // Each element is an endpoint of the edge chain: a single node, or all the nodes of a subgraph
    chain: string[][];
    attributes: DotAttributes;
}

export interface DotAttributeStatement {
    type: 'attribute';
    target: 'graph' | 'node' | 'edge';
    attributes: DotAttributes;
}

export interface DotSubgraph {
    type: 'subgraph';
    id?: string;
    statements: DotStatement[];
}

export type DotStatement = DotNodeStatement | DotEdgeStatement | DotAttributeStatement | DotSubgraph;

export interface DotGraph {
    strict: boolean;
    directed: boolean;
    id?: string;
    statements: DotStatement[];
}

type Token = { kind: 'id'; value: string; quoted: boolean } | { kind: 'punct'; value: string };

const unquotedId = /-?(\.[0-9]+|[0-9]+(\.[0-9]*)?)|[A-Za-z_\u0080-\uffff][A-Za-z_0-9\u0080-\uffff]*/y;

function tokenize(text: string): Token[] {
    const tokens: Token[] = [];
    let i = 0;
    let lineStart = true;

    while (i < text.length) {
        const c = text[i];
        if (c === '\n') {
            lineStart = true;
            i++;
        } else if (/\s/.test(c)) {
            i++;
        } else if (c === '#' && lineStart) {
            // Lines starting with '#' are C preprocessor output and are discarded
            while (i < text.length && text[i] !== '\n') i++;
        } else if (text.startsWith('//', i)) {
            while (i < text.length && text[i] !== '\n') i++;
        } else if (text.startsWith('/*', i)) {
            const end = text.indexOf('*/', i + 2);
            if (end === -1) throw new Error('DOT: unterminated comment');
            i = end + 2;
        } else {
            lineStart = false;
            if (text.startsWith('->', i) || text.startsWith('--', i)) {
                tokens.push({ kind: 'punct', value: text.slice(i, i + 2) });
                i += 2;
            } else if ('{}[]=;,:'.includes(c)) {
                tokens.push({ kind: 'punct', value: c });
                i++;
            } else if (c === '"') {
                // In quoted strings, the only escape is \" (and a backslash before a newline, which
                // continues the line). Other backslashes are kept for the attribute to interpret.
                let value = '';
                i++;
                while (i < text.length && text[i] !== '"') {
                    if (text[i] === '\\' && text[i + 1] === '"') {
                        value += '"';
                        i += 2;
                    } else if (text[i] === '\\' && text[i + 1] === '\n') {
                        i += 2;
                    } else if (text[i] === '\\' && text[i + 1] === '\r' && text[i + 2] === '\n') {
                        i += 3;
                    } else {
                        value += text[i++];
                    }
                }
                if (i >= text.length) throw new Error('DOT: unterminated string');
                i++;

                // Quoted strings can be concatenated with '+'
                const previous = tokens[tokens.length - 1];
                const beforePrevious = tokens[tokens.length - 2];
                if (
                    previous?.kind === 'punct' &&
                    previous.value === '+' &&
                    beforePrevious?.kind === 'id' &&
                    beforePrevious.quoted
                ) {
                    tokens.pop();
                    beforePrevious.value += value;
                } else {
                    tokens.push({ kind: 'id', value, quoted: true });
                }
            } else if (c === '+') {
                tokens.push({ kind: 'punct', value: '+' });
                i++;
            } else if (c === '<') {
                let depth = 0;
                const start = i;
                do {
                    if (text[i] === '<') depth++;
                    else if (text[i] === '>') depth--;
                    i++;
                } while (depth > 0 && i < text.length);
                if (depth > 0) throw new Error('DOT: unterminated HTML string');
                tokens.push({ kind: 'id', value: text.slice(start + 1, i - 1), quoted: true });
            } else {
                unquotedId.lastIndex = i;
                const match = unquotedId.exec(text);
                if (!match) throw new Error(`DOT: unexpected character '${c}'`);
                tokens.push({ kind: 'id', value: match[0], quoted: false });
                i += match[0].length;
            }
        }
    }
    return tokens;
}

class Parser {
    private tokens: Token[];
    private pos = 0;

    constructor(tokens: Token[]) {
        this.tokens = tokens;
    }

    private peek(offset = 0): Token | undefined {
        return this.tokens[this.pos + offset];
    }

    private isPunct(value: string, offset = 0): boolean {
        const token = this.peek(offset);
        return token?.kind === 'punct' && token.value === value;
    }

    private isKeyword(keyword: string, offset = 0): boolean {
        const token = this.peek(offset);
        return token?.kind === 'id' && !token.quoted && token.value.toLowerCase() === keyword;
    }

    private expectPunct(value: string): void {
        if (!this.isPunct(value)) {
            const token = this.peek();
            throw new Error(`DOT: expected '${value}' but found '${token ? token.value : 'end of input'}'`);
        }
        this.pos++;
    }

    private expectId(): string {
        const token = this.peek();
        if (token?.kind !== 'id') {
            throw new Error(`DOT: expected an identifier but found '${token ? token.value : 'end of input'}'`);
        }
        this.pos++;
        return token.value;
    }

    parseGraph(): DotGraph {
        // Skip anything before the graph, such as the "unsat" that cvc5 prints before its proof
        while (this.peek() && !this.isKeyword('strict') && !this.isKeyword('graph') && !this.isKeyword('digraph')) {
            this.pos++;
        }
        const strict = this.isKeyword('strict');
        if (strict) this.pos++;
        if (!this.isKeyword('graph') && !this.isKeyword('digraph')) {
            throw new Error("DOT: expected 'graph' or 'digraph'");
        }
        const directed = this.isKeyword('digraph');
        this.pos++;
        const id = this.peek()?.kind === 'id' ? this.expectId() : undefined;
        this.expectPunct('{');
        const statements = this.parseStatements();
        this.expectPunct('}');
        return { strict, directed, id, statements };
    }

    private parseStatements(): DotStatement[] {
        const statements: DotStatement[] = [];
        while (this.peek() && !this.isPunct('}')) {
            statements.push(this.parseStatement());
            if (this.isPunct(';')) this.pos++;
        }
        return statements;
    }

    private parseStatement(): DotStatement {
        if ((this.isKeyword('graph') || this.isKeyword('node') || this.isKeyword('edge')) && this.isPunct('[', 1)) {
            const target = this.expectId().toLowerCase() as DotAttributeStatement['target'];
            return { type: 'attribute', target, attributes: this.parseAttributeLists() };
        }
        if (this.peek()?.kind === 'id' && this.isPunct('=', 1)) {
            const name = this.expectId();
            this.pos++;
            return { type: 'attribute', target: 'graph', attributes: { [name]: this.expectId() } };
        }

        let first: DotSubgraph | string;
        if (this.isKeyword('subgraph') || this.isPunct('{')) {
            first = this.parseSubgraph();
        } else {
            first = this.parseNodeId();
        }

        if (this.isPunct('->') || this.isPunct('--')) {
            const chain = [this.endpointNodes(first)];
            const subgraphs = typeof first === 'string' ? [] : [first];
            while (this.isPunct('->') || this.isPunct('--')) {
                this.pos++;
                const next =
                    this.isKeyword('subgraph') || this.isPunct('{') ? this.parseSubgraph() : this.parseNodeId();
                if (typeof next !== 'string') subgraphs.push(next);
                chain.push(this.endpointNodes(next));
            }
            const edge: DotEdgeStatement = { type: 'edge', chain, attributes: this.parseAttributeLists() };
            // Subgraphs used as endpoints are also subgraphs of the enclosing graph
            return subgraphs.length ? { type: 'subgraph', statements: [...subgraphs, edge] } : edge;
        }
        if (typeof first !== 'string') return first;
        return { type: 'node', id: first, attributes: this.parseAttributeLists() };
    }

    private parseSubgraph(): DotSubgraph {
        let id: string | undefined;
        if (this.isKeyword('subgraph')) {
            this.pos++;
            if (this.peek()?.kind === 'id') id = this.expectId();
        }
        this.expectPunct('{');
        const statements = this.parseStatements();
        this.expectPunct('}');
        return { type: 'subgraph', id, statements };
    }

    private parseNodeId(): string {
        const id = this.expectId();
        // Ports are irrelevant for us
        while (this.isPunct(':')) {
            this.pos++;
            this.expectId();
        }
        return id;
    }

    private parseAttributeLists(): DotAttributes {
        const attributes: DotAttributes = {};
        while (this.isPunct('[')) {
            this.pos++;
            while (!this.isPunct(']')) {
                const name = this.expectId();
                if (this.isPunct('=')) {
                    this.pos++;
                    attributes[name] = this.expectId();
                } else {
                    attributes[name] = 'true';
                }
                if (this.isPunct(';') || this.isPunct(',')) this.pos++;
            }
            this.pos++;
        }
        return attributes;
    }

    private endpointNodes(endpoint: DotSubgraph | string): string[] {
        return typeof endpoint === 'string' ? [endpoint] : subgraphNodes(endpoint);
    }
}

// All the nodes that occur in a subgraph, including in its nested subgraphs
export function subgraphNodes(subgraph: DotSubgraph, nodes = new Set<string>()): string[] {
    subgraph.statements.forEach((statement) => {
        if (statement.type === 'node') nodes.add(statement.id);
        else if (statement.type === 'edge')
            statement.chain.forEach((endpoint) => endpoint.forEach((n) => nodes.add(n)));
        else if (statement.type === 'subgraph') subgraphNodes(statement, nodes);
    });
    return Array.from(nodes);
}

export function parseDot(text: string): DotGraph {
    return new Parser(tokenize(text)).parseGraph();
}
