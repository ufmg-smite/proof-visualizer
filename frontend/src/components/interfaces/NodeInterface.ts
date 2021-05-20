interface NodeInterface {
    id: number;

    conclusion: string;
    rule: string;
    views: Array<string>;
    children: Array<number>;
    parent: number;

    positionCache: boolean;
    x: number;
    y: number;

    showingChildren: boolean;

    // The node that hide its children
    hideMyChildNode: number;

    hidedNodes: Array<number>;

    hided: boolean;
    hidedIn: number;
}

export type nodeInterface = NodeInterface;
