interface NodeInterface {
    id: number;
    conclusion: string;
    rule: string;
    views: Array<string>;
    children: Array<number>;
    parent: number;
    x: number;
    y: number;
    foldedNode: number;
    showingChildren: boolean;
    hided: boolean;
    hidedNodes: Array<number>;
    piNode: boolean;
    hidedIn: number;
    positionCache: boolean;
}

export type nodeInterface = NodeInterface;
