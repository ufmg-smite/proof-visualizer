export class BaseUndo {
    nodes: number[];

    constructor(nodes: number[]) {
        this.nodes = nodes;
    }
}

export class MoveUndo extends BaseUndo {
    x: number;
    y: number;

    constructor(nodes: number[], x: number, y: number) {
        super(nodes);
        this.x = x;
        this.y = y;
    }
}

export class ColorUndo extends BaseUndo {
    color: string[];

    constructor(nodes: number[], color: string[]) {
        super(nodes);
        this.color = color;
    }
}

export class UnfoldUndo extends BaseUndo {
    positions: { [id: number]: { x: number; y: number } };
    colors: { [id: number]: string };

    constructor(
        nodes: number[],
        positions: { [id: number]: { x: number; y: number } },
        colors: { [id: number]: string },
    ) {
        super(nodes);
        this.positions = positions;
        this.colors = colors;
    }
}

export class FoldUndo extends BaseUndo {
    positions: { [id: number]: { x: number; y: number } };

    constructor(nodes: number[], positions: { [id: number]: { x: number; y: number } }) {
        super(nodes);
        this.positions = positions;
    }
}
