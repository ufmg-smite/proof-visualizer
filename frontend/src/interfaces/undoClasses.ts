export enum UndoKind {
    MOVE,
    COLOR,
    FOLD,
    HIDE,
    UNFOLD,
    SELECT,
}

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

export class FoldUndo extends BaseUndo {
    constructor(nodes: number[]) {
        super(nodes);
    }
}
