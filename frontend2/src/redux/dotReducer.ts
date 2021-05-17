import stateInterface from './stateInterface';

export interface dotState {
    dot: string;
}

const initialState = {
    dot: 'blablabla',
};

type Action = { type: 'SET_DOT'; payload: string };

export const dotReducer = (state: dotState = initialState, action: Action): stateInterface => {
    switch (action.type) {
        case 'SET_DOT':
            return { ...state, dot: action.payload };
        default:
            return state;
    }
};
