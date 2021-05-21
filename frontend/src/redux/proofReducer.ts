import stateInterface from './stateInterface';

import proof from '../components/interfaces/ProofInterface';

export interface proofState {
    label: string;
    options: string | undefined;
    problem: string;
    dot: string | undefined;
}

const initialState = {
    label: '',
    options: '',
    problem: '',
    dot: '',
};

type Action = { type: 'SET_DOT'; payload: proof };

export const proofReducer = (state: proofState = initialState, action: Action): stateInterface => {
    switch (action.type) {
        case 'SET_DOT':
            return {
                ...state,
                label: action.payload.label,
                options: action.payload.options,
                problem: action.payload.problem,
                dot: action.payload.dot,
            };
        default:
            return state;
    }
};
