import { combineReducers } from 'redux';

import stateInterface from './stateInterface';

import proof from '../components/interfaces/ProofInterface';

export interface proofState {
    label: string;
    options: string | undefined;
    problem: string;
    dot: string | undefined;
}

const initialState = {
    proof: {
        label: '',
        options: '',
        problem: '',
        dot: '',
    },
};

type Action = { type: 'SET_PROOF'; payload: proof };

export const proofReducer = (state: stateInterface = initialState, action: Action): stateInterface => {
    console.log(action);
    switch (action.type) {
        case 'SET_PROOF':
            return {
                ...state,
                proof: {
                    label: action.payload.label,
                    options: action.payload.options,
                    problem: action.payload.problem,
                    dot: action.payload.dot,
                },
            };
        default:
            return state;
    }
};

export default combineReducers({ proofReducer });
