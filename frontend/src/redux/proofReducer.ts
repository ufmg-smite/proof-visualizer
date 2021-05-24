import { combineReducers } from 'redux';

import { proof, stateInterface } from '../components/interfaces';

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
