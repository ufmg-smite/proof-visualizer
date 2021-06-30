import { combineReducers } from 'redux';

import { proof, stateInterface } from '../components/interfaces';

const initialStateProofReducer = {
    proof: {
        label: '',
        options: '',
        problem: '',
        dot: '',
        view: 'basic',
    },
};

const initialStateDarkThemeReducer = {
    darkTheme: true,
};

const initialStateStyleReducer = {
    style: 'tree',
};

type Action =
    | { type: 'SET_PROOF'; payload: proof }
    | { type: 'TOGGLE_DARK_THEME' }
    | { type: 'SET_DOT'; payload: proof['dot'] }
    | { type: 'BASIC_VIEW' }
    | { type: 'PROPOSITIONAL_VIEW' }
    | { type: 'FULL_VIEW' }
    | { type: 'SET_STYLE'; payload: string };

const proofReducer = (
    state: stateInterface['proofReducer'] = initialStateProofReducer,
    action: Action,
): stateInterface['proofReducer'] => {
    switch (action.type) {
        case 'SET_PROOF':
            return {
                ...state,
                proof: {
                    label: action.payload.label,
                    options: action.payload.options,
                    problem: action.payload.problem,
                    dot: action.payload.dot,
                    view: 'basic',
                },
            };
        case 'SET_DOT':
            return {
                ...state,
                proof: {
                    ...state.proof,
                    dot: action.payload,
                },
            };
        case 'BASIC_VIEW':
            return {
                ...state,
                proof: {
                    ...state.proof,
                    view: 'basic',
                },
            };
        case 'PROPOSITIONAL_VIEW':
            return {
                ...state,
                proof: {
                    ...state.proof,
                    view: 'propositional',
                },
            };
        case 'FULL_VIEW':
            return {
                ...state,
                proof: {
                    ...state.proof,
                    view: 'full',
                },
            };
        default:
            return state;
    }
};

const darkThemeReducer = (
    state: stateInterface['darkThemeReducer'] = initialStateDarkThemeReducer,
    action: Action,
): stateInterface['darkThemeReducer'] => {
    switch (action.type) {
        case 'TOGGLE_DARK_THEME':
            return {
                ...state,
                darkTheme: !state.darkTheme,
            };
        default:
            return state;
    }
};

const styleReducer = (
    state: stateInterface['styleReducer'] = initialStateStyleReducer,
    action: Action,
): stateInterface['styleReducer'] => {
    switch (action.type) {
        case 'SET_STYLE':
            return {
                ...state,
                style: action.payload,
            };
        default:
            return state;
    }
};

export default combineReducers({ proofReducer, darkThemeReducer, styleReducer });
