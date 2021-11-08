import { combineReducers } from 'redux';

import { proof, stateInterface } from '../components/interfaces/interfaces';

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

const initialStateLetMapReducer = {
    letMap: {},
};

const initialStateImportedDataReducer = {
    importedData: {
        nodes: [],
    },
};

type Action =
    | { type: 'SET_PROOF'; payload: proof }
    | { type: 'TOGGLE_DARK_THEME' }
    | { type: 'SET_DOT'; payload: proof['dot'] }
    | { type: 'BASIC_VIEW' }
    | { type: 'PROPOSITIONAL_VIEW' }
    | { type: 'FULL_VIEW' }
    | { type: 'IMPORTED_DATA_VIEW' }
    | { type: 'SET_STYLE'; payload: string }
    | {
          type: 'SET_LET_MAP';
          payload: {
              [Key: string]: string;
          };
      }
    | {
          type: 'SET_IMPORTED_DATA';
          payload: {
              nodes: Array<{ id: number; color: string; x: number; y: number; hidden: Array<number> }>;
              hidden: Array<Array<number>>;
          };
      };

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
        case 'IMPORTED_DATA_VIEW':
            return {
                ...state,
                proof: {
                    ...state.proof,
                    view: 'imported_data',
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

const letMapReducer = (
    state: stateInterface['letMapReducer'] = initialStateLetMapReducer,
    action: Action,
): stateInterface['letMapReducer'] => {
    switch (action.type) {
        case 'SET_LET_MAP':
            return {
                ...state,
                letMap: action.payload,
            };
        default:
            return state;
    }
};

const importedDataReducer = (
    state: {
        importedData: {
            nodes: Array<{ id: number; color: string; x: number; y: number; hidden: Array<number> }>;
        };
    } = initialStateImportedDataReducer,
    action: Action,
): stateInterface['importedDataReducer'] => {
    switch (action.type) {
        case 'SET_IMPORTED_DATA':
            return {
                ...state,
                importedData: action.payload,
            };
        default:
            return state;
    }
};

export default combineReducers({ proofReducer, darkThemeReducer, styleReducer, letMapReducer, importedDataReducer });
