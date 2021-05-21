import { createStore } from 'redux';
import { proofReducer } from './proofReducer';

export const store = createStore(proofReducer);
