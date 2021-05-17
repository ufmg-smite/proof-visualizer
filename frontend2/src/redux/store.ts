import { createStore } from 'redux';
import { dotReducer } from './dotReducer';

export const store = createStore(dotReducer);
