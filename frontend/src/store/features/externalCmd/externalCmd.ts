import { createSlice, PayloadAction } from '@reduxjs/toolkit';
import { RootState } from '../../store';
import { ExternalCmdState } from '../../../interfaces/interfaces';

const initialState: ExternalCmdState = {
    findData: {
        nodeToFind: -1,
        findOption: false,
    },
    renderData: {
        count: 0,
        fileChanged: false,
    },
};

export const externalCmd = createSlice({
    name: 'externalCmd',
    initialState,
    reducers: {
        findNode: (state, action: PayloadAction<{ nodeId: number; option: boolean }>) => {
            state.findData = { nodeToFind: action.payload.nodeId, findOption: action.payload.option };
        },
    },
});

export const { findNode } = externalCmd.actions;

export const selectFindData = (state: RootState): { nodeToFind: number; findOption: boolean } =>
    state.externalCmd.findData;

export default externalCmd.reducer;
