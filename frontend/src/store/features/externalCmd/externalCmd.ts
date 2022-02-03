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
        reRender: (state) => {
            state.renderData.count = 0;
        },
        addRenderCount: (state) => {
            state.renderData.count++;
        },
        blockRender: (state) => {
            state.renderData.count = 2;
        },
        allowRenderNewFile: (state) => {
            state.renderData.fileChanged = true;
        },
        blockRenderNewFile: (state) => {
            state.renderData.fileChanged = false;
        },
    },
});

export const { findNode, reRender, addRenderCount, blockRender, allowRenderNewFile, blockRenderNewFile } =
    externalCmd.actions;

export const selectFindData = (state: RootState): { nodeToFind: number; findOption: boolean } =>
    state.externalCmd.findData;

export const selectRenderData = (state: RootState): { count: number; fileChanged: boolean } =>
    state.externalCmd.renderData;

export default externalCmd.reducer;
