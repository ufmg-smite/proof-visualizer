const mongoose = require('mongoose');

const Schema = mongoose.Schema;

const proofSchema = new Schema({
    problem : {
        type: String,
    },
    input_language : {
        type: String,
        enum: ['smt2']
    },
    dot : {
        type: String,
    },
    svg : {
        type: String,
    },
    state : {
        type: String,
        require: true,
        enum: ['proof_received', 'dot_ready', 'svg_ready', 'done', 'error']
    }
}, {
    timestamps: true,
});

const Proof = mongoose.model('Proof', proofSchema);

module.exports = Proof;