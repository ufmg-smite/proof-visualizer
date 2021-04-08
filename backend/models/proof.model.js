const mongoose = require('mongoose');

const { Schema } = mongoose;

const proofSchema = new Schema(
  {
    label: {
      type: String,
    },
    problem: {
      type: String,
    },
    input_language: {
      type: String,
      enum: ['smt2'],
    },
    dot: {
      type: String,
    },
    state: {
      type: String,
      require: true,
      enum: ['proof_received', 'dot_ready', 'done', 'error'],
    },
    options: {
      type: String,
    },
  },
  {
    timestamps: true,
  }
);

const Proof = mongoose.model('Proof', proofSchema);

module.exports = Proof;
