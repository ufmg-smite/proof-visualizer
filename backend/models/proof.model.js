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
      default: 'smt2',
    },
    dot: {
      type: String,
    },
    state: {
      type: String,
      require: true,
      enum: ['proof_received', 'done', 'error'],
      default: 'proof_received',
    },
    options: {
      type: String,
    },
    error: {
      type: String,
    },
  },
  {
    timestamps: true,
  }
);

const Proof = mongoose.model('Proof', proofSchema);

module.exports = Proof;
