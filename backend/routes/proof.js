const { spawnSync } = require('child_process');
const router = require('express').Router();
const fs = require('fs');

const Proof = require('../models/proof.model');

router.route('/').get((req, res) => {
  Proof.find()
    .select('_id label problem options dot')
    .then((proofs) => res.json(proofs))
    .catch((err) => res.status(400).json(`Error: ${err}`));
});

router.route('/add').post((req, res) => {
  const { label } = req.body;
  const { problem } = req.body;
  const { options } = req.body;
  const inputLanguage = 'smt2';
  const state = 'proof_received';

  const newProof = new Proof({
    label,
    problem,
    inputLanguage,
    state,
    options,
  });

  newProof
    .save()
    .then(() => res.json(newProof.id))
    .catch((err) => res.status(400).json(`Error: ${err}`));
});

router.route('/:id').get((req, res) => {
  Proof.findById(req.params.id)
    .select('label problem options dot')
    .then((proof) => res.json(proof))
    .catch((err) => res.status(400).json(`Error: ${err}`));
});

router.route('/:id').delete((req, res) => {
  Proof.findByIdAndDelete(req.params.id)
    .then(() => res.json('Proof deleted.'))
    .catch((err) => res.status(400).json(`Error: ${err}`));
});

router.route('/process-proof/:id').get((req, res) => {
  Proof.findById(req.params.id)
    .then((proof) => {
      if (proof.state === 'dot_ready') {
        res.json(proof.dot);
      }
      fs.writeFileSync(
        `${process.cwd()}/proof_files/proof.smt2`,
        proof.problem,
        (err) => {
          if (err) {
            throw err;
          }
        }
      );
      return proof;
    })
    .then((proof) => {
      const userOptions = proof.options !== '' ? proof.options.split(' ') : [];
      const options = [
        `${process.cwd()}/proof_files/proof.smt2`,
        '--dump-proof',
        '--proof-format-mode=dot',
        '--proof',
      ].concat(userOptions);

      const cvc4 = spawnSync('cvc4', options);

      proof.dot = cvc4.stdout;
      proof.dot = proof.dot.slice(proof.dot.indexOf('digraph'));
      proof.state = 'dot_ready';
      proof.save();
      res.json(proof.dot);
    })
    .catch((err) => {
      res.status(400).json(`Error: ${err}`);
    });
});

module.exports = router;
