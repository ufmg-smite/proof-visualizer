const { spawnSync } = require('child_process');
const router = require('express').Router();
const fs = require('fs');

const Proof = require('../models/proof.model');

router.route('/').get((req, res) => {
  Proof.find()
    .then((proofs) => res.json(proofs))
    .catch((err) => res.status(400).json(`Error: ${err}`));
});

router.route('/add').post((req, res) => {
  const { label, problem, options } = req.body;

  const newProof = new Proof({
    label,
    problem,
    options,
  });

  newProof
    .save()
    .then(() => res.json(newProof.id))
    .catch((err) => res.status(400).json(`Error: ${err}`));
});

router.route('/:id').get((req, res) => {
  Proof.findById(req.params.id)
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
      if (proof.state === 'done') {
        res.json(proof.dot);
      }
      fs.writeFileSync(
        `${process.cwd()}/proof_files/proof.${proof.input_language}`,
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
        `${process.cwd()}/proof_files/proof.${proof.input_language}`,
        '--dump-proof',
        '--proof-format-mode=dot',
        '--proof',
      ].concat(userOptions);

      const cvc4 = spawnSync('cvc4', options);

      if (!cvc4.stderr.toString().length) {
        proof.dot = cvc4.stdout;
        proof.dot = proof.dot.slice(proof.dot.indexOf('digraph'));
        proof.state = 'done';
      } else {
        proof.error = cvc4.stderr.toString();
        proof.state = 'error';
      }
      proof.save();
      res.json(proof.dot);
    })
    .catch((err) => {
      res.status(400).json(`Error: ${err}`);
    });
});

module.exports = router;
