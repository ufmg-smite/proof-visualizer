const { spawnSync } = require('child_process');
const router = require('express').Router();
const fs = require('fs');

router.route('/new-proof').post((req, res) => {
  const { problem, options } = req.body;

  fs.writeFileSync(`${process.cwd()}/proof_files/proof.smt2`, problem, (err) => {
      if (err) {
          throw err;
      }
  });

  const userOptions = options !== '' ? options.split(' ') : [];
  const cvc5Options = [
      `${process.cwd()}/proof_files/proof.smt2`,
      '--dump-proof',
      '--proof-format-mode=dot',
  ].concat(userOptions);

  const cvc5 = spawnSync(`${process.cwd()}/cvc5/cvc5`, cvc5Options);

  if (!cvc5.stderr.toString().length) {
      let dot = cvc5.stdout;
      dot = dot.slice(dot.indexOf('digraph'));
      res.json(dot.toString());
  } else {
      throw Object.assign(new Error(`CVC5 ERROR:\n${cvc5.stderr.toString()}`));
  }
});

module.exports = router;
