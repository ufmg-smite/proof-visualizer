const express = require('express');
const cors = require('cors');

const app = express();
const port = process.env.PORT || 5000;

app.options('*', cors());
app.use(cors());
app.use(express.json());

const proofRouter = require('./routes/proof');

app.use('/proof', proofRouter);

app.listen(port, () => {
  console.log(`Server is running on port: ${port}`);
});
