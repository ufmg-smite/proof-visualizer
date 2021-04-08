const express = require('express');
const cors = require('cors');
const mongoose = require('mongoose');

require('dotenv').config();

const app = express();
const port = process.env.PORT || 5000;

app.options('*', cors());
app.use(cors());
app.use(express.json());

const uri = process.env.ATLAS_URI;
mongoose.connect(uri, {
  useUnifiedTopology: true,
  useNewUrlParser: true,
  useCreateIndex: true,
});
const { connection } = mongoose;
connection.once('open', () => {
  console.log('MongoDB database connection established successfully');
});

const proofRouter = require('./routes/proof');

app.use('/proof', proofRouter);

app.listen(port, () => {
  console.log(`Server is running on port: ${port}`);
});
