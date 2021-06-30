FROM node:16

WORKDIR /usr/src/app

COPY ./package.json ./
COPY ./package-lock.json ./

RUN npm install -g npm@7.19.0
RUN npm install

COPY . .

EXPOSE 5000

CMD ["node", "server"]