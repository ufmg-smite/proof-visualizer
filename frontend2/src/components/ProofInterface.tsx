import { ObjectID } from 'mongodb';

export default interface proof {
    _id: ObjectID;
    label: string;
    problem: string;
}
