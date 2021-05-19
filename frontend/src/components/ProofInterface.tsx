import { ObjectID } from 'mongodb';

export default interface proof {
    _id?: ObjectID;
    label: string;
    options?: string;
    problem: string;
    dot?: string;
}
