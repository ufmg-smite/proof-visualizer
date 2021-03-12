import React, { Component } from 'react';
import { Arrow } from 'react-konva';
import PropTypes from 'prop-types';

export default class Line extends Component {
  constructor(props) {
    super(props);

    const { points, key } = this.props;

    this.state = {
      points,
      key,
    };
  }

  setPoints(points) {
    this.setState({ points });
  }

  render() {
    const { points, key } = this.state;

    return (
      <Arrow
        key={key}
        strokeWidth={2}
        stroke="black"
        fill="black"
        points={[points[0], points[1], points[2], points[3]]}
      />
    );
  }
}

Line.propTypes = {
  points: PropTypes.any,
  key: PropTypes.any,
};
