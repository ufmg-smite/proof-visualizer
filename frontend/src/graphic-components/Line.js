import { Arrow } from 'react-konva';
import PropTypes from 'prop-types';

export default function Line(props) {
  const { points, key } = props;

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

Line.propTypes = {
  points: PropTypes.any,
  key: PropTypes.any,
};
