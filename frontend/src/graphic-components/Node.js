import React from 'react';
import { Label, Text, Tag } from 'react-konva';
import PropTypes from 'prop-types';

function Node(props) {
  const { name, onClick, y, x, children, conclusion } = props;

  return (
    <Label
      key={name}
      name={name}
      id={name}
      onClick={onClick}
      draggable
      y={y}
      x={x}
      cornerRadius={100}
    >
      <Tag fill={conclusion ? 'gray' : 'white'} stroke="black" />
      <Text
        text={children}
        fontSize={15}
        lineHeight={1.2}
        padding={10}
        fill="black"
      />
    </Label>
  );
}

export default Node;

Node.propTypes = {
  name: PropTypes.any,
  onClick: PropTypes.any,
  y: PropTypes.any,
  x: PropTypes.any,
  children: PropTypes.any,
  conclusion: PropTypes.bool,
};
