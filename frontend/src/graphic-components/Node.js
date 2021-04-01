import React from 'react';
import { Label, Text, Tag } from 'react-konva';
import PropTypes from 'prop-types';

function textColorFromBg(bgColor) {
  const color = bgColor.charAt(0) === '#' ? bgColor.substring(1, 7) : bgColor;
  const r = parseInt(color.substring(0, 2), 16);
  const g = parseInt(color.substring(2, 4), 16);
  const b = parseInt(color.substring(4, 6), 16);
  return r * 0.299 + g * 0.587 + b * 0.114 > 150 ? '#000000' : '#ffffff';
}

export default function Node(props) {
  const [bgClosedConclusionColor, bgOpenConclusionColor, bgRuleColor] = [
    '#2b2d42',
    '#8d99ae',
    '#edf2f4',
  ];

  const { children, id, onClick, onMouse, showingChildren, x, y } = props;

  const conclusion = id.indexOf('c') !== -1;

  const bgConclusionColor = showingChildren
    ? bgOpenConclusionColor
    : bgClosedConclusionColor;
  const bgColor = conclusion ? bgConclusionColor : bgRuleColor;

  return (
    <Label
      conclusion={conclusion}
      draggable
      id={id}
      key={id}
      onClick={onClick}
      onDragMove={(e) => {
        const { updateParentState } = props;
        updateParentState(id, e.target.attrs.x, e.target.attrs.y);
      }}
      onMouseEnter={(e) => {
        onMouse(e.target.attrs.text);
      }}
      onMouseLeave={() => onMouse('')}
      x={x}
      y={y}
    >
      <Tag fill={bgColor} stroke="black" />
      <Text
        align="center"
        fill={textColorFromBg(bgColor)}
        fontSize={15}
        height={35}
        padding={10}
        text={children}
        width={300}
      />
    </Label>
  );
}

Node.propTypes = {
  children: PropTypes.string,
  id: PropTypes.string,
  onClick: PropTypes.func,
  onMouse: PropTypes.func,
  showingChildren: PropTypes.bool,
  updateParentState: PropTypes.func,
  x: PropTypes.number,
  y: PropTypes.number,
};
