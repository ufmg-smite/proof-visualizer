import React, { Component } from 'react';
import { Label, Text, Tag } from 'react-konva';
import PropTypes from 'prop-types';

function textColorFromBg(bgColor) {
  const color = bgColor.charAt(0) === '#' ? bgColor.substring(1, 7) : bgColor;
  const r = parseInt(color.substring(0, 2), 16);
  const g = parseInt(color.substring(2, 4), 16);
  const b = parseInt(color.substring(4, 6), 16);
  return r * 0.299 + g * 0.587 + b * 0.114 > 150 ? '#000000' : '#ffffff';
}

export default class Node extends Component {
  constructor(props) {
    super(props);

    this.state = {
      bgClosedConclusionColor: '#2b2d42',
      bgOpenConclusionColor: '#8d99ae',
      bgRuleColor: '#edf2f4',
    };
  }

  render() {
    const {
      children,
      id,
      onClick,
      onMouse,
      showingChildren,
      x,
      y,
    } = this.props;

    const {
      bgClosedConclusionColor,
      bgOpenConclusionColor,
      bgRuleColor,
    } = this.state;

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
          const { updateParentState } = this.props;
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
