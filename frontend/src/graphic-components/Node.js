import React, { Component } from 'react';
import { Label, Text, Tag } from 'react-konva';
import PropTypes from 'prop-types';

export default class Node extends Component {
  constructor(props) {
    super(props);

    const {
      name,
      onClick,
      y,
      x,
      children,
      conclusion,
      key,
      id,
      updateParentState,
      onMouseIn,
      onMouseOut,
    } = this.props;

    this.state = {
      name,
      onClick,
      x,
      y,
      children,
      conclusion,
      key,
      id,
      updateParentState,
      onMouseIn,
      onMouseOut,
      color: ['#8d99ae', '#2b2d42', '#edf2f4'],
    };
  }

  onDragEnd = (e) => {
    const { updateParentState, id } = this.state;
    updateParentState(id, e.target.attrs.x, e.target.attrs.y);
  };

  render() {
    const {
      name,
      onClick,
      y,
      x,
      children,
      conclusion,
      key,
      onMouseIn,
      onMouseOut,
      color,
    } = this.state;

    const { showingChildren } = this.props;

    const colorConclusionBG = showingChildren ? color[0] : color[1];
    const colorText = conclusion && !showingChildren ? 'white' : 'black';

    return (
      <Label
        conclusion={conclusion}
        key={key}
        name={name}
        id={name}
        onClick={onClick}
        draggable
        x={x}
        y={y}
        onDragEnd={(e) => this.onDragEnd(e)}
        onMouseEnter={(e) => {
          onMouseIn(e.target.attrs.text);
        }}
        onMouseLeave={() => onMouseOut()}
      >
        <Tag fill={conclusion ? colorConclusionBG : color[2]} stroke="black" />
        <Text
          text={children}
          fontSize={15}
          width={300}
          height={35}
          padding={10}
          align="center"
          fill={colorText}
        />
      </Label>
    );
  }
}

Node.propTypes = {
  name: PropTypes.any,
  onClick: PropTypes.any,
  y: PropTypes.any,
  x: PropTypes.any,
  children: PropTypes.any,
  conclusion: PropTypes.bool,
  key: PropTypes.any,
  id: PropTypes.any,
  updateParentState: PropTypes.func,
  showingChildren: PropTypes.any,
  onMouseIn: PropTypes.func,
  onMouseOut: PropTypes.func,
};
