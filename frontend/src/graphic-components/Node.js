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
      showingChildren,
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
      isDragging: false,
      updateParentState,
      showingChildren,
    };
  }

  onDragEnd = (e) => {
    const { updateParentState, id } = this.state;
    this.state = {
      ...this.state,
      x: e.target.x(),
      y: e.target.y(),
    };
    updateParentState(id, e.target.x(), e.target.y());
  };

  x() {
    const { x } = this.state;
    return x;
  }

  y() {
    const { y } = this.state;
    return y;
  }

  render() {
    const { name, onClick, y, x, children, conclusion, key } = this.state;

    const { showingChildren } = this.props;

    const colorConclusion = showingChildren ? 'darkgray' : 'gray';

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
      >
        <Tag fill={conclusion ? colorConclusion : 'white'} stroke="black" />
        <Text
          text={children}
          fontSize={15}
          width={300}
          height={35}
          padding={10}
          align="center"
          fill="black"
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
};
