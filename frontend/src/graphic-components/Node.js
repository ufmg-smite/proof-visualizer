import React, { Component } from 'react';
import { Label, Text, Tag } from 'react-konva';
import PropTypes from 'prop-types';

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
      name,
      onClick,
      onMouseIn,
      onMouseOut,
      showingChildren,
      x,
      y,
    } = this.props;

    const {
      bgClosedConclusionColor,
      bgOpenConclusionColor,
      bgRuleColor,
    } = this.state;

    const bgConclusionColor = showingChildren
      ? bgOpenConclusionColor
      : bgClosedConclusionColor;
    const conclusion = id.indexOf('c') !== -1;
    const textColor = conclusion && !showingChildren ? 'white' : 'black';

    return (
      <Label
        conclusion={conclusion}
        draggable
        id={name}
        key={id}
        name={name}
        onClick={onClick}
        onDragEnd={(e) => {
          const { updateParentState } = this.props;
          updateParentState(id, e.target.attrs.x, e.target.attrs.y);
        }}
        onMouseEnter={(e) => {
          onMouseIn(e.target.attrs.text);
        }}
        onMouseLeave={() => onMouseOut()}
        x={x}
        y={y}
      >
        <Tag
          fill={conclusion ? bgConclusionColor : bgRuleColor}
          stroke="black"
        />
        <Text
          align="center"
          fill={textColor}
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
  name: PropTypes.string,
  onClick: PropTypes.func,
  onMouseIn: PropTypes.func,
  onMouseOut: PropTypes.func,
  showingChildren: PropTypes.bool,
  updateParentState: PropTypes.func,
  x: PropTypes.number,
  y: PropTypes.number,
};
