import React, { Component } from 'react';
import { Label, Text, Tag, Group } from 'react-konva';
import PropTypes from 'prop-types';

function textColorFromBg(bgColor) {
  const color = bgColor.charAt(0) === '#' ? bgColor.substring(1, 7) : bgColor;
  const r = parseInt(color.substring(0, 2), 16);
  const g = parseInt(color.substring(2, 4), 16);
  const b = parseInt(color.substring(4, 6), 16);
  return r * 0.299 + g * 0.587 + b * 0.114 > 150 ? '#000000' : '#ffffff';
}

export default class Node extends Component {
  overlap = (node) => {
    const { x, y } = this.props;
    const overlapXleftPointInside =
      node.props.x > x - 25 && node.props.x < x + 325;
    const overlapXrightPointInside =
      node.props.x + 300 > x - 25 && node.props.x + 300 < x + 325;
    const overlapX = overlapXleftPointInside || overlapXrightPointInside;
    const overlapY =
      (node.props.y > y - 25 && node.props.y < y + 60) ||
      (node.props.y + 30 > y - 25 && node.props.y + 30 < y + 60);

    if ((overlapX && overlapY) || (x === node.props.x && y === node.props.y)) {
      return true;
    }
    return false;
  };

  render() {
    const {
      rule,
      conclusion,
      id,
      onClick,
      setCurrentText,
      setFocusText,
      showingChildren,
      x,
      y,
      hasChildren,
    } = this.props;

    const bgClosedColor = '#2b2d42';
    const bgOpenColor = '#8d99ae';

    const bgColor =
      showingChildren || !hasChildren ? bgOpenColor : bgClosedColor;

    return (
      <Group
        draggable
        id={id}
        key={id}
        onDragMove={(e) => {
          const { updateNodeState } = this.props;
          updateNodeState(id, e.target.attrs.x, e.target.attrs.y);
        }}
        x={x}
        y={y}
      >
        <Label
          onClick={(e) =>
            e.evt.button === 2
              ? setCurrentText(e.target.attrs.text)
              : onClick({ id, x, y })
          }
          onMouseEnter={(e) => {
            setFocusText(e.target.attrs.text);
          }}
          onMouseLeave={() => setFocusText('')}
          x={0}
          y={0}
        >
          <Tag fill={bgColor} stroke="black" />
          <Text
            align="center"
            fill={textColorFromBg(bgColor)}
            fontSize={15}
            height={35}
            padding={10}
            text={conclusion}
            width={300}
          />
        </Label>
        <Label
          x={0}
          y={35}
          onClick={(e) =>
            e.evt.button === 2
              ? setCurrentText(e.target.attrs.text)
              : onClick({ id, x, y })
          }
          onMouseEnter={(e) => {
            setFocusText(e.target.attrs.text);
          }}
          onMouseLeave={() => setFocusText('')}
        >
          <Tag fill={bgColor} stroke="black" />
          <Text
            align="center"
            fill={textColorFromBg(bgColor)}
            fontSize={15}
            height={35}
            padding={10}
            text={rule}
            width={300}
          />
        </Label>
      </Group>
    );
  }
}

Node.propTypes = {
  rule: PropTypes.string,
  conclusion: PropTypes.string,
  id: PropTypes.string,
  onClick: PropTypes.func,
  setFocusText: PropTypes.func,
  setCurrentText: PropTypes.func,
  showingChildren: PropTypes.bool,
  updateNodeState: PropTypes.func,
  x: PropTypes.number,
  y: PropTypes.number,
  hasChildren: PropTypes.bool,
};
