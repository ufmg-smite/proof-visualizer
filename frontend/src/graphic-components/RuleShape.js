import React from 'react';
import { Label, Text, Tag } from 'react-konva';

function RuleShape(props) {
  return (
    <Label onDragEnd={props.onDragEnd} onDragStart={props.onDragStart} draggable y={props.y} x={props.x}>
        <Tag fill='white' stroke='black'></Tag>
        <Text text={props.children} fontSize={15} lineHeight={1.2} padding={10} fill={'black'}></Text>
    </Label>
  );
}

export default RuleShape;