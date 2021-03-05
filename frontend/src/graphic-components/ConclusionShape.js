import React from 'react';
import { Label, Text, Tag, Rect } from 'react-konva';

function ConclusionShape(props) {

  return (
    <Label key={props.name} name={props.name} id={props.name} onClick={props.onClick} onDragEnd={props.onDragEnd} onDragStart={props.onDragStart} draggable y={props.y} x={props.x} cornerRadius={100}>
        <Tag fill='gray' stroke='black'></Tag>
        <Text text={props.children} fontSize={15} lineHeight={1.2} padding={10} fill={'black'}></Text>
    </Label>
  );
}

export default ConclusionShape;