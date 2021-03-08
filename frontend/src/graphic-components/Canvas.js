import React, { Component } from 'react';
import { Stage, Layer } from 'react-konva';
import RuleShape from './RuleShape';
import ConclusionShape from './ConclusionShape';

export default class Canvas extends Component {
  constructor(props) {
    super(props);

    var numberOfNodes = ((this.props.dot.match(/label/g) || []).length)/2;
    var nodes = new Array(numberOfNodes);
    var edges = [];
    const lines = this.props.dot.slice(this.props.dot.indexOf("{")+1,this.props.dot.indexOf("}")-2).replace(/(\n|\t)/gm, "").split(';');
    for(var i in lines){
      var line = lines[i];
      if(line.search("label") !== -1){
        if(line.split("[")[0].search('c') === -1){
          var node = {
            id: line.split("[")[0].trim().slice(1,-1),
            rule: line.slice(lines[i].indexOf("label")+9,line.lastIndexOf('"')),
            ref: React.createRef(),
            refConclusion: React.createRef(),
            children: [],
            clicked: false,
          }
          nodes[parseInt(node.id)] = node;
        }
        else {
          const id = line.split("[")[0].trim().slice(1,-1);
          nodes[parseInt(id)].conclusion = line.slice(lines[i].indexOf("label")+9,line.lastIndexOf('"'));
        }
      }
      else if(line.search("->") !== -1){
        const edge_nodes = line.split("->").map(element => {
          return element.trim().replaceAll('"','').replace("c",'')
        });
        edges.push({ from: edge_nodes[0], to: edge_nodes[1] });
        if(edge_nodes[0] !== edge_nodes[1]){
          nodes[edge_nodes[1]].children.push(edge_nodes[0]);
        }
      }
    }

    this.state = {
      stageScale: 1,
      stageX: 0,
      stageY: 0,
      dot: this.props.dot,
      proofNodes: nodes,
      proofEdges: edges,
      showingNodes: [],
      shapeRef: React.createRef()
    }
  }

  handleWheel = e => {
    e.evt.preventDefault();

    const scaleBy = 1.02;
    const stage = e.target.getStage();
    const oldScale = stage.scaleX();
    const mousePointTo = {
      x: stage.getPointerPosition().x / oldScale - stage.x() / oldScale,
      y: stage.getPointerPosition().y / oldScale - stage.y() / oldScale
    };

    const newScale = e.evt.deltaY > 0 ? oldScale * scaleBy : oldScale / scaleBy;


    this.setState({
      stageScale: newScale,
      stageX:
        -(mousePointTo.x - stage.getPointerPosition().x / newScale) * newScale,
      stageY:
        -(mousePointTo.y - stage.getPointerPosition().y / newScale) * newScale
    });
  };

  onClick = e => {
    const myIndex = e.target.parent.attrs.id;
    if(this.state.proofNodes[myIndex].clicked) return;
    var newNodes = [
      <RuleShape 
        ref={this.state.proofNodes[myIndex].refConclusion}
        key={(this.state.proofNodes[myIndex].id)}
        id={(this.state.proofNodes[myIndex].id)}
        name={this.state.proofNodes[myIndex].id}
        x={e.target.parent.attrs.x}
        y={e.target.parent.attrs.y+42}>
          {this.state.proofNodes[myIndex].rule}
        </RuleShape>
    ]
    for(var child in this.state.proofNodes[myIndex].children){
      const index = this.state.proofNodes[myIndex].children[child];
      newNodes.push(
      <ConclusionShape 
      onClick={(e2) => this.onClick(e2)}
      id={(index)}
      name={(index)}
      key={(index)} y={e.target.parent.attrs.y+84} x={e.target.parent.attrs.x+(child * 200)}>
        {this.state.proofNodes[index].conclusion}
      </ConclusionShape>)
    }
    this.setState({
      showingNodes: [...this.state.showingNodes, ...newNodes]
    })
    var newProofNodes = this.state.proofNodes;
    newProofNodes[myIndex].clicked = true;
    this.setState({proofNodes: newProofNodes});
  }


  componentDidMount(){
    this.setState({
      showingNodes: [<ConclusionShape 
      ref={this.state.proofNodes[0].refConclusion}
      key={(this.state.proofNodes[0].id)+'c'}
      id={(this.state.proofNodes[0].id)+'c'}
      onClick={(e) => this.onClick(e)}
      name={this.state.proofNodes[0].id}
      y={10} x={window.innerWidth * 0.35}>
        {this.state.proofNodes[0].conclusion}
      </ConclusionShape>,]
    })
  }

  render (){
    return (
      <Stage width={window.innerWidth * 0.9} height={window.innerHeight * 0.7} 
      onWheel={this.handleWheel}
      scaleX={this.state.stageScale}
      scaleY={this.state.stageScale}
      x={this.state.stageX}
      y={this.state.stageY}>
          <Layer>
            {this.state.showingNodes.map(element => element)}
          </Layer>
      </Stage>
    );
  }
}