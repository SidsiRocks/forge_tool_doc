const stage = new Stage()

var cur_height = 100
const line_height = 20
const fontSize = 16

const seqMap = {}

function printText(txt){
    txt_width = (fontSize * txt.length)
    let obj = new TextBox({
        text:txt,
        coords:{x:50+txt_width/4,y:cur_height},
        color:"black",
        fontSize:fontSize
    })
    stage.add(obj)
    cur_height += line_height
    return Object.getOwnPropertyNames(obj)
}

components.tuples().forEach((tuple) => {
    let atoms = tuple.atoms();
    let seq_obj = atoms[0].toString();
    let component = atoms[2].toString();

    if(!seqMap[seq_obj]){
        seqMap[seq_obj] = [];
    }
    seqMap[seq_obj].push(component);
})

printText("text")
printText(JSON.stringify(seqMap))
stage.render(svg,document)
