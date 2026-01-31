/* ===== CONSTANTS ===== */
const LGHT=0, DARK=1;
const L_PWN=0, D_PWN=1, L_HRS=2, D_HRS=3, EMPTY=4, NOUSE=5;

const pcConv = new Int32Array([
   1, 3, 5, 7,  8,10,12,14, 17,19,21,23, 24,26,28,30,
  33,35,37,39, 40,42,44,46, 49,51,53,55, 56,58,60,62
]);

/* map 64-square index → 1..32 */
const sq32 = new Int32Array(64);
for(let i=0;i<32;i++) sq32[pcConv[i]] = i+1;

let side = LGHT;
let pc = new Int32Array(64);

let moveList = [], step = 0, curStep = 0, boardHistory = [];   // snapshot ของ board ทุก step

/* ===== CANVAS ===== */
const canvas = document.getElementById("board");
const ctx = canvas.getContext("2d");

canvas.style.width  = "320px";
canvas.style.height = "320px";
const COLW = 40;

/* ===== COLORS ===== */
const COL_NOUSE     = "#4f6b7a";
const COL_EMPTY     = "#2a3b47";
const COL_LGHT_PAWN = "#b3c2cc";
const COL_DARK_PAWN = "#0f1a22";
const COL_LGHT_RING = "#7f98a8";
const COL_DARK_RING = "#3a5566";

/* ===== BOOK DB ===== */
const bk_map = new Map();
let bkdbLoaded = 0;

loadBKDB();

/* ===== LOAD BOOK ===== */
async function loadBKDB(zipUrl="DB0508.zip", innerFile="DB0508.txt"){
  const res = await fetch(zipUrl);
  const zip = await JSZip.loadAsync(await res.blob());
  const txt = await zip.file(innerFile).async("text");
  const lines = txt.split("\n").map(x=>x.trim()).filter(x=>x.length>=21);

  for(const line of lines){
    const key = BigInt("0x"+line.substring(0,16));
    const mov = Number("0x"+line.substring(16,21));
    if(!bk_map.has(key)) bk_map.set(key,[]);
    bk_map.get(key).push(mov);
    bkdbLoaded++;
  }
  console.log("Book loaded:",bkdbLoaded);
}

/* ===== BOARD ENCODE ===== */
function boardEncode(){
  const encL = [4n,5n,6n,7n];   // L_PWN, D_PWN, L_HRS, D_HRS
  const encD = [5n,4n,7n,6n];   // swapped colors for dark-to-move
  let l = 0n;
  if(side === LGHT){
    for(let i=0;i<32;i++){
      const p = pc[pcConv[i]];
      l = (l * (p>=EMPTY ? 2n : 8n)) | (p>=EMPTY ? 0n : encL[p]);
    }
  }else{
    // reverse board order + reverse colors
    for(let i=31;i>=0;i--){
      const p = pc[pcConv[i]];
      l = (l * (p>=EMPTY ? 2n : 8n)) | (p>=EMPTY ? 0n : encD[p]);
    }
  }
  return l;
}


/* ===== MOVE HELPERS ===== */
const FM=x=>x&255;
const TO=x=>(x>>8)&255;

/* ===== BOARD RESET ===== */
function resetBoard(){
  for(let i=0;i<64;i++){
    pc[i]=(((i>>3)+(i&7))&1)?EMPTY:NOUSE;
  }
}

/* ===== INIT PIECES ===== */
function initPieces(){
  resetBoard();
  for(let y of [0,1,6,7]){
    const p=(y<2)?D_PWN:L_PWN;
    for(let x=0;x<8;x++){
      const i=y*8+x;
      if(pc[i]!==NOUSE) pc[i]=p;
    }
  }
  side=LGHT;
  updateSideRadios();draw();
}

/* ===== CLEAR ===== */
function clearBoard(){resetBoard();draw();}


/* ===== SIDE ===== */
function setSide(s){side=s;updateSideRadios();}
function flipSide(){side^=1;updateSideRadios();}
function updateSideRadios(){
  sideLight.checked=(side===LGHT);
  sideDark.checked =(side===DARK);
}

/* ===== REVERSE ===== */
function reverseBoard(){
  const t=pc.slice();
  for(let i=0;i<64;i++) pc[63-i]=swapColor(t[i]);
  flipSide();draw();
}

/* ===== SWAP COLOR ===== */
function swapColor(p){
  if(p===L_PWN) return D_PWN;
  if(p===D_PWN) return L_PWN;
  if(p===L_HRS) return D_HRS;
  if(p===D_HRS) return L_HRS;
  return p;
}

//============================================
//                MOVE REPLAY
//============================================

function parseMoves(str){
  return str
    .trim()
    .split(/\s+/)
    .map(m => {
      const isCap = m.includes('x');
      const [a,b] = m.split(isCap ? 'x' : '-');
      return {
        from: parseInt(a,10),
        to: parseInt(b,10),
        cap: isCap
      };
    });
}

function loadMoves(){
  initPieces();draw();   // หรือ drawPieces()
  const txt = moveInput.value.trim();
  if(!txt){
    moveList = [];
    curStep = 0;
    stepInfo.innerText = "ไม่มี move";
    return;
  }
  moveList = txt.split(/\s+/); // "25-12 8-11 24x15"
  curStep = 0;
  stepInfo.innerText = "โหลดแล้ว " + moveList.length + " moves";
}

function gotoStep(n){
  curStep = Math.max(0, Math.min(n, moveList.length));
  initPieces();
  for(let i = 0; i < curStep; i++) applyMove(moveList[i]);
  draw();
  stepInfo.innerText = "Step " + curStep + "/" + moveList.length;
}

function stepFirst(){ gotoStep(0);}
function stepBack() { gotoStep(curStep - 1);}
function stepNext() { gotoStep(curStep + 1);}
function stepLast() { gotoStep(moveList.length);}

function applyMove(mv){
  if(mv.includes("x")){
    // capture
    const [from,to] = mv.split("x").map(n=>parseInt(n,10));
    doCapture(from,to);
  }else{
    // normal move
    const [from,to] = mv.split("-").map(n=>parseInt(n,10));
    doMove(from,to);
  }
}

function doMove(fm32, to32){
  //console.log(curStep,fm32, to32);
  const fm = pcConv[fm32 - 1];
  const to = pcConv[to32 - 1];
  const p = pc[fm];
  if(p === EMPTY) return;
  pc[to] = p;
  pc[fm] = EMPTY;
  // promotion
  if     (p === L_PWN && to32 <=  3) pc[to] = L_HRS;
  else if(p === D_PWN && to32 >= 28) pc[to] = D_HRS;
}

function doCapture(fm32, to32){
  const fm = pcConv[fm32 - 1];
  const to = pcConv[to32 - 1];
  doMove(fm32, to32);
  p = fm > to ? ((fm&7) > (to&7) ? to + 9 : to + 7) : ((fm&7) > (to&7) ? to - 7 : to - 9);
  if (pc[p] !== EMPTY) pc[p] = EMPTY;
}

//============================================
//                BOOK PROBE
//============================================

function checkBook(){
  if(!bkdbLoaded) return;

  const info = document.getElementById("bkinfo");
  const betterBox = document.getElementById("betterBox");

  const key = BigInt(boardEncode());
  const hexKey = key.toString(16);
  document.getElementById("boardKey").value = hexKey;

  const list = bk_map.get(key);


  if(!list){
    info.innerText = "ยังไม่มีใครสอน";
    //betterBox.style.display = "none";   // hide
  }else{
    const cnt = new Map();
    for(const mv of list) cnt.set(mv,(cnt.get(mv)||0)+1);
    const arr = [...cnt.entries()].sort((a,b)=>b[1]-a[1]);

    let s = "";
    for(const [mv,n] of arr){
      const f = FM(mv), t = TO(mv);
      const pct = (n*100/list.length).toFixed(1);
      s += `${sqBySide(f)}-${sqBySide(t)} (${pct}%)\n`;
    }
    info.innerText = s;

    //betterBox.style.display = "block";
    submitBtn.style.display = "inline";   // show again for this position
    submitInfo.innerText = "";            // clear old message
  }
}

function sqBySide(cell){
  const s = sq32[cell];
  return (side === LGHT) ? s : (33 - s);
}


//============================================
//                DRAW BOARD
//============================================

function draw(){
  for(let y=0;y<8;y++)for(let x=0;x<8;x++){
    const idx=y*8+x;

    ctx.fillStyle=(pc[idx]===NOUSE)?COL_NOUSE:COL_EMPTY;
    ctx.fillRect(x*COLW,y*COLW,COLW,COLW);

    if(pc[idx]<=D_HRS){
      const cx=x*COLW+COLW/2, cy=y*COLW+COLW/2;
      const dark=pc[idx]&1;
      ctx.fillStyle=dark?COL_DARK_PAWN:COL_LGHT_PAWN;
      ctx.beginPath();
      ctx.arc(cx,cy,COLW/3,0,Math.PI*2);
      ctx.fill();

      if(pc[idx]>=2){
        ctx.strokeStyle=dark?COL_DARK_RING:COL_LGHT_RING;
        ctx.lineWidth=2;
        ctx.beginPath();
        ctx.arc(cx,cy,COLW/5,0,Math.PI*2);
        ctx.stroke();
      }
    }

    if(pc[idx]!==NOUSE){
      ctx.fillStyle="#8fa3b0";
      ctx.font="9px monospace";
      ctx.textAlign="right";
      ctx.textBaseline="top";
      ctx.fillText(sq32[idx],x*COLW+COLW-3,y*COLW+3);
    }
  }
  printBoardCode();
  checkBook();
}


//============================================
//                BOARD CODE
//============================================

const sym = ["o","x","@","#","."]; // L_PWN, D_PWN, L_HRS, D_HRS, EMPTY

function printBoardCode(){
  let s = "";
  for(let i=0;i<32;i++){
    const p = pc[ pcConv[i] ];
    s += sym[p <= EMPTY ? p : EMPTY];
  }
  document.getElementById("boardCode").value = s;
  document.getElementById("bkinfo").textContent = "";
}

/*function boardToCode(){
  let s = "";
  for(let i=0;i<32;i++){
    const c = pcConv[i];   // your existing convert
    const p = pc[c];
    s += sym[p];
  }
  document.getElementById("boardCode").value = s;
}
*/

// read code and draw board
function loadFromCode(){
  const txt = document.getElementById("codeInput").value.trim();
  clearBoard();
  const n = Math.min(txt.length, 32);
  for(let i=0;i<n;i++){
    const c  = pcConv[i];
    const ch = txt[i];
    const v  = sym.indexOf(ch);
    if(v !== -1) pc[c] = v;
  }
  draw();
}

function copyBoardCode(){
  const txt = document.getElementById("boardCode").value;
  prompt("Plese copy this:", txt);
}

//============================================
//                FETCH LOG
//============================================

document.addEventListener("DOMContentLoaded", ()=>{
  submitBetterMove(false);   // false = ไม่ต้อง alert
});

function submitBetterMove(showAlert = true){
  const moveType = document.getElementById("moveType");

  fetch("https://chnp.co.th/makhos/bettermove.php" +
        "?code=" + encodeURIComponent(boardCode.value) +
        "&side=" + side  +
        "&type=" + encodeURIComponent(moveType.value) +
        "&move=" + encodeURIComponent(betterMove.value)
  )
  .then(r => r.text())
  .then(t => {
    if(showAlert){
      alert("ส่งข้อมูลเรียบร้อยแล้ว ขอบคุณครับ");
    }
    submitInfo.innerText = t;
    betterMove.value = "";
  });
}

//============================================
//                ON CLICK
//============================================

/* ===== EDIT BY CLICK ===== */
let selectedPiece=L_PWN;

document.querySelectorAll('input[name="piece"]').forEach(r=>{
  r.onchange = ()=>{
    selectedPiece = Number(r.value);
  };
});

canvas.onclick = e=>{
  const x = (e.offsetX / COLW) | 0;
  const y = (e.offsetY / COLW) | 0;
  const i = y*8 + x;

  if(pc[i] === NOUSE) return;

  // click on a piece → pick it
  if(pc[i] <= D_HRS){
    const p = pc[i];
    pc[i] = EMPTY;
    setPieceRadio(p);   // select radio to that piece
  }
  // click on empty → place selected piece
  else{
    pc[i] = selectedPiece;

    // side becomes opposite of placed piece
    side = (selectedPiece & 1) ? LGHT : DARK;
    document.getElementById("sideLight").checked = (side === LGHT);
    document.getElementById("sideDark").checked  = (side === DARK);
  }

  draw();
};


function setPieceRadio(p){
  const radios = document.getElementsByName("piece");
  for(let r of radios){
    if(Number(r.value) === p){
      r.checked = true;
      break;
    }
  }
  selectedPiece = p;
}


/* ===== START ===== */
resetBoard();
draw();
