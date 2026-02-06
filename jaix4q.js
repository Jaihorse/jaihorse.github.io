/*
============================================================
  Sunhorse - Version 2025.12 - jaix4.js from jai09.js
------------------------------------------------------------
  Author: Jaroonsak Wangviwat
  Last Updated: December 2025
  Project: Web-based Checkers (Sunhorse)

  Description:
    - Based on Jaihorse js030523.java and Sunhorse jai03.js
    - Optimized core evaluation routine (lightweight)
    - Supports Transposition Table (TT) for faster search
    - Integrated 4P Endgame Database with fallback defaults
    - Modern HTML5 front-end using Canvas
    - Adaptive UI: responsive board and piece sizing
    - Game Levels: win to level up, lose to level down
    - Use fixed unsigned integer 32 bit for arrays
    - Use 64 bit Zobrist key for both TT and Endgame DB.
    - Display remaining time for both side.
    - Animation for piece move, init board, selected piece
    - Extra depth if time thinking left
    - Opening book integration
    - Renaming variables to more understandable

  Notes:
    - Endgame DB is zipped and renamed to .bmp file to hide
    - Opening Book uses 3-bit piece and 1-bit empty board encoding

============================================================

Technical Notes:

Use Zobrist key for both TT and Endgame DB.
Zobrist key is 64 bits to avoid key duplication.

VERSTIONS
----------
x4h Dec-2025 hand animation
x4s Jan-2026 sound
x4q Feb-2026 fixed search, tt, eg, eval score

*/

"use strict";

const CODE_VERSION = "x4q";
const CODE_DATE = "2602061645";

//========== SWITCH ==========
const DEBUG = false;    // debug mode to disable random
const USE_BK = true;
const USE_TT = true;
const USE_EG = true;
const BASE_DEPTH = 10;   // depth for level 1, depth 11 takes 5-10 sec per move
const MAX_LEVEL = 2;

let level = 1, prevLevel = level; // start level
let targetDepth = BASE_DEPTH;     // actual search depth

/* ===== GAME / PIECE CONSTANTS ===== */
const GS_LGHT=0, GS_LMOV=1, GS_DARK=2, GS_NONE=3;
let gameState = GS_LGHT, gameCount = 0, gameStartTime = 0;
let moveHistoryStr = "", gameResultStr = "", winStreak = 0, loseStreak = 0;

const LGHT =0, DARK =1;
const L_PWN=0, D_PWN=1, L_HRS=2, D_HRS=3, EMPTY=4, NOUSE=5;
const X_PWN=0, X_HRS=2;

let L_PWN_cnt=0, D_PWN_cnt=0, L_HRS_cnt=0, D_HRS_cnt=0;
let pieceCount=0, pieceCode=0; // [L_HRS] [L_PWN] [D_HRS] [D_PWN]

//

const pc_init = new Int32Array([
  5, 1, 5, 1, 5, 1, 5, 1,
  1, 5, 1, 5, 1, 5, 1, 5,
  5, 4, 5, 4, 5, 4, 5, 4,
  4, 5, 4, 5, 4, 5, 4, 5,
  5, 4, 5, 4, 5, 4, 5, 4,
  4, 5, 4, 5, 4, 5, 4, 5,
  5, 0, 5, 0, 5, 0, 5, 0,
  0, 5, 0, 5, 0, 5, 0, 5
]);

/*/

const pc_init = new Int32Array([  // 6p
  5, 1, 5, 4, 5, 4, 5, 4,
  0, 5, 4, 5, 4, 5, 4, 5,
  5, 4, 5, 4, 5, 2, 5, 1,
  4, 5, 1, 5, 4, 5, 4, 5,
  5, 4, 5, 4, 5, 0, 5, 4,
  1, 5, 4, 5, 4, 5, 4, 5,
  5, 4, 5, 4, 5, 4, 5, 4,
  4, 5, 4, 5, 4, 5, 4, 5
]);

//

const pc_init = new Int32Array([  // 2p
  5, 4, 5, 1, 5, 1, 5, 4,
  0, 5, 4, 5, 4, 5, 4, 5,
  5, 4, 5, 4, 5, 0, 5, 4,
  1, 5, 4, 5, 4, 5, 4, 5,
  5, 4, 5, 4, 5, 4, 5, 4,
  4, 5, 0, 5, 0, 5, 4, 5,
  5, 4, 5, 0, 5, 4, 5, 4,
  4, 5, 4, 5, 3, 5, 4, 5
]);

//

const pc_init = new Int32Array([  // 2p
  5, 4, 5, 4, 5, 4, 5, 4,
  4, 5, 4, 5, 4, 5, 3, 5,
  5, 4, 5, 4, 5, 4, 5, 4,
  2, 5, 1, 5, 4, 5, 1, 5,
  5, 4, 5, 4, 5, 4, 5, 4,
  4, 5, 4, 5, 0, 5, 4, 5,
  5, 4, 5, 4, 5, 4, 5, 4,
  4, 5, 4, 5, 4, 5, 4, 5
]);

/*/

let pc = new Int32Array(pc_init);

const pcsq_init = new Int32Array([
   0,  0,  0,  0,  0,  0,  0,  0,
   8,  0, 29,  0, 29,  0, 29,  0,
   0, 16,  0, 16,  0, 16,  0,  6,
   4,  0,  5,  0,  5,  0, (5), 0,   // 30
   0, (2), 0,  9,  0,  7,  0, (6),  // 33,39
  (1), 0,  6,  0,  6,  0,  6,  0,   // 40
   0,  3,  0,  4,  0,  4,  0,  3,
   0,  0,  9,  0,  7,  0,  6,  0
]);

const pcsq_end = new Int32Array([
   0,  0,  0,  0,  0,  0,  0,  0,
   8,  0, 29,  0, 29,  0, 29,  0,
   0, 16,  0, 16,  0, 16,  0, 11,
  15,  0, 10,  0, 10,  0, 10,  0,
   0,  6,  0,  6,  0,  6,  0,  7,
   4,  0,  3,  0,  3,  0,  3,  0,
   0,  1,  0,  1,  0,  1,  0,  2,
   0,  0,  0,  0,  0,  0,  0,  0
]);

let pcsq = new Int32Array(pcsq_init);
//let pcsq32 = new Array(32).fill(0);
//let pcsq_end32 = new Array(32).fill(0);

const mailbox = new Int32Array([
  -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
  -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
  -1,  0,  1,  2,  3,  4,  5,  6,  7, -1,
  -1,  8,  9, 10, 11, 12, 13, 14, 15, -1,
  -1, 16, 17, 18, 19, 20, 21, 22, 23, -1,
  -1, 24, 25, 26, 27, 28, 29, 30, 31, -1,
  -1, 32, 33, 34, 35, 36, 37, 38, 39, -1,
  -1, 40, 41, 42, 43, 44, 45, 46, 47, -1,
  -1, 48, 49, 50, 51, 52, 53, 54, 55, -1,
  -1, 56, 57, 58, 59, 60, 61, 62, 63, -1,
  -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
  -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
]);

const mailbox64 = new Int32Array([
  21, 22, 23, 24, 25, 26, 27, 28,
  31, 32, 33, 34, 35, 36, 37, 38,
  41, 42, 43, 44, 45, 46, 47, 48,
  51, 52, 53, 54, 55, 56, 57, 58,
  61, 62, 63, 64, 65, 66, 67, 68,
  71, 72, 73, 74, 75, 76, 77, 78,
  81, 82, 83, 84, 85, 86, 87, 88,
  91, 92, 93, 94, 95, 96, 97, 98
]);

const offset = new Int32Array([-11,-9,11,9]);

const pcConv = new Int32Array([
   1, 3, 5, 7,  8,10,12,14, 17,19,21,23, 24,26,28,30,
  33,35,37,39, 40,42,44,46, 49,51,53,55, 56,58,60,62
]);
const pcFlip = new Int32Array([
 62,60,58,56, 55,53,51,49, 46,44,42,40, 39,37,35,33,
 30,28,26,24, 23,21,19,17, 14,12,10, 8,  7, 5, 3, 1
]);
const cellToNum = new Int32Array(64).fill(-1);

/* ===== ENGINE / STACK STATE ===== */
let side=LGHT, xside=DARK, ply, maxply, compFirst;
let moveCount=0, drawCount=0, lastmove, lastmoveCap=0;
let follow_pv=false, bCompBusy=false;

const PWN_VAL_default=100, HRS_VAL_default=190;
let PWN_VAL=PWN_VAL_default, HRS_VAL=HRS_VAL_default, HRS_VAL_D=HRS_VAL_default;

const MOVE_STACK=256, HIST_STACK=64;
const MMOVE = 0x000000|0, MCAPTURE = 0x020000|0, MCAP_PWN = 0x020000|0, MCAP_HRS = 0x030000|0, MPROMOTE = 0x040000|0, MSKIP = 0x080000|0;

let gen_dat = new Int32Array(MOVE_STACK);
let gen_begin = new Int32Array(HIST_STACK), gen_end = new Int32Array(HIST_STACK), gen_score = new Int32Array(MOVE_STACK);
let hist_dat = new Int32Array(HIST_STACK), hist_cap = new Int32Array(HIST_STACK);

/* ===== mov_val: flat typed array + helpers ===== */
const MOV_VAL_WIDTH = 64, MOV_VAL_SIZE = MOV_VAL_WIDTH * MOV_VAL_WIDTH;
let mov_val_flat = new Int16Array(MOV_VAL_SIZE);
const MOV_INDEX = (to,from) => (to << 6) + from;
const MOV_VAL = (to,from) => mov_val_flat[MOV_INDEX(to,from)];
const ADD_MOV_VAL = (to,from,delta) => { mov_val_flat[MOV_INDEX(to,from)] = (mov_val_flat[MOV_INDEX(to,from)] + delta); };

/* ===== PV triangular storage (simple JS arrays kept) ===== */
let pv = new Array(HIST_STACK), pv_lgth = new Array(HIST_STACK);


/******************** INIT ************************
 
             ####  ##   ##  ####  ######
              ##   ###  ##   ##     ## 
              ##   ## # ##   ##     ##
              ##   ##  ###   ##     ##  
             ####  ##   ##  ####    ##

 *************************************************/

function init(){ 
  initArrays(); loadImages(); loadBKDB(); loadEGDB(); waitForAssets();
}

function initArrays() {
  gen_dat.fill(0); gen_score.fill(0); gen_begin.fill(0); gen_end.fill(0); 
  hist_dat.fill(0); hist_cap.fill(0); pv_lgth.fill(0);
  mov_val_flat.fill(0);
  for (let i=0;i<HIST_STACK;i++){ pv[i]=new Array(HIST_STACK).fill(0); }
  for (let i=0;i<32;i++) cellToNum[pcConv[i]]=i+1; // cell number text on board
  initDomRefs();
  initZobrist();
}

function waitForAssets() { // wait for images, egdb, and bkdb loading complete
  if (!imagesLoaded || egdbLoaded===0 || bkdbLoaded===0) { 
    setTimeout(waitForAssets, 200); return; 
  }
  fetch(VISIT_LOG_URL + "level=" + CODE_DATE + "&result=" +
      egdbLoaded + "&moves=" + bkdbLoaded);
  startGame();
}

async function startGame() {
  bCompBusy = true;
  gameStartTime = performance.now(); 
  gameCount++; compFirst = !(gameCount & 1); moveHistoryStr = "";
  initEngineState(); await warmUp(500);
  pieceSelected = false; selectedCell = -1; selectedTo = -1;
  dragX = dragY = 0; wasDragging = false;
  initCellOffsets(); drawBoard(); drawPieces(); 

  message("Jaihorse makhos.com"); version(CODE_VERSION+" level "+level); 
  showNewGame(false); showStyleIcon(); await warmUp(500); 
  hideTimers(); await warmUp(500);

  // Dark gives a piece if player lose level 0 
  await showOverlayText("Level "+level, 500);
  if (level===0 && prevLevel===0) {
    await showOverlayText("ต่อให้", 250);
    //const cell = pick(8, 10, 12); 
    await animateGivePiece();
    //pc[cell]=EMPTY; 
    drawPieces(); await warmUp(500); 
  }
  resetClock(); updateTimeDisplay();
  showStyleIconIcon(true);
  await showOverlayText(compFirst ? "คุณเดินหลัง" : "คุณเดินก่อน", 250);

  if (compFirst) { // if dark moves first
    const fm = 14, to = 21, mv = fm | (to << 8);
    await animateMove(mv);
    pc[to] = pc[fm]; pc[fm] = EMPTY; drawPieces(); 
  }
  recalcPieceCounts(); 

  bCompBusy = false;
}

async function warmUp(ms) {
  //await holdMs(ms);
  const t0 = performance.now();
  // 1. Force image decode + GPU upload
  for (let i = 0; i < images[IMG_HAND].length; i++) {
    const img = images[IMG_HAND][i];
    initHandCanvas(img, img.width, img.height);  // push into GPU
    handCtx.clearRect(0, 0, img.width, img.height);
  }
  // 2. Warm animation pipeline
  while (performance.now() - t0 < ms) {
    await runPhase(16, t => { drawHand(0, 0); }); // draw offscreen 
  }
  //drawPieces(); // Warm drawPieces
  await holdMs(); // small settle time
}

function initEngineState() {
  side=LGHT; xside=DARK; gameState=GS_LGHT;
  moveCount=0; drawCount=0; lastmove=MMOVE; lastmoveCap=0;
  ply=0; pv_lgth[0]=0; pc.set(pc_init); pcsq.set(pcsq_init);
  gen_begin[0]=0; gen(GEN_ALL);
  randomizeValues(); ttClear(); 
}

async function showOverlayText(text, ms) {
  if (DEBUG) ms = 20;
  hideOverlay(); await warmUp(ms); 
  showOverlay(text); await warmUp(ms * 2); 
  hideOverlay(); await warmUp(ms);
}

function showOverlay(text) { overlayText.textContent = text; overlayText.classList.add("show"); }
function hideOverlay() { overlayText.classList.remove("show"); }

function randomizeValues(){
  if(DEBUG)return; //disable random to get the same results for testing

  PWN_VAL=PWN_VAL_default; HRS_VAL=HRS_VAL_default; HRS_VAL_D=HRS_VAL_default;
  PWN_VAL  += pick(-5, 0, 5);
  HRS_VAL_D+= pick(-5, 0, 5);
  HRS_VAL  += pick(10,20,30);

  pcsq[30] += pick(0, 1, 2);
  pcsq[33] += pick(0, 1, 2);
  pcsq[39] += pick(0, 1, 2);
  pcsq[40] += pick(0, 1, 2);

  pcsq[35] += pick(0,-3,-6);
  pcsq[pick(49,51,53)] += 4;

/* ====== 64 ======
     1   3   5   7
   8  10  12  14
    17  19  21  23
  24  26  28  30
    33  35  37  39
  40  42  44  46
    49  51  53  55
  56  58  60  62
  ================ */
}

function recalcPieceCounts(){
  L_PWN_cnt=D_PWN_cnt=L_HRS_cnt=D_HRS_cnt=0;
  let pcCnt=0;
  for(let i=0;i<32;i++){
    const q=pcConv[i], p=pc[q];
    if(p===EMPTY) continue;
    pcCnt++;
    switch (p) {
      case L_PWN: L_PWN_cnt++; break; case D_PWN: D_PWN_cnt++; break; 
      case L_HRS: L_HRS_cnt++; break; case D_HRS: D_HRS_cnt++; break;
    }
  }
  pieceCount = pcCnt;
}

function updatePieceCode(){
  pieceCode = L_HRS_cnt*1000 + L_PWN_cnt*100 + D_HRS_cnt*10 + D_PWN_cnt; 
}

function chance(p){ return Math.random() < p; }
function pick(a,b,c){
  const r = Math.random();
  return r < 0.3 ? a : r < 0.7 ? b : c;
}


/***************** RENDER & INPUT ********************
 
         ####  ##    ##   ####     #####  #####
          ##   ###  ###  ##  ##   ##      ##
          ##   ## ## ##  #######  ## ###  ####
          ##   ##    ##  ##   ##  ##  ##  ##
         ####  ##    ##  ##   ##   #####  #####

 *****************************************************/

// IMPORTANT!!! Change images based on side to move first. 23-Jan-2026
// If computer moves first, then the board should be visually inverted:
// use D_ images as the “player side”, but internally keep LGHT/DARK logic unchanged.
// only swap which image index is used, not the game logic.

//const L_PWN_MOV=6,D_PWN_MOV=7,L_HRS_MOV=8,D_HRS_MOV=9;
const L_ICO=6,D_ICO=7,SEL_BLACK=8,SEL_WHITE=9,PMOV_SHIFT=0; //(L_PWN_MOV-L_PWN);
const imageFiles = [
  // classic (0)
  [ "mLPWN256_128.png","mDPWN256_128.png","mLHRS256_128.png","mDHRS256_128.png",
    "brddrk.jpg","brdwht.jpg",
    //"mLPWNmov_64.png","mDPWNmov_64.png","mLHRSmov_64.png","mDHRSmov_64.png",
    //"mLPWN256_128.png","mDPWN256_128.png","mLHRS256_128.png","mDHRS256_128.png",
    "mL_ico.png", "mD_ico.png", "selBlack.png", "selWhite.png" ],
  // modern (1)
  [ "wLPWN256r_64.png","wDPWN256r_64.png","wLHRS256r_64.png","wDHRS256r_64.png",
    "wEMPTY.png","wNOUSE.png",
    //"wLPWNmov_64.png","wDPWNmov_64.png","wLHRSmov_64.png","wDHRSmov_64.png",
    //"wLPWN256_64.png","wDPWN256_64.png","wLHRS256_64.png","wDHRS256_64.png",
    "wL_ico.png", "wD_ico.png", "selBlack.png", "selBlack.png" ],
  // checkers (2)
  [ "cLPWN256_64.png","cDPWN256_64.png","cLHRS256_64.png","cDHRS256_64.png",
    "brddrk.jpg","brdwht.jpg",
    //"cLPWNmov_64.png","cDPWNmov_64.png","cLHRSmov_64.png","cDHRSmov_64.png",
    //"cLPWN256_64.png","cDPWN256_64.png","cLHRS256_64.png","cDHRS256_64.png",
    "cL_ico.png", "cD_ico.png", "selBlack.png", "selBlack.png" ],
  // hand animation
  [ "handMov1_64.png","handMov2_64.png",
    "handCap1_64.png","handCap2_64.png", "handCapW_64.png",
    "girlMov3_64.png","girlCap3_64.png" ],
];

// Hands
const IMG_HAND = 3, HAND_MOV1 = 0, HAND_MOV2 = 1, HAND_CAP1 = 2, HAND_CAP2 = 3, HAND_CAPW = 4,
      GIRL_MOV1 = 5, GIRL_CAP1 = 6;
const HAND_GRIP_OFFSET_X = 400, HAND_GRIP_OFFSET_Y = 150; // all images width 800

// Styles
const IMAGE_GROUP = imageFiles.length;
const STYLE_COUNT = 3, STYLE_CLASSIC = 0, STYLE_MODERN = 1, STYLE_CHECKERS = 2;

let doc=document;
let boardWrapper;
let boardCanvas, boardCtx, pieceCanvas, pieceCtx, animeCanvas, animeCtx, handCanvas, handCtx;
let messageElm, versionElm, footerElm, styleElm, styleCompElm, soundElm, cellNumElm, newGameElm;
let compTimeElm, playerTimeElm, overlayText, cellNumEnabled=true;
let images={};
let boardStyle=STYLE_CLASSIC; // 3 styles: 0=classic 1=modern 2=checkers
let pieceSelected=false, selectedCell=-1, selectedTo=-1;
let COLW=1, CANVAS_W=1, CANVAS_H=1;
let cellX = new Int16Array(64), cellY = new Int16Array(64); // cell position
let cellErrX = [], cellErrY = []; // small offsets of each cell

function initDomRefs(){
  boardWrapper = $("boardWrapper");
  boardCanvas  = $("boardCanvas");
  boardCtx     = boardCanvas.getContext("2d");
  pieceCanvas  = $("pieceCanvas");
  pieceCtx     = pieceCanvas.getContext("2d");
  animeCanvas  = $("animeCanvas");
  animeCtx     = animeCanvas.getContext("2d");
  //pmovCanvas   = doc.createElement("canvas");
  //pmovCtx      = pmovCanvas.getContext("2d");
  handCanvas   = doc.createElement("canvas");
  handCtx      = handCanvas.getContext("2d");
  messageElm   = $("message");
  versionElm   = $("version");
  newGameElm   = $("newgame");
  styleElm     = $("styleSwitch");
  styleCompElm = $("styleComp");
  soundElm     = $("soundSwitch");
  cellNumElm   = $("cellNumSwitch");
  footerElm    = $("footer");
  compTimeElm  = $("compTime");
  playerTimeElm= $("playerTime");
  overlayText  = $("overlayText");
  showNewGame(false); showStyleIconIcon(false);
  soundElm.textContent = "🔈";
  animeCtx.imageSmoothingEnabled = false;
  handCtx.imageSmoothingEnabled = false;
  /*
  // text style of checkers cell numbers
  pieceCtx.textAlign = "right";
  pieceCtx.textBaseline = "top";
  pieceCtx.strokeStyle = "rgba(255,255,255,.8)";
  pieceCtx.fillStyle = "rgba(0,0,0,.7)";
  pieceCtx.lineWidth = 2;
  */
}

function $(id){ return doc.getElementById(id); }


/* ===== Load All Images ===== */

let imagesLoaded = false;

function loadImages() {
  showOverlay("Loading...");
  let total=0, loaded=0;
  for(let s=0; s<IMAGE_GROUP; s++) total+=imageFiles[s].length;
  for(let s=0; s<IMAGE_GROUP; s++){
    images[s]=[];
    for(let p=0; p<imageFiles[s].length; p++){
      const img = images[s][p] = new Image();
      img.onload = () => {
        if(++loaded === total){
          imagesLoaded = true;
          allImagesLoaded();
        }
      };
      img.src = imageFiles[s][p];
    }
  }
}

function allImagesLoaded() {
  resizeAllCanvases();
  installPointerHandlers();
  window.addEventListener('resize', resizeAllCanvases);
}

/* ===== Resize canvases ===== */
function resizeAllCanvases() {
    // Compute board size in CSS pixels (multiple of 8)
    let size = computeBoardCssSize();
    const dpr = window.devicePixelRatio || 1;

    size = Math.floor(size / 8) * 8; // Round to multiples of 8
      
    // Set board wrapper CSS
    boardWrapper.style.width  = size + "px";
    boardWrapper.style.height = size + "px";

    // Resize canvases: backing pixels = CSS pixels × dpr
    [boardCanvas, pieceCanvas, animeCanvas].forEach(canvas => {
    //[pieceCanvas, animeCanvas].forEach(canvas => {
        canvas.width  = size * dpr;
        canvas.height = size * dpr;
        canvas.style.width  = size + "px";
        canvas.style.height = size + "px";
    });

    COLW = pieceCanvas.width / 8; // COLW in backing pixels
    CANVAS_W = CANVAS_H = pieceCanvas.width; // CANVAS width and height
    //cellNumberStyle();
    showStyleIcon();
    initCellOffsets();
    drawBoard();
    drawPieces();
    animeCanvas.style.boxShadow = "0 0 2px 2px #333";
}

/* ===== Compute board CSS size (multiple of 8) ===== */
function computeBoardCssSize() {
    let w = window.innerWidth, h = window.innerHeight;
    if (w > h * 80 / 95) w = h; else w = w * 95 / 80;
    return Math.floor(w * 0.8); // 80% of space
}

function initCellOffsets() { 
  let v = 0.05; // default 5% offset of each cell
  if (level === 0) v = 0.08; // 8% for level 0
  if (gameCount < 2) v = 0; // no error in the first game
  for (let i = 0; i < 64; i++) {
    cellErrX[i] = (Math.random() * 2 - 1) * v; 
    cellErrY[i] = (Math.random() * 2 - 1) * v;
  }
  calcCellOffsets();
}

function calcCellOffsets() {
  const c = COLW;   // cell size in px
  for (let i = 0; i < 64; i++) {
    cellX[i] = Math.round(((i & 7)  + cellErrX[i]) * c);
    cellY[i] = Math.round(((i >> 3) + cellErrY[i]) * c);
  }
}

/* ===== Board Styles ===== */
function toggleStyle() {
  boardStyle = (boardStyle + 1) % STYLE_COUNT; // shift
  showStyleIcon();
  drawBoard();
}

function showStyleIcon() {
  styleElm.src = imageFiles[boardStyle % STYLE_COUNT][compFirst ? L_ICO : D_ICO];
  styleCompElm.src = imageFiles[boardStyle % STYLE_COUNT][compFirst ? D_ICO : L_ICO];
  drawPieces();
}

function toggleCellNum() { 
  cellNumEnabled = !cellNumEnabled; 
  cellNumSwitch.classList.toggle("off", !cellNumEnabled);
  drawBoard(); 
}

/* ===== Draw board (once) ===== */ 
function drawBoard() {
  const c = COLW, pad = c * 0.03;
  boardCtx.font = (c * 0.15 | 0) + "px Arial"; boardCtx.fillStyle = "#A98";
  boardCtx.textAlign = "right"; boardCtx.textBaseline = "top"; 
  //console.log(c,boardStyle);
  for (let i = 0; i < 64; i++) {
    const x = i & 7, y = i >> 3, playable = (x + y) & 1;
    boardCtx.drawImage(images[boardStyle][playable ? EMPTY : NOUSE], x * c, y * c, c, c);
    if (cellNumEnabled && playable) {
      const n = cellToNum[compFirst ? 63 - i : i];
      boardCtx.fillText(n, x * c + c - pad, y * c + pad);
    }
  }
}

/* ===== Draw pieces ===== */
function drawPieces(hightlight = true) {
  clearPieceCanvas();
  clearAnimeCanvas();
  for(let i = 0; i < 64; i++) {
    const p = pc[i];
    if(p < 0 || p > 3) continue;
    drawPiece(p, i);
  }

  // Highlight selected piece
  if(hightlight && pieceSelected) {
    const c = COLW, i = selectedCell;
    const p = imgP(pc[i]);
    const img = images[boardStyle][COLOR(p) === LGHT ? SEL_WHITE : SEL_BLACK];
    animeCtx.drawImage(img, (i & 7) * c, (i >> 3) * c, c, c);
  }
}

function drawPiece(p, cell) {
  const c = COLW;
  if (p === EMPTY) { 
    clearPiece(cell);
  } else {
    const img = images[boardStyle][imgP(p)];
    //const ex = cellErrX[cell] * c, ey = cellErrY[cell] * c;
    //if (img) pieceCtx.drawImage(img, x + ex, y + ey, c, c);
    const ex = cellX[cell], ey = cellY[cell];
    if (img) pieceCtx.drawImage(img, ex, ey, c, c);
  }
}

function clearPiece(cell) {
  const c = COLW, x = (cell & 7) * c, y = (cell >> 3) * c, e = c * 0.2;
  pieceCtx.clearRect(x, y - e, c, c + e * 2); // clear top bottom too
  pieceCtx.clearRect(x - e, y, c + e * 2, c); // clear left right too
}

// switch dark-light images, suggested by community 23-Jan-2026
function imgP(p){ 
  if (compFirst || p === EMPTY || p === NOUSE) return p;
  return p^1;  // swap L <-> D when compFirst
}

function clearPieceCanvas() { pieceCtx.clearRect(0, 0, pieceCanvas.width, pieceCanvas.height); }
function clearAnimeCanvas() { animeCtx.clearRect(0, 0, animeCanvas.width, animeCanvas.height); }

/* ===== message helpers ===== */
function message(text){ messageElm.textContent = text; }
function version(text){ versionElm.textContent = text; }
function footer(text) { footerElm.textContent = text; }
function showNewGame(show) { newGameElm.style.visibility = show ? "visible" : "hidden"; }
function setNewGameEnabled(on) { newGameElm.classList.toggle("disabled", !on); }
function showStyleIconIcon(show) { 
  //styleElm.style.display = show ? "inline" : "none"; 
  cellNumElm.style.display = show ? "inline" : "none"; 
  soundElm.style.display = show ? "inline" : "none"; 
}


/********* ANIMATE HAND AND PIECE MOVE **************
 
          ###    ##   ##  ####  ##    ##  ######
         ## ##   ###  ##   ##   ###  ###  ## 
        #######  ## # ##   ##   ## ## ##  #####
        ##   ##  ##  ###   ##   ##    ##  ##
        ##   ##  ##   ##  ####  ##    ##  ######
 
 ****************************************************

/*
  animateMove
   ├─ simple animation → return
   └─ hand animation
       ├─ Phase 1   : hand approaches piece
       ├─ Phase 1.5 : finger touch
       ├─ Phase 2   : drag (maybe wrong drop)
       ├─ Phase 2.5 : correction (optional)
       ├─ Phase 3   : capture handling (optional)
       ├─ Phase 4   : promote handling (optional)
       └─ exit hand
*/

const PAUSE = 60, PIECE_MOVE_MS = 200;
const HSLOW = 300, HFAST = 200, GIRL_SPEED = 1.2;

async function animateMove(mv, startX = null, startY = null) {
  const fmCell = FM(mv), toCell = TO(mv), mvBits = BITS(mv), mvPiece = pc[fmCell];
  const handAnimate = COLOR(mvPiece) === DARK && boardStyle != STYLE_MODERN;
  const c = COLW; dirty = null;

  // Piece Coordinates
  //const fmX = PFILE(fmCell) * c, fmY = RANK(fmCell) * c;
  //const toX = PFILE(toCell) * c, toY = RANK(toCell) * c;
  const fmX = cellX[fmCell], fmY = cellY[fmCell];
  const toX = cellX[toCell], toY = cellY[toCell];
  //const pieceImg = images[boardStyle][imgP(mvPiece)];
  const pmoveImg = images[boardStyle][imgP(mvPiece) + PMOV_SHIFT];
  const emptyImg = images[boardStyle][EMPTY];
  //initPmovCanvas(mvPiece); // init piece moving image

  // -------- SIMPLE MODE (no hand animation) --------

  if (!handAnimate) {
    drawPiece(EMPTY, fmCell);
    const sX = startX ?? fmX, sY = startY ?? fmY;
    await runPhase(PIECE_MOVE_MS, t => {
      const px = Math.round(sX + (toX - sX) * t);
      const py = Math.round(sY + (toY - sY) * t);
      drawMovingPiece(pmoveImg, px, py);
    });
    drawPiece(mvPiece, toCell);
    return;
  }

  // ======== HAND ANIMATION ========

  const isCapture = (mvBits & MCAPTURE) !== 0;
  const isPromote = (mvBits & MPROMOTE) !== 0;
  const isMovePwn = !isCapture && !isPromote && mvPiece === D_PWN;
  const prvFm = prvBestMove > 0 ? FM(prvBestMove) : -1;
  const prvTo = prvBestMove > 0 ? TO(prvBestMove) : -1;
  const isFar = fmCell >= 24;

  // 2.1 Hand Images and Move Speed
  let handIdx, spd = 1, isConfident = false;

  if (level === 0) {
    spd = GIRL_SPEED;
    if (isMovePwn) handIdx = GIRL_MOV1;
    else handIdx = GIRL_CAP1;
  } else {
    if (isPromote) handIdx = HAND_CAP2;
    else if (mvPiece === D_HRS && boardStyle === STYLE_CLASSIC) handIdx = HAND_CAPW; // wide
    else if (isCapture) handIdx = isFar ? HAND_CAP2 : HAND_CAP1;
    else handIdx = isFar ? HAND_MOV1 : HAND_MOV2;
  }
  if (level > 1 || curBestScore > 150) isConfident = true;

  // --- set intention-based flags ---
  const isHesitantMovPwn = moveCount > 6 && isMovePwn && !isConfident;
  const doSmallDragError = isHesitantMovPwn && chance(0.1);
  const doTargetHesitate = isHesitantMovPwn && prvFm === fmCell && prvTo !== toCell;
  const doSecondBestLook = isHesitantMovPwn && prvFm !== fmCell;

  // 2.2 Hand Scaling & Finger-tip Offsets
  const imgHand = images[IMG_HAND][handIdx];
  setHandScale(imgHand);

  // 2.3. Hand key positions
  const arc = HAND_CURVE * c;
  const pickX = fmX, pickY = fmY, dropX = toX, dropY = toY;

  await initHandCanvas(imgHand, handW, handH);
  const homeX = (PFILE(toCell) / 2) * COLW, homeY = -COLW; // Off-screen top left
  handX = homeX - handGripX; handY = homeY - handGripY; // hand start ourside board
  await handTo(20, homeX, homeY); // reset hand to home position

  // === PHASE 1: Hand moving to a piece ===

  const pickErrX = Math.round((Math.random() * 0.1 - 0.05) * c);
  const pickErrY = Math.round(((mvPiece === D_HRS || isCapture) ? 0.1 : -0.1) * c);
  const prePickX = pickX + pickErrX, prePickY = pickY + pickErrY;

  // --- hand to second best piece ---
  //if (moveCount > 8 && isMovePwn && !isConfident && prvFm != fmCell) {
  if (doSecondBestLook) {
    const fm2X = PFILE(prvFm) * c, fm2Y = RANK(prvFm) * c; // second best cell
    const fm1X = (fm2X + homeX) / 2, fm1Y = (fm2Y + homeY) / 2; // best cell
    await handTo(HSLOW * spd, fm2X, fm2Y); // hand to 2nd best piece
    await handUp(HSLOW, fm2X, fm2Y);
    await handTo(HSLOW * spd, fm1X, fm1Y, arc); // hand back half way
    await handUp(HSLOW, fm1X, fm1Y);
  }

  // === PHASE 1.5: touch a piece ---
  if (isCapture) await handTo(HFAST, pickX, pickY);
  else {
    // hand to pre-pick position
    await handTo(HSLOW * spd, prePickX, prePickY, fmCell < 16 ? -arc / 2 : 0);
    // hand hesitate
    //if (isMovePwn && !isConfident && chance(0.1)) 
    if (isHesitantMovPwn && chance(0.1)) 
      await handUp(HSLOW, prePickX, prePickY); // hand float
    await holdMs(20); // tiny pause
    await handTo(PAUSE, pickX, pickY);
    await holdMs(PAUSE * (1 + Math.random())); // Eye-before-move
  }

  // --- remove from piece ---
  drawPiece(EMPTY, fmCell);

  // === PHASE 2: Move hand with piece to target cell ===

  // --- hesitate if the moving piece can move two ways ---
  //if (moveCount > 8 && isMovePwn && !isConfident && prvFm === fmCell && prvTo !== toCell) {
  if (doTargetHesitate) {
    //const prvTo = TO(prvBestMove);
    const prvToX = PFILE(prvTo) * c, prvToY = RANK(prvTo) * c;
    const t = 0.25 + Math.random() * 0.5;
    const midX = fmX + (prvToX - fmX) * t, midY = fmY + (prvToY - fmY) * t;
    // 1) drag to previous best target
    await handTo(HSLOW * spd, midX, midY, 0, pmoveImg,null,null, null,SOUND_MOV);
    await holdMs(HSLOW);
    // 2) drag back to original square (change of mind)
    await handTo(HSLOW, fmX + 0.1 * c, fmY + 0.1 * c, 0, pmoveImg,null,null, null,SOUND_MOV);
    await holdMs(HSLOW);
  }

  // drag piece with small error
  //if (isMovePwn && !isConfident && chance(0.1)) { // drags piece with small error
  if (isHesitantMovPwn && chance(0.1)) {
    const errX = Math.round((Math.random() * 2 - 1) * 0.2 * c);
    const errY = Math.round((Math.random() * 2 - 1) * 0.3 * c);
    const pErrX = toX + errX, pErrY = toY + errY;
    const hErrX = dropX + errX, hErrY = dropY + errY;
    const hAwayX = (homeX + dropX) / 2, hAwayY = (homeY + dropY) / 2;
    // 1) Hand drags piece to target cell with small error
    await handTo(HSLOW * spd, hErrX, hErrY, 0, pmoveImg,null,null, null,SOUND_MOV);
    await holdMs();
    // 2) Hand moves away half way
    await handTo(HFAST, hAwayX, hAwayY, 0, pmoveImg, pErrX, pErrY);
    // 3) Hand comes back
    await handTo(HFAST, hErrX, hErrY, 0, pmoveImg, pErrX, pErrY);
    // 4) Hand drags piece to correct position
    await handTo(HFAST, dropX, dropY, 0, pmoveImg,null,null, null,SOUND_FIX);
    await holdMs();
  } else {
    // piece to target cell
    if (isCapture) {
      // Drop piece at target cell
      await handTo(HSLOW * spd, dropX, dropY, arc, pmoveImg,null,null, null,null,SOUND_CAP);
    } else {
      // Drag piece to target cell
      await handTo(HSLOW * spd, dropX, dropY, 0, pmoveImg,null,null, null,SOUND_MOV);
    }
    await holdMs();
  }  

  // draw target piece
  drawPiece(mvPiece, toCell);

  // Hit another piece accidentally
  if (isMovePwn && toCell > 24 && chance(0.2)) { // chance 20%
    const hitCell = toCell - 16; // the piece we hit by mistake at 2 rows below
    const hitPc = pc[hitCell];
    if (hitPc === L_PWN || hitPc === D_PWN) {
      // Correct position of the hit piece
      //const hitX = PFILE(hitCell) * c, hitY = RANK(hitCell) * c;
      const hitX = cellX[hitCell], hitY = cellY[hitCell];
      // Accidental dragged position
      const slipX = hitX + Math.round((Math.random() * 2 - 1) * 0.3 * c);
      const slipY = hitY - Math.round(Math.random() * 0.3 * c);
      const hitImg = images[boardStyle][imgP(hitPc) + PMOV_SHIFT];
      drawPiece(EMPTY, hitCell); // temp remove the hit piece
      await handTo(PAUSE, (slipX+homeX)/2, (slipY+homeY)/2, 0, hitImg, slipX, slipY); // away
      await holdMs();
      await handTo(HFAST, slipX, slipY, arc, hitImg, slipX, slipY); // hand back, piece stays
      await holdMs();
      await handTo(HFAST, hitX, hitY, 0, hitImg,null,null, null,SOUND_FIX); // drag to correct
      drawPiece(hitPc, hitCell); // restore the hit piece
    }
  }

  // === PHASE 3: pick up captured piece ===
  if (isCapture) {
    const capCell = captureCellFromMove(mv);
    const capHX = PFILE(capCell) * c, capHY = RANK(capCell) * c;
    const capImg = images[boardStyle][imgP(CAPPIECE(mv)) + PMOV_SHIFT];
    // 1) move hand to captured cell
    await handTo(HFAST * spd, capHX, capHY, arc);
    await holdMs();   // pause after pick captured piece
    // 2) remove captured piece
    drawPiece(EMPTY, capCell);
    // 3) Carry captured piece away
    await handTo(HFAST * spd, homeX, homeY, 0, capImg);
  } else {
    // --- Hand away ---
    await handTo(HFAST * spd, homeX, homeY);
  }

  // --- Promote ---
  if (isPromote) {
    // 1) hand returns with new piece
    const promoImg = images[boardStyle][imgP(D_PWN)];
    await handTo(HFAST * spd, dropX, dropY, 0, promoImg,null,null, null,null,SOUND_HIT);
    await holdMs();
    // 2) draw promoted piece
    drawPiece(D_HRS, toCell);
    // 3) hand leaves again
    await handTo(HFAST * spd, homeX, homeY);
  }
}

async function animateGivePiece() {
  if (boardStyle === STYLE_MODERN) return;
  const c = COLW, arc = HAND_CURVE * c;

  // hand image
  const imgHand = images[IMG_HAND][GIRL_CAP1];
  setHandScale(imgHand);
  await initHandCanvas(imgHand, handW, handH);

  //const homeX = Math.round((8 * c) / 2 - handW);
  //const homeY = Math.round(-handH);
  //handX = homeX; handY = homeY; // start hand at home
  const homeX = 3 * COLW, homeY = -COLW; // Off-screen top left
  handX = homeX - handGripX; handY = homeY - handGripY; // hand start ourside board
  await handTo(20, homeX, homeY); // move hand to home position

  if(chance(0.6)) { 
    // 60% Give a dark pawn away
    const cell = pick(8, 10, 12), piece = pc[cell], img = images[boardStyle][imgP(piece)];
    if (piece === EMPTY) return;
    let cell0; // first attempt cell but not equal to actual cell
    do { cell0 = pick(8, 10, 12); } while (cell0 === cell);
    const pck0X = PFILE(cell0) * c, pck0Y = RANK(cell0) * c;
    const pickX = PFILE(cell) * c, pickY = RANK(cell) * c;
    const giveX = (8 * c) / 2, giveY = (8 * c);
    const r = Math.random();
    if (r < 0.3) {
      await handTo(HFAST, pickX, pickY, arc); // hand to cell
      await handUp(HSLOW, pickX, pickY);
    }
    if (r < 0.6) {
      await handTo(HFAST, pck0X, pck0Y, arc); // hand to random cell
      await handUp(HSLOW, pck0X, pck0Y);
    }
    await handTo(HFAST, pickX, pickY, arc); // hand to cell
    await holdMs();
    drawPiece(EMPTY, cell); // remove piece
    await handTo(HSLOW * 2, giveX, giveY, 0, img,null,null, SOUND_PCK); // carry
    await holdMs();
    await handTo(HSLOW * GIRL_SPEED, homeX, homeY); // hand back to home
    pc[cell] = EMPTY;
  } else {
    // 40% Promote a light pawn
    const cell = pick(58, 60, 62), piece = pc[cell], img = images[boardStyle][imgP(piece)];
    if (piece === EMPTY) return;
    const pickX = PFILE(cell) * c, pickY = RANK(cell) * c;
    await handTo(HSLOW, pickX, pickY, arc, img,null,null, null,null,SOUND_HIT); // hand to cell
    drawPiece(L_HRS, cell); // promote piece
    await holdMs();
    await handTo(HSLOW * GIRL_SPEED, homeX, homeY); // hand back to home
    pc[cell] = L_HRS;
  }
}

async function animateSelect(cell) {
  const p = pc[cell], c = COLW;
  const x = PFILE(cell) * c;
  const y = RANK(cell) * c;
  clearAnimeCanvas();
  if(COLOR(p)===LGHT) animeCtx.drawImage(images[boardStyle][SEL_WHITE], x, y, c, c);
  if(COLOR(p)===DARK) animeCtx.drawImage(images[boardStyle][SEL_BLACK], x, y, c, c);
}

function captureCellFromMove(mv) {
  if (!(mv & MCAPTURE)) return -1;
  const from = FM(mv), to = TO(mv);
  return (
    from > to
      ? (PFILE(from) > PFILE(to) ? to + 9 : to + 7)
      : (PFILE(from) > PFILE(to) ? to - 7 : to - 9)
  );
}


/********************* HAND ************************
 
          ##   ##    ###    ##   ##  ###### 
          ##   ##   ## ##   ###  ##  ##   ##
          #######  #######  ## # ##  ##   ##
          ##   ##  ##   ##  ##  ###  ##   ##
          ##   ##  ##   ##  ##   ##  ######
 
 ****************************************************/

// ====================== INIT HAND =======================

const HAND_IN_SQUARES = 11, HAND_CURVE = 2; // hand is 11 squares tall
let handScale = 1, handW = 0, handH = 0, handX = 0, handY = 0, handGripX = 0, handGripY = 0;

function setHandScale(imgHand) {
  handScale = (HAND_IN_SQUARES * COLW) / imgHand.height;
  handW = imgHand.width * handScale;
  handH = HAND_IN_SQUARES * COLW;
  //handH = imgHand.height * handScale;
  handGripX = Math.round(HAND_GRIP_OFFSET_X * handScale);
  handGripY = Math.round(handH - (HAND_GRIP_OFFSET_Y * handScale));
}

async function initHandCanvas(img, w, h) {
  handCanvas.width  = w; handCanvas.height = h;
  handCtx.clearRect(0, 0, w, h);
  handCtx.drawImage(img, 0, 0, w, h);
  return handCanvas;
}

// ====================== HAND TO =======================

async function handTo(ms, hx, hy, arc = 0, img = null, qx = null, qy = null, 
    pckSound = null, movSound = null, endSound = null) {
  // play sound before and during animation
  const movMs = Math.max(20, HFAST, vary(ms));
  if      (pckSound !== null) playSound(pckSound);
  else if (movSound !== null) playSound(movSound, movMs);
  // animate hand and piece
  const dstX = hx - handGripX;
  const dstY = hy - handGripY;
  const sx = handX, sy = handY;  // source point
  const dx = dstX - sx, dy = dstY - sy;  // destination point
  const cx = (sx + dstX) * 0.5;  // control point
  const cy = (sy + dstY) * 0.5 - arc; // curve in y axis
  const useBezier = arc !== 0;
  //console.log(moveCount,dstX,dstY,sx,sy,dx,dy);
  await runPhase(movMs, t => {
    let x, y;
    if (!useBezier) {
      x = sx + dx * t;
      y = sy + dy * t;
    } else {
      x = bezier(sx, cx, dstX, t);
      y = bezier(sy, cy, dstY, t);
    }
    if (img && qx != null && qy != null) {
      drawMovingPiece(img, qx, qy); // if q then piece stays at q position
      drawHand(x, y); // move only hand while piece stays
    } else {
      if (img) drawHand(x, y, x + handGripX, y + handGripY, img); // move hand and piece
      else drawHand(x, y); // move hand only
    }
  });
  // play sound after animation
  if (endSound !== null) playSound(endSound, movMs);
  handX = dstX; handY = dstY;
}

async function handUp(ms, x, y, amp = COLW / 50) {
  const t0 = performance.now();
  while (performance.now() - t0 < ms) {
    const rx = (Math.random() * 2 - 1) * amp;
    const ry = (Math.random() * 2 - 1) * amp;
    await handTo(ms / 2, x + rx, y + ry);
  }
  await handTo(PAUSE, x, y); // settle back
}

/*async function doThinkGesture(cell1, cell2) {
  const c = COLW, homeX = 3 * c, homeY = -c; // Off-screen top left
  const x1 = PFILE(cell1) * c, y1 = RANK(cell1) * c;
  const x2 = PFILE(cell2) * c, y2 = RANK(cell2) * c;
  // move hand near the target square (as if "considering")
  await handTo(20, homeX, homeY); // hand ready
  await handTo(HSLOW, x1, y1, 0); // hand to cell1
  await holdMs(vary(HFAST)); // thinking pause
  await handTo(HSLOW, x2, y2, HAND_CURVE * c); // hand to cell2
  await holdMs(vary(HFAST)); // thinking pause
  await handTo(HSLOW, homeX, homeY); // hand away
}*/


// ============ RUN PHASE ===============

let phaseId = 0;

async function runPhase(ms, drawFn) {
  const myId = ++phaseId;
  return new Promise(resolve => {
    const t0 = performance.now();
    function tick(now) {
      const t = Math.min(1, (now - t0) / ms);
      const ease = easeInOut(t);
      if (dirty) clearDirty();
      drawFn(ease);
      if (t < 1) requestAnimationFrame(tick);
      else resolve();
    }
    requestAnimationFrame(tick);
  });
}

// ============ DRAW HAND AND PIECE ===============

function drawHand(dx, dy, px, py, img = null) {
  //console.log(phaseId, Math.round(dx), Math.round(dy));
  const visX = Math.round(Math.max(0, dx));
  const visY = Math.round(Math.max(0, dy));
  const visW = Math.round(Math.min(dx + handCanvas.width,  CANVAS_W) - visX);
  const visH = Math.round(Math.min(dy + handCanvas.height, CANVAS_H) - visY);
  if (visW <= 0 || visH <= 0) return;
  const sx = Math.round(visX - dx);
  const sy = Math.round(visY - dy);
  if (img != null) drawMovingPiece(img, Math.round(px), Math.round(py));
  //if (img != null) drawMovingPiece(img, px, py);
  //console.log("h",moveCount, sx, sy, visW, visH, visX, visY, visW, visH);
  animeCtx.drawImage(handCanvas, sx, sy, visW, visH, visX, visY, visW, visH);
  markDirty(visX, visY, visW, visH);
}

function drawMovingPiece(img, x, y) {
  //console.log("p",moveCount,x,y);
  //animeCtx.drawImage(img, x, y, COLW, COLW);
  animeCtx.drawImage(img, x, y, COLW, COLW);
  markDirty(x, y, COLW, COLW);
}

let dirty = null;

function markDirty(x, y, w, h) {
  if (!dirty) {
    dirty = { x, y, w, h };
  } else {
    // expand existing dirty rect
    const minX = Math.min(dirty.x, x);
    const minY = Math.min(dirty.y, y);
    const maxX = Math.max(dirty.x + dirty.w, x + w);
    const maxY = Math.max(dirty.y + dirty.h, y + h);
    dirty = { x: minX, y: minY, w: maxX - minX, h: maxY - minY };
  }
}

function clearDirty(x, y, w, h) {
  animeCtx.clearRect(dirty.x, dirty.y, dirty.w, dirty.h);
  dirty = null;
}

function easeInOut(t) { return t * t * (3 - 2 * t); }
function bezier(p0, p1, p2, t) { const u=1-t; return u*u*p0 + 2*u*t*p1 + t*t*p2; }


/********************* SOUND ************************
 
       #####    #####   ##   ##  ##   ##  ###### 
      ##       ##   ##  ##   ##  ###  ##  ##   ##
       #####   ##   ##  ##   ##  ## # ##  ##   ##
           ##  ##   ##  ##   ##  ##  ###  ##   ##
       #####    #####    #####   ##   ##  ######
 
 ****************************************************/

// ======== WEB AUDIO SOUND SYSTEM ========
const SOUND_PCK = 0, SOUND_MOV = 1, SOUND_FIX = 2, SOUND_CAP = 3, SOUND_HIT = 4;

let audioCtx, soundUnlocked = false, soundsReady = false;
let buffers = { classic: {}, default: {} }; // sound buffers per board style

async function loadSound(style, id, url) {
  const res = await fetch(url);
  const arr = await res.arrayBuffer();
  buffers[style][id] = await audioCtx.decodeAudioData(arr);
}

async function loadAllSounds() {
  await Promise.all([
    // classic board style sounds
    loadSound("classic", SOUND_PCK, "mPck_40.wav"),
    loadSound("classic", SOUND_MOV, "mMov_320.wav"),
    loadSound("classic", SOUND_FIX, "mFix_72.wav"),
    loadSound("classic", SOUND_CAP, "mCap_320.wav"),
    loadSound("classic", SOUND_HIT, "mHit_20.wav"),
    // default board style sounds
    loadSound("default", SOUND_PCK, "cPck_20.wav"),
    loadSound("default", SOUND_MOV, "cMov_300.wav"),
    loadSound("default", SOUND_FIX, "cFix_60.wav"),
    loadSound("default", SOUND_CAP, "cCap_120.wav"),
    loadSound("default", SOUND_HIT, "cHit_60.wav"),
  ]);
  soundsReady = true;
}

function playSound(type, ms = null) {
  if (!soundUnlocked || !soundsReady || !soundEnabled) return;
  if (boardStyle === STYLE_MODERN) return; // no sound for modern style
  const style = (boardStyle === STYLE_CLASSIC ? "classic" : "default");
  const buffer = buffers[style][type] || buffers.default[type];
  if (!buffer) return;
  const src = audioCtx.createBufferSource();
  const gain = audioCtx.createGain();
  let rate = 1;
  let volume = vary(SOUND_VOLUME);
  if (type === SOUND_MOV && ms > 0) rate = buffer.duration * 1000 / ms;

  src.buffer = buffer;
  src.playbackRate.value = rate;
  gain.gain.value = volume;
  src.connect(gain).connect(audioCtx.destination);
  src.start();
  //console.log("rate=",rate," vol=",volume);
}

function unlockSound() {
  if (soundUnlocked) return;
  audioCtx = new (window.AudioContext || window.webkitAudioContext)();
  if (audioCtx.state === "suspended") audioCtx.resume();
  const src = audioCtx.createBufferSource();
  src.buffer = audioCtx.createBuffer(1, 1, audioCtx.sampleRate);
  src.connect(audioCtx.destination);
  src.start(0);
  soundUnlocked = true;
  loadAllSounds();
}

let soundEnabled = false, soundLevel = 0; // 0=🔈 muted, 1=🔉 medium, 2=🔊 loud
let SOUND_VOLUME = 0.5;

async function toggleSound() {
  if (!soundUnlocked) await unlockSound();
  soundEnabled = true;
  soundLevel = (soundLevel + 1) % 3;
  if      (soundLevel === 0) { soundElm.textContent = "🔈"; soundEnabled = false; } 
  else if (soundLevel === 1) { soundElm.textContent = "🔉"; SOUND_VOLUME = 0.3; } 
  else                       { soundElm.textContent = "🔊"; SOUND_VOLUME = 0.5; }
}

function vary(base, amount = 0.25) { return base * (1 + (Math.random() * 2 - 1) * amount); }


/******************** MOUSE ************************
 
     ##    ##   #####   ##   ##   #####   #####
     ###  ###  ##   ##  ##   ##  ##       ##     
     ## ## ##  ##   ##  ##   ##   #####   ####  
     ##    ##  ##   ##  ##   ##       ##  ##     
     ##    ##   #####    #####    #####   #####

 *************************************************/

/*
  GS_LGHT + pieceSelected=false  → waiting for source
  GS_LGHT + pieceSelected=true   → waiting for target
  GS_DARK                        → AI thinking
*/

// drag state
let dragging=false, dragFrom=-1, dragPc=EMPTY;
let dragX=0, dragY=0, dragStartX=0, dragStartY=0, 
    dragPrevX=null, dragPrevY=null, wasDragging = false;
const DRAG_THRESHOLD=2;

function installPointerHandlers() {

  pieceCanvas.addEventListener("pointerdown",(e)=>{
    e.preventDefault();
    //unlockSound();
    if(bCompBusy) return;
    if(gameState===GS_NONE) return startNewGame();
    if(gameState!==GS_LGHT) return;
    const cell=getCellFromClientPos(pieceCanvas,e.clientX,e.clientY);
    if(cell<0) return;
    if(pieceSelected && isMovableTarget(cell)) return; // let pointerup handle
    if(!selectSource(cell)) return;
    initDrag(cell, e);
    cacheForceMove();
    //console.log("pointerdown",gameState,"dragging",dragging,pieceSelected,selectedCell);
  },{passive:false});

  pieceCanvas.addEventListener("pointermove", (e)=>{
    e.preventDefault();
    if(dragFrom<0) return;
    if(!dragging){
      const dx=Math.abs(e.clientX-dragStartX), dy=Math.abs(e.clientY-dragStartY);
      if(dx+dy < DRAG_THRESHOLD) return;
      dragging=true;
      //const fmX=(dragFrom&7)*COLW, fmY=(dragFrom>>3)*COLW;
      //pieceCtx.drawImage(images[boardStyle][EMPTY], fmX, fmY, COLW, COLW);
      drawPiece(EMPTY, dragFrom);
    }
    //console.log("pointermove",gameState,"dragging",dragging,pieceSelected,selectedCell);
    updateDragPos(e); drawDrag();
  });

  pieceCanvas.addEventListener("pointerup",async (e)=>{
    e.preventDefault();
    if(bCompBusy) { resetDrag(); clearAnimeCanvas(); return; }
    pieceCanvas.releasePointerCapture(e.pointerId);
    wasDragging=dragging;
    resetDrag(); clearAnimeCanvas();
    let cell=getCellFromClientPos(pieceCanvas,e.clientX,e.clientY);
    //if(wasDragging && !isMovableTarget(cell)) cell=nearestTarget(e.clientX,e.clientY);
    if(cell<0 || (wasDragging && !isMovableTarget(cell))){ drawPieces(); return; }
    if(pieceSelected && isMovableTarget(cell)) await handlePlayerMove(cell);
    else drawPieces();
    //console.log("pointerup",gameState,"dragging",dragging,pieceSelected,selectedCell);
  });

  //pieceCanvas.addEventListener("touchstart", e => { unlockSound(); }, { passive: false });
  pieceCanvas.addEventListener("pointercancel",cancelDrag);
  pieceCanvas.addEventListener("pointerleave",cancelDrag);
  soundElm.addEventListener("click", toggleSound);
  cellNumElm.addEventListener("click", toggleCellNum);
  styleElm.addEventListener("click", toggleStyle);
  newGameElm.addEventListener("click", () => { 
    if (bCompBusy) return;
    gameOver(-1); startNewGame(); 
  });
}

async function startNewGame() { 
  if(bCompBusy) return;
  if(gameState === GS_DARK) return; // safe guard
  await startGame(); gameState = GS_LGHT; 
}

async function handlePlayerMove(cell) {
  if(!pieceSelected) return;
  let selIndex = -1;
  for(let i = 0; i < gen_end[0]; i++) {
    if(FM(gen_dat[i]) === selectedCell && TO(gen_dat[i]) === cell) {
      selIndex = i; break; // find move index
    }
  }
  if(selIndex < 0) { // Invalid destination
    if(isMovableSource(cell)) selectedCell = cell;
    drawPieces(); bCompBusy = false; return;
  }
  await executePlayerMove(selIndex); // Valid move
}

async function executePlayerMove(selIndex) {
  bCompBusy = true;
  const mv=gen_dat[selIndex], fm=FM(mv), to=TO(mv), bits=BITS(mv);
  if(wasDragging) await animateMove(mv,dragPrevX,dragPrevY);
  else await animateMove(mv);
  //if(boardStyle !== STYLE_MODERN) 
  playSound(bits === MMOVE ? SOUND_HIT : SOUND_CAP);
  makemove(mv); lastmove = mv; lastmoveCap = to;
  addMoveToHistory(mv);
  if (BITS(lastmove) === MMOVE && pc[to] === L_HRS) drawCount++;
  else drawCount = 0;
  pieceSelected = false; gameState = GS_DARK; // bCompBusy=true; 
  message("Sunhorse กำลังคิด.."); drawPieces();
  stopPlayerTimer();
  await holdMs(20);
  await aiMainLoop(); // <<<<<<<<<<< AI MAIN LOOP <<<<<<<<<<<
  drawPieces();
  bCompBusy=false; // unlock after ai move
}

let moveTargets=[]; // store all movable targets of current source
let forceMove=-1;

function selectSource(cell){
  if(!isMovableSource(cell)) return false;
  pieceSelected=true; selectedCell=cell;
  moveTargets.length=0;
  for(let i=0; i<gen_end[0]; i++)
    if(FM(gen_dat[i])===cell) moveTargets.push(TO(gen_dat[i]));
  animateSelect(cell);
  return true;
}

function isMovableSource(cell) {
  for(let i=0; i<gen_end[0]; i++) if(FM(gen_dat[i])===cell) return true;
  return false;
}

function isMovableTarget(cell) {
  if(!pieceSelected) return false;
  for(let i=0; i<gen_end[0]; i++) {
    if(FM(gen_dat[i])===selectedCell && TO(gen_dat[i])===cell) return true;
  }
  return false;
}

function cacheForceMove(){
  forceMove=-1;
  if(gen_end[0]===1) forceMove=TO(gen_dat[0]);
}

function addMoveToHistory(mv) {
  moveHistoryStr += mvToStr(mv);
}

function mvToStr(mv) {
  const fm = cellToNum[FM(mv)];
  const to = cellToNum[TO(mv)];
  const bits = BITS(mv);
  let sym = "-"; //, pmo = "";
  if (bits & MSKIP) return ". ";
  if (bits & MCAPTURE) sym = "x";
  //if (bits & MPROMOTE) pmo = "+";
  return fm + sym + to + " ";  // e.g. "25-24 24x18 . 8x4 "
}

function getCellFromClientPos(canvas, clientX, clientY) {
  const rect = canvas.getBoundingClientRect();
  const scaleX = canvas.width / rect.width;
  const scaleY = canvas.height / rect.height;
  const x = Math.floor((clientX - rect.left) * scaleX / COLW);
  const y = Math.floor((clientY - rect.top) * scaleY / COLW);
  if (x < 0 || x > 7 || y < 0 || y > 7) return -1;
  return y * 8 + x;
}

// drag helpers
function updateDragPos(e){
  const r=pieceCanvas.getBoundingClientRect();
  dragX=(e.clientX-r.left)*(pieceCanvas.width/r.width);
  dragY=(e.clientY-r.top )*(pieceCanvas.height/r.height);
}

function drawDrag(){
  const x=Math.round(dragX-COLW/2), y=Math.round(dragY-COLW/2);
  //if(dragPrevX!==null) animeCtx.clearRect(dragPrevX, dragPrevY, COLW, COLW);
  //clearAnimeCanvas();
  if(dirty) clearDirty();
  //animeCtx.drawImage(pmovCanvas, x, y);
  const img = images[boardStyle][imgP(dragPc) + PMOV_SHIFT];
  drawMovingPiece(img, x, y)
  dragPrevX=x; dragPrevY=y;
  // ghost target
  const t=nearestCachedTarget(dragX, dragY);
  if(t>=0){
    const tx=(t&7)*COLW, ty=(t>>3)*COLW;
    animeCtx.globalAlpha=0.1;
    //animeCtx.drawImage(pmovCanvas, tx, ty);
    drawMovingPiece(img, tx, ty)
    animeCtx.globalAlpha=1;
  }
}

/*function drawDrag(){
  clearAnimeCanvas();
  animeCtx.drawImage(images[boardStyle][dragPc], dragX-COLW/2, dragY-COLW/2, COLW, COLW);
}*/

function cancelDrag(){
  if(!dragging) return;
  resetDrag(); clearAnimeCanvas(); drawPieces();
  //console.log("cancelDrag",gameState,"dragging",dragging,pieceSelected,selectedCell);
}

function initDrag(cell, e) {
  dragFrom=cell; dragPc=pc[cell];
  dragStartX=e.clientX; dragStartY=e.clientY;
  //pmovCanvas.width = COLW; pmovCanvas.height = COLW;
  //pmovCtx.drawImage(images[boardStyle][dragPc], 0, 0, COLW, COLW);
  //initPmovCanvas(pc[cell]);
  dragPrevX=(cell&7)*COLW; dragPrevY=(cell>>3)*COLW;
  pieceCanvas.setPointerCapture(e.pointerId);
  clearAnimeCanvas();
  //if (boardStyle !== STYLE_MODERN) 
  playSound(SOUND_PCK);
}

function resetDrag(){
  dragging=false; dragFrom=-1; dragPc=EMPTY; //dragPrevX=dragPrevY=null;
}

function nearestCachedTarget(px,py){
  if(forceMove>=0) return forceMove;
  let best=-1, bestD=(1.1*COLW)*(1.1*COLW);
  for(const c of moveTargets){
    const cx=(c&7)*COLW+COLW/2, cy=(c>>3)*COLW+COLW/2;
    const dx=px-cx, dy=py-cy, d=dx*dx+dy*dy;
    if(d<bestD){ best=c; bestD=d; }
    //console.log(c,d,best,bestD);
  }
  return best;
}

function nearestTarget(x, y){
  if(!pieceSelected) return -1;
  const r=pieceCanvas.getBoundingClientRect();
  if(x<r.left || x>r.right || y<r.top || y>r.bottom) return -1;
  const sx=pieceCanvas.width/r.width, sy=pieceCanvas.height/r.height;
  const px=(x-r.left)*sx, py=(y-r.top)*sy;
  return nearestCachedTarget(px, py);
}


/******************** GEN ************************
 
              #####   #####  ##   ## 
             ##       ##     ###  ## 
             ##  ###  ####   ## # ## 
             ##   ##  ##     ##  ### 
              #####   #####  ##   ## 

 *************************************************/


/* ===== bit helpers ===== */
function FM(x){ return x & 0x000000ff; }
function TO(x){ return (x >> 8) & 0x000000ff; }
function RTO(x){ return x << 8; }
function BITS(x){ return x & 0x00ff0000; }
function COLOR(x){ return x & 5; }
function PFILE(x){ return x & 7; }
function RANK(x){ return x >> 3; } // devide by 8
function CAPBITS(x){ return ((x & X_HRS) ? MCAP_HRS : MCAP_PWN); }
function CAPPIECE(x){ return ((x & 0x00010000) ? X_HRS : X_PWN); }

const GEN_ALL = true, ONLY_BITS = false;


function gen(flag){
  //const t0 = performance.now();
  let lmvb=(ply>0?hist_dat[ply-1]:lastmove), capture=false;
  gen_end[ply]=gen_begin[ply];
  if((lmvb & MCAPTURE) && (lmvb & MPROMOTE)==0){
    revSide();
    capture = (ply>0 ? can_capture(TO(hist_dat[ply-1])) : can_capture(lastmoveCap));
    revSide();
    if(capture){ gen_push(0,0,MSKIP); gen_begin[ply+1]=gen_end[ply]; return; }
  }
  capture=false;
  if(lmvb & MSKIP){
    if(ply>0) gen_cap(TO(hist_dat[ply-2])); else gen_cap(lastmoveCap); capture=true; 
  } else {
    for(let q=0;q<32;q++){ const i=pcConv[q], p=pc[i]; if(p>=EMPTY || (p&5)!=side) continue; if(gen_cap(i)) capture=true; } // COLOR(p) is p&5
  }
  if(!capture && flag===GEN_ALL){
    for(let q=0;q<32;q++){ 
      const i=pcConv[q], p=pc[i]; // COLOR(p) is p&5, pfile(i) is i&7
      if(p>=EMPTY || (p&5)!=side) continue; 
      if(p===L_PWN){ const f=(i&7); if(f!==0 && pc[i-9]===EMPTY) gen_push(i,i-9,MMOVE); if(f!==7 && pc[i-7]===EMPTY) gen_push(i,i-7,MMOVE); continue; }
      if(p===D_PWN){ const f=(i&7); if(f!==7 && pc[i+9]===EMPTY) gen_push(i,i+9,MMOVE); if(f!==0 && pc[i+7]===EMPTY) gen_push(i,i+7,MMOVE); continue; }
      if(p===L_HRS||p===D_HRS){ for(let k=0;k<4;k++){ for(let n=i;;){ n=mailbox[mailbox64[n] + offset[k]]; if(n===-1) break; if(pc[n]===EMPTY) gen_push(i,n,MMOVE); else break; } } continue; }
    }
  }
  gen_begin[ply+1]=gen_end[ply];
  //genTime += (performance.now() - t0);
}

function can_capture(i){
  const p=pc[i]; // COLOR(p) is p&5, pfile(i) is i&7
  if(p===L_PWN){ if(i<=15) return false; const f=(i&7); if(f>1 && (pc[i-9]&5)===DARK && pc[i-18]===EMPTY) return true; if(f<6 && (pc[i-7]&5)===DARK && pc[i-14]===EMPTY) return true; }
  if(p===D_PWN){ if(i>=48) return false; const f=(i&7); if(f<6 && (pc[i+9]&5)===LGHT && pc[i+18]===EMPTY) return true; if(f>1 && (pc[i+7]&5)===LGHT && pc[i+14]===EMPTY) return true; }
  if(p===L_HRS||p===D_HRS){ for(let k=0;k<4;k++){ for(let n=i;;){ n=mailbox[mailbox64[n] + offset[k]]; if(n===-1) break; if(pc[n]!==EMPTY){ if((pc[n]&5)===xside){ let m=mailbox[mailbox64[n] + offset[k]]; if(m===-1) break; if(pc[m]===EMPTY) return true; } break; } } } }
  return false;
}

function gen_cap(i){
  const p=pc[i]; let capture=false; // COLOR(p) is p&5, pfile(i) is i&7
  if(p===L_PWN){ if(i>15){ const f=(i&7); if(f>1 && (pc[i-9]&5)===DARK && pc[i-18]===EMPTY){ gen_push(i,i-18,CAPBITS(pc[i-9])); capture=true; } if(f<6 && (pc[i-7]&5)===DARK && pc[i-14]===EMPTY){ gen_push(i,i-14,CAPBITS(pc[i-7])); capture=true; } } return capture; }
  if(p===D_PWN){ if(i<48){ const f=(i&7); if(f<6 && (pc[i+9]&5)===LGHT && pc[i+18]===EMPTY){ gen_push(i,i+18,CAPBITS(pc[i+9])); capture=true; } if(f>1 && (pc[i+7]&5)===LGHT && pc[i+14]===EMPTY){ gen_push(i,i+14,CAPBITS(pc[i+7])); capture=true; } } return capture; }
  if(p===L_HRS||p===D_HRS){ for(let k=0;k<4;k++){ for(let n=i;;){ n=mailbox[mailbox64[n] + offset[k]]; if(n===-1) break; if(pc[n]!==EMPTY){ if((pc[n]&5)===xside){ let m=mailbox[mailbox64[n] + offset[k]]; if(m===-1) break; if(pc[m]===EMPTY){ gen_push(i,m,CAPBITS(pc[n])); capture=true; } } break; } } } return capture; }
  return capture;
}

function gen_push(from,to,bits){
  let i=gen_end[ply];
  if(pc[from]===L_PWN && to<=7) bits |= MPROMOTE;
  if(pc[from]===D_PWN && to>=56) bits |= MPROMOTE;
  gen_dat[i]=(from | RTO(to) | bits);
  gen_score[i]=MOV_VAL(to,from);
  if (bits & MCAP_PWN) gen_score[i] += PWN_VAL;
  if (bits & MCAP_HRS) gen_score[i] += HRS_VAL;
  if (bits & MPROMOTE) gen_score[i] += HRS_VAL;
  gen_end[ply]++;
}


/******************** EVAL ************************
 
           #####  ##   ##    ###    ##       
           ##     ##   ##   ## ##   ##       
           ####   ##   ##  #######  ##       
           ##      ## ##   ##   ##  ##     
           #####    ##     ##   ##  #####   

 ***************************************************/

const MID_GAME = 35;
const D_CNT_BONUS = 2; // comp to keep dark pieces


function myeval(){
  const side_is_L = (side === LGHT);
  //const pa = pc, conv = pcConv;
  let score_LGHT=0, score_DARK=0;

  // --- no piece, terminal ---
  if ((L_PWN_cnt | L_HRS_cnt) === 0) return side_is_L ? -MAXBETA + ply :  MAXBETA - ply;
  if ((D_PWN_cnt | D_HRS_cnt) === 0) return side_is_L ?  MAXBETA - ply : -MAXBETA + ply;

  // score based on position of pieces
  const table = (moveCount < MID_GAME) ? pcsq : pcsq_end;
  /*for (let e = 0; e < 64; e++) {
    if (pc[e] === L_PWN) score_LGHT += table[e];
    else if (pc[e] === D_PWN) score_DARK += table[63 - e];
  }*/
  for (let i = 0; i < 32; i++) {
    const q = pcConv[i], p = pc[q];
    if (p === EMPTY) continue;
    if (p === L_PWN) score_LGHT += table[q];
    else if (p === D_PWN) score_DARK += table[63-q];
  }

  // --- Endgame phase, check egdb only on light side ---
  if(USE_EG && pieceCount <= 4) { // egdb for 4 pieces
    updatePieceCode();
    if(pieceCode == 1010) return(0); // both sides 2 hrs draw

    // 3-Feb-2026, rewrite score for endgame, suggested by chatGpt
    // score_pc = endgame shaping term (no DTM available)
    // - Guide fastest win and maximum resistance when egdb gives only W/L/D
    // - Outcome (±1000) and ply dominate; score_pc must stay small
    // Components:
    // 1) Pawn advance bonus: RANK + 5
    //    - Makes every pawn matter (even unadvanced)
    //    - Advanced pawns = closer to resolution
    // 2) Pawn reduction bonus: (4 - totalPawnCnt) * 6
    //    - Fewer pawns = simpler ending
    //    - Winning side prefers trades; losing side resists them
    // 3) Horse-only clarity bonus: +10
    //    - Helps resolve pawnless H vs H endings
    //    - Small enough to not override ply
    // Scale notes:
    // - score_pc typically stays < ~40
    // - Must never overpower ±ply or ±1000 outcome

    let score_pc = 0, pawnCnt = 0;
    for (let i = 0; i < 32; i++) {
      const q = pcConv[i], p = pc[q];
      if (p === EMPTY) continue;
      if (p === L_PWN) score_pc += RANK(q) + 5;           // light pawn score
      else if (p === D_PWN) score_pc += RANK(63-q) + 5;      // dark pawn mirrored score
    }
    score_pc += (4 - L_PWN_cnt - D_PWN_cnt) * 6;
    if ((L_PWN_cnt | D_PWN_cnt) === 0) score_pc += 10;

    const zkey = egHash(); // 63 bit zobrist
    const dval = egProbe(zkey);

    // COMLEXITY STYLES: level 0 draw quick, level 2 stubborn to draw
    let drawBias = 0;
    if (level === 0 || level >= 2) {
      const bal = (L_PWN_cnt + L_HRS_cnt) - (D_PWN_cnt + D_HRS_cnt);
      let sign = (level === 0) ? -1 : Math.sign(side_is_L ? bal : -bal);
      if (sign === 0) sign = -1;
      drawBias = sign * score_pc;
    }

    if (dval !== 0) {
//console.log(boardToText());
//console.log("z", zkey.toString(36),"s",side,"ply",ply,"v",dval);
//console.log("HIT!!!! in db, dval",dval);
//console.log(boardToText());

      egHitCnt++;
      if (dval === EG_W) return side_is_L ?  1000 - score_pc - ply : -1000 + score_pc + ply;
      if (dval === EG_L) return side_is_L ? -1000 + score_pc + ply :  1000 - score_pc - ply;
      //if (dval === EG_D) return side_is_L ?         score_pc       :        -score_pc;
      if (dval === EG_D) return side_is_L ? drawBias : -drawBias;
    }
    // fallback if no rec in egdb
    const xval = getdx(pieceCode);
//console.log("no db, code",pieceCode,"xval",xval);
    if (xval === EG_W) return side_is_L ?  1000 - score_pc - ply : -1000 + score_pc + ply;
    if (xval === EG_L) return side_is_L ? -1000 + score_pc + ply :  1000 - score_pc - ply;
    //if (xval === EG_D) return side_is_L ?         score_pc       :       -score_pc;
    if (xval === EG_D) return side_is_L ? drawBias : -drawBias;
  }

  // === Piece Count Bonus ===
  score_LGHT += (L_PWN_cnt * PWN_VAL + L_HRS_cnt * HRS_VAL);
  score_DARK += (D_PWN_cnt * PWN_VAL + D_HRS_cnt * HRS_VAL_D);
  // --- preservation bias ---
  score_LGHT += (L_PWN_cnt + L_HRS_cnt) * D_CNT_BONUS; // apply to only computer side
  score_DARK += (D_PWN_cnt + D_HRS_cnt) * D_CNT_BONUS;

  // === Bad Position Penalty ===
  if(pc[8] ===L_PWN && pc[1] ===D_PWN) score_DARK += 17;
  if(pc[55]===D_PWN && pc[62]===L_PWN) score_LGHT += 17;
  
/* ====== 64 ======
     1   3   5   7
   8  10  12  14
    17  19  21  23
  24  26  28  30
    33  35  37  39
  40  42  44  46
    49  51  53  55
  56  58  60  62
  ================ */

  // === only at beginning of the game ===
  if (moveCount < MID_GAME) {
    //const bEM = ~(bLP | bDP | bLH | bDH) & 0xffffffff; // bit 1 for empty
    //const pa = pc;
    
    // bonus for E-Pum & Standard for DARK (in case no follow MAK)
    if (pc[5] === D_PWN && pc[3] === D_PWN && pc[21] === D_PWN && pc[19] === D_PWN) {
    //if((pc[5] & pc[3] & pc[21] & pc[19]) === D_PWN){
      score_DARK += 5;
      if (pc[14] === D_PWN || pc[12] === D_PWN || pc[10] === D_PWN) score_DARK += 8;
      if (pc[17] === D_PWN && pc[1] === D_PWN) score_DARK += 8;  // right pieces
      if (pc[28] === D_PWN) score_DARK += 5;                     // piece at top
    }

    // Penalty for DARK
    if(pc[17] == L_PWN){
      if     (pc[1] == EMPTY && pc[8] == EMPTY) score_LGHT += 17;
      else if(pc[1] == EMPTY && pc[3] == EMPTY) score_LGHT += 16;
      else if(pc[3] == EMPTY)                   score_LGHT += 8;
    }
    if(pc[19] == L_PWN){
      if     (pc[3] == EMPTY && pc[1] == EMPTY) score_LGHT += 17;
      else if(pc[3] == EMPTY && pc[5] == EMPTY) score_LGHT += 17;
      else if(pc[3] == EMPTY && pc[1] == D_PWN && pc[5] == D_PWN) score_LGHT += 8;
      else if(pc[1] == EMPTY && pc[3] == D_PWN && pc[8] == D_PWN) score_LGHT += 8;
      else if(pc[1] == D_PWN && pc[3] == D_PWN) score_LGHT += 8;
    }
    if(pc[21] == L_PWN){
      if     (pc[5] == EMPTY && pc[3] == EMPTY) score_LGHT += 17;
      else if(pc[5] == EMPTY && pc[7] == EMPTY) score_LGHT += 17;
      else if(pc[5] == EMPTY && pc[3] == D_PWN && pc[7] == D_PWN) score_LGHT += 8;
      else if(pc[3] == EMPTY && pc[5] == D_PWN && pc[7] == D_PWN) score_LGHT += 8;
    }
    if(pc[23] == L_PWN){
      if     (pc[5] == EMPTY && pc[7] == EMPTY) score_LGHT += 15;
    }
    if(pc[24] == L_PWN){
      if     (pc[1] == EMPTY && pc[3] == EMPTY && pc[10]== EMPTY && pc[17]== D_PWN) score_LGHT += 17;
    }
    // light pawn is blocked by dark pawn at the back
    if (pc[62] == L_PWN && pc[55] == D_PWN) score_LGHT += 15;
    //if (pc[58] == L_PWN && pc[40] == D_PWN) score_LGHT += 10;

    // allow Horse penalty for LGHT
    /*
    if(pc[63-17] == L_PWN) {
      if   (pc[63-1] == EMPTY && pc[63-8] == EMPTY)     score_DARK += 17;
      else if(pc[63-1] == EMPTY && pc[63-3] == EMPTY)     score_DARK += 16;
      else if(pc[63-3] == EMPTY)            score_DARK += 8;
    }
    if(pc[63-19] == L_PWN) {
      if   (pc[63-3] == EMPTY && pc[63-1] == EMPTY)     score_DARK += 17;
      else if(pc[63-3] == EMPTY && pc[63-5] == EMPTY)     score_DARK += 17;
      else if(pc[63-3] == EMPTY && pc[63-1] == L_PWN && pc[63-5] == L_PWN)
                          score_DARK += 8;
      else if(pc[63-1] == EMPTY && pc[63-3] == L_PWN && pc[63-8] == L_PWN)
                          score_DARK += 8;
      else if(pc[63-1] == L_PWN && pc[63-3] == L_PWN)     score_DARK += 8;
    }
    if(pc[63-21] == L_PWN){
      if   (pc[63-5] == EMPTY && pc[63-3] == EMPTY)     score_DARK += 17;
      else if(pc[63-5] == EMPTY && pc[63-7] == EMPTY)     score_DARK += 17;
      else if(pc[63-5] == EMPTY && pc[63-3] == L_PWN && pc[63-7] == L_PWN)
                          score_DARK += 8;
      else if(pc[63-3] == EMPTY && pc[63-5] == L_PWN && pc[63-7] == L_PWN)
                          score_DARK += 8;
    }
    if(pc[63-23] == L_PWN){
      if   (pc[63-5] == EMPTY && pc[63-7] == EMPTY)     score_DARK += 15;
    }
    */

  }

  //evalTime += (performance.now() - t0);
  return (side_is_L ? score_LGHT - score_DARK : score_DARK - score_LGHT);
}

// global objects to accumulate times
let evalTime = 0, ttTime = 0, genTime = 0;

/* ===== sort/update helpers (optimized) ===== */

function sort_pv() {
  follow_pv = false;
  const b = gen_begin[ply], e = gen_end[ply], t = pv[0][ply];
  for (let i = b; i < e; i++) if (gen_dat[i] === t) {
    follow_pv = true; gen_score[i] += MAXBETA; return;
  }
}

function sort(gf) {
  let bi = gf, bs = gen_score[gf];
  for (let i = gf + 1, ge = gen_end[ply]; i < ge; i++)
    if (gen_score[i] > bs) bs = gen_score[bi = i];
  let tmp = gen_dat[gf]; gen_dat[gf] = gen_dat[bi]; gen_dat[bi] = tmp;
  tmp = gen_score[gf]; gen_score[gf] = gen_score[bi]; gen_score[bi] = tmp;
}

function update_pv(i) {
  const p0 = pv[ply], p1 = pv[ply+1], len = pv_lgth[ply+1];
  p0[ply] = gen_dat[i];
  for (let e = ply + 1; e < len; e++) p0[e] = p1[e];
  pv_lgth[ply] = len;
}


/********************** SEARCH **************************
 
      #####   #####    ###    #####    ####  ##  ## 
     ##       ##      ## ##   ##  ##  ##     ##  ## 
      #####   ####   #######  #####   ##     ###### 
          ##  ##     ##   ##  ## ##   ##     ##  ## 
      #####   #####  ##   ##  ##  ##   ####  ##  ## 

 ********************************************************/

const VALUE_INF = 10000;
const MINALPHA = -VALUE_INF, MAXBETA = VALUE_INF;

function search(alpha, beta, depth) {
  // TT-aware search: probe at entry and store at exit
  if (depth === 0) return quiesce(alpha, beta);

  const zkey = ttHash();
  const tt = ttProbe(zkey, depth, alpha, beta);
  if (tt.bestMove && ply === 0) pv[0][0] = tt.bestMove;

  if (tt.hit) return tt.score;

  pv_lgth[ply] = ply;
  gen(GEN_ALL);

  if (gen_end[ply] == gen_begin[ply]) {
    // --- terminal ---
    const score = -VALUE_INF + ply;
    ttStore(zkey, depth, TT_EXACT, score, 0);
    return score;
  }

  if ((gen_end[ply] - gen_begin[ply]) == 1)
   // forced move extension
    if (L_PWN_cnt > 1 && D_PWN_cnt > 1) depth++;

  if (follow_pv) sort_pv();

  let alphaOrig = alpha;
  let bestMove  = 0;
  let bestScore = -VALUE_INF;

  for (let i = gen_begin[ply]; i < gen_end[ply]; i++) {
    sort(i);
    makemove(gen_dat[i]);
    let score = -search(-beta, -alpha, depth - 1);
    takeback();
    if (score > bestScore) {
      bestScore = score;
      bestMove  = gen_dat[i];
    }

    // --- beta cutoff ---
    if (score >= beta) {
      ttStore(zkey, depth, TT_BETA, score, gen_dat[i]);
      return score; // fail-soft
    }

    // --- alpha improve ---
    if (score > alpha) {
      alpha = score;
      ADD_MOV_VAL(TO(gen_dat[i]), FM(gen_dat[i]), depth);
      update_pv(i);
    }
  }

  // --- store result ---
  const flag = (bestScore > alphaOrig) ? TT_EXACT : TT_ALPHA;
  ttStore(zkey, depth, flag, bestScore, bestMove);

  return bestScore;
}


function quiesce(alpha, beta) {

  pv_lgth[ply] = ply;

  // --- Stand pat evaluation ---
  let stand = myeval();
  if (stand >= beta) return stand; // fail-soft cutoff
  if (stand > alpha) alpha = stand;

  // --- Generate captures ---
  gen(ONLY_BITS);
  if (gen_end[ply] === gen_begin[ply]) return stand; // quiet position

  if (follow_pv) sort_pv();

  // --- Search captures ---
  for (let i = gen_begin[ply]; i < gen_end[ply]; i++) {
    sort(i);
    makemove(gen_dat[i]);
    let score = -quiesce(-beta, -alpha);
    takeback();
    if (score >= beta) return score; // fail-soft beta cutoff
    if (score > alpha) { alpha = score; update_pv(i); }
  }

  return alpha;                // best capture line
}


/***********************************************
                MAKEMOVE/TAKEBACK
************************************************/

function makemove(mv){ const from = FM(mv), to = TO(mv); hist_dat[ply]=mv;
  if(mv & MSKIP){ ply++; if(ply>maxply) maxply=ply; revSide(); return true; }
  if(mv & MCAPTURE){ let cpos = (from>to ? (PFILE(from)>PFILE(to)? to+9:to+7) : (PFILE(from)>PFILE(to)? to-7:to-9)); hist_cap[ply]=cpos; switch(pc[cpos]){case L_PWN:L_PWN_cnt--;break;case D_PWN:D_PWN_cnt--;break;case L_HRS:L_HRS_cnt--;break;case D_HRS:D_HRS_cnt--;break;} pieceCount--; pc[cpos]=EMPTY; } else hist_cap[ply]=-1;
  if(mv & MPROMOTE){ switch(pc[from]){ case L_PWN: pc[to]=L_HRS; L_HRS_cnt++; L_PWN_cnt--; break; case D_PWN: pc[to]=D_HRS; D_HRS_cnt++; D_PWN_cnt--; break; } } else pc[to]=pc[from];
  pc[from]=EMPTY; ply++; revSide(); return true;
}
function takeback(){ revSide(); ply--; const mv = hist_dat[ply], from = FM(mv), to = TO(mv); if(mv & MSKIP) return; 
  if(mv & MPROMOTE){ switch(pc[to]){ case L_HRS: pc[from]=L_PWN; L_HRS_cnt--; L_PWN_cnt++; break; case D_HRS: pc[from]=D_PWN; D_HRS_cnt--; D_PWN_cnt++; break; } } else pc[from]=pc[to]; 
  if(mv & MCAPTURE){ let cpos=hist_cap[ply]; pc[cpos]=(CAPPIECE(mv)|xside); switch(pc[cpos]){case L_PWN:L_PWN_cnt++;break;case D_PWN:D_PWN_cnt++;break;case L_HRS:L_HRS_cnt++;break;case D_HRS:D_HRS_cnt++;break;} pieceCount++; } pc[to]=EMPTY; }


/******************** THINK ************************
 
     #######  ##  ##   ####   ##   ##   ##   ## 
       ##     ##  ##    ##    ###  ##   ##  ##  
       ##     ######    ##    ## # ##   #####   
       ##     ##  ##    ##    ##  ###   ##  ##  
       ##     ##  ##   ####   ##   ##   ##   ## 

 *************************************************/

const MIN_THINK_MS = 500, MAX_THINK_MS = 5000; // time to think in ms
const MAX_EXTRA_DEPTH = 3; // how many extra depths allowed beyond targetDepth
let prvBestMove = 0, curBestMove = 0, curBestScore = -9999;

async function think(){
  const t0 = performance.now();   // start time
  ply=0; maxply=0; mov_val_flat.fill(0);
  let score=0, depth=1, elapsed=0;
  //prvBestMove = 0; curBestMove = 0;
  const extraDepth = Math.min(MAX_EXTRA_DEPTH, Math.max(0, (16-pieceCount) >> 1));

  while(true) {
    if(depth >= 10) await yieldThread(depth, score, elapsed, MIN_THINK_MS); // update UI
    prvBestMove = curBestMove;
    follow_pv = true; score = search(MINALPHA, MAXBETA, depth);
    curBestMove = pv[0][0], curBestScore = score;
    //console.log(FM(prvBestMove), FM(pv[0][0]));

if(DEBUG) console.log(depth,score,FM(pv[0][0]),TO(pv[0][0]));
//console.log("in think, after search: targetDepth",depth,"score",score,"mv",FM(gen_dat[0]),TO(gen_dat[0]));

    elapsed = performance.now() - t0;
    if(elapsed >= MAX_THINK_MS) break; // time limit
    if(depth >= targetDepth && score < -9988) return false; // mate loss
    if(depth >= targetDepth && elapsed >= MIN_THINK_MS
      && (score <= -300 || score >= 300 || depth >= targetDepth + extraDepth)) break;
    if(DEBUG && depth >= targetDepth) break;
    depth++;

//console.log("in think, after search: targetDepth",depth,"score",score,"mv",FM(gen_dat[0]),TO(gen_dat[0]));

  }
  if(score>200) { showStyleIconIcon(false); showNewGame(true); }
  thinkTime = performance.now() - t0; // end total time
  if(thinkTime < 1000) thinkTime = 1000; // at least 1 second
  compSeconds -= Math.floor(thinkTime/1000); if(compSeconds<0) compSeconds=0;
  //startPlayerTimer(); // update comp timer
  if(DEBUG) console.log("d",depth,"t",(thinkTime).toFixed(0),"sc",score,"tt",ttStoreCnt,ttHitCnt,ttProbeCnt,ttCollision,"eg",egHitCnt,egProbeCnt,"dw",drawCount);
  ttHitCnt=0; ttProbeCnt=0; egHitCnt=0; egProbeCnt=0;
  evalTime=0; ttTime=0; genTime=0;
  return true;
}

async function yieldThread(depth, score, elapsed) {
  /*
  //updateTimeDisplay();
  //if(gen_end[0]>0) await animateSelect(FM(gen_dat[0]));
  console.log(moveCount, depth, elapsed.toFixed(0), pieceCount, score, TO(prvBestMove), TO(curBestMove));
  if (chance(0.99) && pieceCount > 10 //&& elapsed >= MIN_THINK_MS * 0.9  
      //&& moveCount > MID_GAME && score >= -150 && score <= -50
      && prvBestMove > 0 && curBestMove > 0 && FM(prvBestMove) != FM(curBestMove) 
     ) await doThinkGesture(FM(prvBestMove), FM(curBestMove));
  else await holdMs(100); // give UI breathing time
  */
  await holdMs(100);
}

async function holdMs(ms = PAUSE) {
  await new Promise(res => setTimeout(res, DEBUG ? 20 : ms)); // sleep for ms
}


/**************** MAIN LOOP ***********************
 
          ##    ##    ###    ####  ##   ## 
          ###  ###   ## ##    ##   ###  ## 
          ## ## ##  #######   ##   ## # ##    
          ##    ##  ##   ##   ##   ##  ###   
          ##    ##  ##   ##  ####  ##   ##  
 
 **************************************************

  Game States
  -----------
  GS_NONE : Game not started / game over
  GS_LGHT : Waiting for player to select a piece
  GS_LMOV : Player selected piece, waiting for destination
  GS_DARK : AI is thinking / moving

  Note: computer always plays the Dark side
*/

async function aiMainLoop(){
  //bCompBusy=true;
  setNewGameEnabled(false); // disable newgame button
  for(;;){
    let msg="";
    // dark turn
    moveCount++; ply=0; gen(GEN_ALL);
    let bestmv=0; pv[0][0]=0; prvBestMove=0; curBestMove=0; // reset vars
    if(gen_end[0]===0){ gameOver(1); break; }
    if(gen_end[0]===1){ bestmv=gen_dat[0]; await holdMs(20); }
    if(moveCount < 4 && bestmv===0){ // force opening moves
      bestmv = forceOpeningMove();
      if(bestmv!==0) { msg+="..."; await holdMs(500); }
    }
    if(USE_BK && moveCount > 6 && bestmv===0 && chance(0.8)) { // 80% to use opening book
      const bk_mv = bkProbe();
      if(bk_mv) { bestmv=bk_mv; msg+=".."; await holdMs(500); }
    }
    if(bestmv===0){ 
      if(await think()===false){ gameOver(1); break; }
      bestmv=pv[0][0];
      //bestmv=bestMoveSoFar; 
    }
    if(!(gen_dat[0] & MSKIP)) { 
      bCompBusy = true; drawPieces(); 
      await animateMove(bestmv); 
      bCompBusy = false;
    }
    makemove(bestmv); lastmove=bestmv; 
    addMoveToHistory(bestmv);
    if(!(lastmove & MSKIP)) lastmoveCap = TO(bestmv);
    if(BITS(lastmove)===MMOVE && pc[TO(lastmove)]===D_HRS){ 
      drawCount++; 
      if(checkDraw()){ gameOver(0); break; } 
    } else drawCount=0;
    drawPieces();

    // light turn
    msg="ตาคุณเดิน"+msg;
    moveCount++; ply=0; gen(GEN_ALL);
    if(gen_dat[0] & MSKIP){
      makemove(MSKIP); lastmove=MSKIP; ply=0; gen(GEN_ALL); continue; 
    }
    if(gen_end[0]===0){ gameOver(-1); break; } // light can't move
    if(gen_end[0]>=1) {
      let fm0=FM(gen_dat[0]);
      for(let i=1; i<gen_end[0]; i++)
        if(FM(gen_dat[i]) !== fm0) { fm0 = -1; break; }
      if(fm0 >= 0) {
        selectedCell=fm0; pieceSelected=true; gameState=GS_LGHT;
        message(msg); drawPieces(); break;
      }
    }

    gameState=GS_LGHT; pieceSelected=false; message(msg); break;
  }

  // wait user to play
  if(gameState===GS_LGHT) { setNewGameEnabled(true); startPlayerTimer(); }
  //bCompBusy=false; 
}

function forceOpeningMove() {
  if (DEBUG) return 0;
  let mv = 0;
  if(compFirst) { 
    switch(moveCount) {
      case 1: mv = (21 | RTO(28) | MMOVE); break;
      case 3: mv = ( 7 | RTO(14) | MMOVE); break;
      //case 5: mv = (14 | RTO(21) | MMOVE); break;
      default: mv = 0;
    }
  } else {
    switch(moveCount) {
      case 1: mv = (14 | RTO(21) | MMOVE); break;
      case 3: mv = ( 7 | RTO(14) | MMOVE); break;
      //case 5: mv = (12 | RTO(19) | MMOVE); break;
      default: mv = 0;
    }
  }
  return mv;
}

const VISIT_LOG_URL = "https://chnp.co.th/makhos/visit.php?";

function gameOver(r) { // +1 player won, 0 draw, -1 player lost
  const result = r>0 ? "W" : (r<0 ? "L" : "D");
  const elapsed = Math.round((performance.now() - gameStartTime) / 1000);
  gameResultStr += level + result + " ";
  //console.log(gameCount,level,result,elapsed,gameResultStr,moveHistoryStr);
  //fetch(VISIT_LOG_URL + "level=" + level + "&result=" + result); // log
  let url = VISIT_LOG_URL + "level=" + level + "&result=" + encodeURIComponent(gameResultStr);
  if (level > 0 && result === "W") url += "&moves=" + encodeURIComponent(moveHistoryStr);
  fetch(url); // log
  const msg = r>0 ? "คุณชนะ" : (r<0 ? "คุณแพ้" : "เสมอกัน");
  message(msg + "!, เริ่มเกมใหม่");
  showOverlay(msg);
  // update level
  /*if(r!==0) {
    level+=r; if(level<0) level=0; if(level>MAX_LEVEL) level=MAX_LEVEL;
  }*/
  updateLevel(r);
  targetDepth = BASE_DEPTH + (level-1);
  if(level<=0) targetDepth = BASE_DEPTH; // safeguard
  gameState = GS_NONE; stopPlayerTimer();
}

const DRAW_MIN=6, DRAW_MAX=25;

function checkDraw() {
  updatePieceCode();
  if(pieceCode==1010 && (pc[7]===EMPTY || pc[48]===EMPTY)) return(true);
  if(drawCount < DRAW_MIN) return(false);
  if(drawCount > DRAW_MAX) return(true);
  if(pieceCode==1111) return true; // move only hrs for 6 times
  return false; 
}

function updateLevel(r) {
  prevLevel = level;
  if       (r > 0) { winStreak++; loseStreak=0; }
  else if  (r < 0) { winStreak=0; loseStreak++; }
  else             { winStreak=0; loseStreak=0; }
  if (r > 0 && prevLevel===0) { level=1; winStreak=loseStreak=0; } // win level 0
  else {
    if (winStreak === 2) { level++; winStreak =0; }
    if (loseStreak=== 2) { level--; loseStreak=0; }
  }
  level = Math.max(0, Math.min(MAX_LEVEL, level));
}

/* =================== Timer ==================== */
let thinkTime = 0;
let playerSeconds = 180, compSeconds = 180;  // 3 minutes
let playerInterval = null, compInterval = null;

function formatTime(sec) {
  const m = Math.floor(sec / 60);
  const s = sec % 60;
  return m + ":" + (s < 10 ? "0" + s : s);
}

function updateTimeDisplay() {
  compTimeElm.textContent = formatTime(compSeconds);
  playerTimeElm.textContent = formatTime(playerSeconds);
  if (compSeconds <= 0) compTimeElm.style.color = "#fd0";
  if (playerSeconds <= 0) playerTimeElm.style.color = "#fd0";
}

function startPlayerTimer() {
  compTimeElm.style.color = "#aaa";
  playerTimeElm.style.color = "#eee";
  updateTimeDisplay();
  if (playerInterval) clearInterval(playerInterval);
  playerInterval = setInterval(() => {
    if (playerSeconds > 0) playerSeconds--;
    updateTimeDisplay();
  }, 1000);
}

function stopPlayerTimer() {
  compTimeElm.style.color = "#eee";
  playerTimeElm.style.color = "#aaa";
  if (playerInterval) clearInterval(playerInterval);
  playerInterval = null;
  updateTimeDisplay();
}

function resetClock() {
  playerSeconds = compSeconds = 180;
  compTimeElm.style.color = "#aaa";
  playerTimeElm.style.color = "#eee";
}

function hideTimers() {
  compTimeElm.textContent = " ";
  playerTimeElm.textContent = " ";
}


/******************** THINK ************************
 
              ########   ########  
                 ##         ##
                 ##         ##
                 ##         ##
                 ##         ##

 *************************************************/

//============= Zobrist Key ===============

let zobrist_piece = null, zobrist_side = 0n;

function rand64(seed) {
  const A = 6364136223846793005n;
  const C = 1n;
  const MASK = (1n << 64n) - 1n;
  return (BigInt(seed) * A + C) & MASK;
}

function initZobrist() {
  let seed = 124987n; // fixed initial prime seed
  zobrist_piece = [];
  for (let sq = 0; sq < 32; sq++) {
    zobrist_piece[sq] = [];
    for (let p = 0; p < 10; p++) {   // 10 entries for both side
      seed = rand64(seed);           // update seed for each entry
      zobrist_piece[sq][p] = seed;   // assign value
    }
  }
  seed = rand64(seed);               // one more for side
  zobrist_side = seed;
}

/***********************************************
              Transposition Table
************************************************/

const TT_EXACT = 0, TT_ALPHA = 1, TT_BETA = 2;

// ---------- Typed-array TT declarations (replace Map-based TT) ----------
const TT_POW = USE_TT ? 21 : 8; // 2^21 = 2M entries
const TT_SIZE = 1 << TT_POW;
const TT_MASK = TT_SIZE - 1;
let ttHitCnt = 0, ttProbeCnt = 0, ttStoreCnt = 0, ttCollision = 0;

// typed arrays for TT (bounded memory, contiguous)
const tt_keylo = new Uint32Array(TT_SIZE); // low 32 bits of zobrist
const tt_keyhi = new Uint32Array(TT_SIZE); // high 32 bits (for full-64 equality check)
const tt_depth = new Int16Array(TT_SIZE);
const tt_flag  = new Int8Array(TT_SIZE);
const tt_score = new Int32Array(TT_SIZE);
const tt_move  = new Int32Array(TT_SIZE);

function ttProbe(key64, depth, alpha, beta) {
  if (!USE_TT) return { hit: false, bestMove: 0 };
  //if (side === LGHT) return { hit: false, bestMove: 0 };
  //if (!USE_TT || pieceCount <= 4) return { hit: false, bestMove: 0 };
  ttProbeCnt++;
  //const { hi, lo } = splitKeyTo32(key64);
  const lo = Number(key64 & 0xffffffffn) >>> 0;
  const hi = Number((key64 >> 32n) & 0xffffffffn) >>> 0;
  const idx = lo & TT_MASK; // use low bits for index

  if (tt_keylo[idx] !== lo || tt_keyhi[idx] !== hi) { // missed
    return { hit: false, bestMove: 0 };
  }
  // matched
  const d = tt_depth[idx], f = tt_flag[idx], m = tt_move[idx];
  const s = scoreFromTT(tt_score[idx], ply);

  if (d >= depth) {
    ttHitCnt++;
//let pcs=""; for (let i=0;i<32;i++){ pcs += pc[pcConv[i]] + ((i%4===3) ? " " : ""); }
//console.log(boardToText());
//console.log("probe idx",idx,"key",hi.toString(16),lo.toString(16),"targetDepth",d,"mv",FM(m),TO(m),"f",f,"sc",s,"side",side);
    if (f === TT_EXACT) return { hit: true, score: s, bestMove: m };
    if (f === TT_ALPHA && s <= alpha) return { hit: true, score: s, bestMove: m };
    if (f === TT_BETA  && s >= beta)  return { hit: true, score: s, bestMove: m };
  }
  // Key matches but score unusable
  return { hit: false, score: 0, bestMove: m };
}

function ttStore(key64, depth, flag, score, bestMove) {
  if (!USE_TT) return;
  //if (side === LGHT) return; // store only dark to move
  if (depth === 0) return; // skip if depth is 0
  //if (pieceCount <= 4) return; // skip if endgame
  //const t0 = performance.now();
  ttStoreCnt++;
  //const { hi, lo } = splitKeyTo32(key64);
  const lo = Number(key64 & 0xffffffffn) >>> 0;
  const hi = Number((key64 >> 32n) & 0xffffffffn) >>> 0;
  const idx = lo & TT_MASK;
  score = scoreToTT(score, ply);
//let pcs=""; for (let i=0;i<32;i++){ pcs += pc[pcConv[i]] + ((i%4===3) ? " " : ""); }
//console.log(boardToText());
//console.log("put s",side,"d",depth,"v",score,"mv",FM(bestMove),TO(bestMove));
//console.log(boardToText());
//console.log("store idx",idx,"key",hi.toString(16),lo.toString(16),"targetDepth",depth,"mv",FM(bestMove),TO(bestMove),"sc",score,"side",side);
  // always store if slot is empty
  if (tt_keyhi[idx] === 0 && tt_keylo[idx] === 0) {
    tt_keylo[idx] = lo;
    tt_keyhi[idx] = hi;
    tt_depth[idx] = depth > 0 ? depth : 1; // avoid depth=0
    tt_flag[idx]  = flag;
    tt_score[idx] = score;
    tt_move[idx]  = bestMove | 0;
    return;
  }

  //return; 

  const oldKeylo = tt_keylo[idx];
  const oldKeyhi = tt_keyhi[idx];
  const oldDepth = tt_depth[idx];
  const oldFlag  = tt_flag[idx];

  // COLLISION: different position, always replace
  if (oldKeyhi !== hi || oldKeylo !== lo) {
    tt_keylo[idx] = lo;
    tt_keyhi[idx] = hi;
    tt_depth[idx] = depth;
    tt_flag[idx]  = flag;
    tt_score[idx] = score;
    tt_move[idx]  = bestMove | 0;
    
    //console.log("collision",depth,flag);
    return;
  }

  //return;
  ttCollision++;

  // otherwise, replace if deeper and not EXACT. tested 3-Feb-2026 and result was better
  if (oldKeyhi === hi && oldKeylo === lo) {

    // do not replace exact with bound
    if (oldFlag === TT_EXACT && flag !== TT_EXACT) return;
    // deeper wins unless new is exact
    if (depth < oldDepth && flag !== TT_EXACT) return;
    // Do not overwrite deeper EXACT with shallower EXACT
    if (flag === TT_EXACT && oldFlag === TT_EXACT && depth < oldDepth) return;

    // replace existing data
    tt_depth[idx] = depth;
    tt_flag[idx]  = flag;
    tt_score[idx] = score;
    tt_move[idx]  = bestMove | 0;
    return;
  }

}


function ttHash() { // for TT
  if (!USE_TT) return 0n;
  const zp = zobrist_piece; //const conv = pcConv; // local alias
  let h = 0n;
  for (let i = 0; i < 32; i++) {
    const sq = pcConv[i], p = pc[sq], zpSq = zp[i];
    if(p >= 4 || p < 0) continue; // p is not pieces
    h ^= zpSq[p];  
  }
  if (side === DARK) h ^= zobrist_side;
  return h;
}

function ttClear() {
  for (let i = 0; i < TT_SIZE; i++) {
    tt_keylo[i] = 0;
    tt_keyhi[i] = 0;
    tt_depth[i] = 0;
    tt_flag[i]  = 0;
    tt_score[i] = 0;
    tt_move[i]  = 0;
  }
  ttHitCnt = 0;
  ttProbeCnt = 0;
  ttStoreCnt = 0;
  ttCollision = 0;
  //console.log("New game, TT cleared");
}

function scoreToTT(score, ply) {
  if (score > 9000) return score + ply;
  if (score < -9000) return score - ply;
  return score;
}

function scoreFromTT(score, ply) {
  if (score > 9000) return score - ply;
  if (score < -9000) return score + ply;
  return score;
}


/********************* ENDGAME **********************
 
                   ######   ###### 
                   ##      ##     
                   #####   ##  ###  
                   ##      ##   ## 
                   ######   ######  

 ****************************************************/


/*---------------------------------------------------
 Note: original jaihorse endgameDB zsys4p.txt

#################
#      2p       #
#################
#0110 default -
tyyyeyyyyyyyyyyy.
xyyyeyyyyyyyyyyy.
ytyyeyyyyyyyyyyy.
...
vyyfvyyyyyyyyyyy.
yyygyjyuyyyyyyyy.
yyyygyvyeyyyyyyy.
#0103 cnt=72632 err=0 +/7 ./143 -/72482

replace y with number of y (yyyyeyyyyyyyyyyy. = 4e10)
write to description2.txt and zip to background2.zip

t3e11.
x3e11.
1t2e11.
...
v2fv11.
3g1j1u8.
4g1v1e7.

read file, restore y, conv to pc[], create zorist key
-----------------------------------------------------*/
const EG_D = 1;  // draw
const EG_W = 2;  // light win
const EG_L = 3;  // light loss

let egdbLoaded = 0;
const egStats = new Map(); // key = pieceCode, value = { win:0, draw:0, loss:0, total:0, def:0 }

// typed arrays
const EG_POW = 21; // 2M
const EG_SIZE = 1 << EG_POW;
const EG_MASK = EG_SIZE - 1;
const MASK_63 = (1n << 63n) - 1n; // all bits 0–62 are 1, bit 63 is 0

const eg_keylo = new Uint32Array(EG_SIZE);
const eg_keyhi = new Uint32Array(EG_SIZE);
const eg_value = new Uint8Array(EG_SIZE);

let egProbeCnt = 0, egHitCnt = 0;
let max_shift = 0;


// hash position for endgame, diff key for light and dark side
function egHash() {
  if (!USE_EG) return 0n;
  const isLght = (side === LGHT);
  const zp = zobrist_piece;
  const conv = isLght ? pcConv : pcFlip;
  let h = 0n;
  for (let i = 0; i < 32; i++) {
    const sq = pcConv[i];
    const zpSq = zp[i];
    let p = pc[sq];
    if(p >= 4 || p < 0) continue; // p is not pieces or empty
    if (!isLght && p !== EMPTY) p ^= 1; // flip piece if dark
    h ^= zpSq[p];
  }
  return h & MASK_63;  // return 63-bit unsigned bigint
}

// ----------- STORE -----------
function egStore(zkey, value) {
  if (!USE_EG) return false;
  const kLo = Number(zkey & 0xffffffffn);
  const kHi = Number(zkey >> 32n);
  let idx  = kLo & EG_MASK;
  const step = kHi | 1;
  for (let p = 0; p < EG_SIZE; p++) {
    const v = eg_value[idx];
    if (v === 0) {
      eg_keylo[idx] = kLo; eg_keyhi[idx] = kHi; eg_value[idx] = value;
      if(p > max_shift) max_shift = p;
      //if(p>5) console.log(boardToText());
      return true;
    }
    if (eg_keylo[idx] === kLo && eg_keyhi[idx] === kHi) return false; // duplicate zkey
    idx = (idx + step) & EG_MASK;
  }
  return false; // overflow
}

// ----------- PROBE -----------
function egProbe(zkey) { // Ultra-Fast tuning, exit in few operations
  if (!USE_EG) return 0;
  egProbeCnt++;
  const kLo = Number(zkey & 0xffffffffn);
  const kHi = Number(zkey >> 32n);
  let idx  = kLo & EG_MASK;
  const v0 = eg_value[idx];
  if (v0 === 0) return 0; // no data
  if (eg_keylo[idx] === kLo && eg_keyhi[idx] === kHi) { egHitCnt++; return v0; } // 1st slot
  const step = kHi | 1;
  idx = (idx + step) & EG_MASK;
  const v1 = eg_value[idx];
  if (v1 === 0) return 0; // chain stopped, no data
  if (eg_keylo[idx] === kLo && eg_keyhi[idx] === kHi) { egHitCnt++; return v1; } // 2nd slot
  // ---- FALLBACK (rare) ----
  for (let p = 2; p <= max_shift; p++) {
    idx = (idx + step) & EG_MASK;
    const v = eg_value[idx];
    if (v === 0) return 0; // chain stopped, no data
    if (eg_keylo[idx] === kLo && eg_keyhi[idx] === kHi) { egHitCnt++; return v; } // others
  }
  //console.log("px");
  return 0;
}

// ---------- loadEGDB ----------
async function loadEGDB(zipUrl="background2.jpg", innerFile="description2.txt") {
  try {
    if (!USE_EG) { egdbLoaded = 1; return; }
    const response = await fetch(zipUrl);
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    const blob = await response.blob();
    const zip = await JSZip.loadAsync(blob);
    const file = zip.file(innerFile);
    if (!file) throw new Error(`File ${innerFile} not found`);
    const text = await file.async("text");

    eg_keylo.fill(0); eg_keyhi.fill(0); eg_value.fill(0);

    side = LGHT;
    let count = 0, dup = 0, collision = 0;

    const lines = text.split('\n').map(l => l.trim())
      .filter(l => l && !l.startsWith('#'));

    for (const line of lines) {
      const mapVal = { '.':EG_D, '+':EG_W, '-':EG_L };
      const value = mapVal[line[line.length-1]] || 0;
      const rleDb = line.substring(0, line.length-1);
      const fullDb = expandRLE(rleDb);
      if (fullDb.length !== 16) continue;

      decodeDb(fullDb);

      const zkey = egHash();
      if (!egStore(zkey, value)) collision++;
      else count++;
    }

    pc.set(pc_init); side = LGHT;
    egdbLoaded = count;
    //console.log("EGDB",egdbLoaded,"DUP",collision,"SHF",max_shift);

  } catch (err) {
    //console.error("EGDB Failed:", err);
  }
}

// ---------- helper to rotate 32-bit ----------
//function rotr32(x, r) { r &= 31; return (x >>> r) | (x << (32 - r)); }

function expandRLE(rle) {
  let out = "", i = 0;
  while (i < rle.length) {
    let c = rle[i];
    if (c >= '0' && c <= '9') {
      let j = i + 1;
      if (j < rle.length && rle[j] >= '0' && rle[j] <= '9') j++; // support 2-digit (1–99)
      const run = parseInt(rle.slice(i, j), 10);
      out += "y".repeat(run); i = j;
    } else { out += c; i++; }
  }
  return out;
}

function decodeDb(s) {
  const enc = [L_PWN, D_PWN, L_HRS, D_HRS, EMPTY];
  for (let i = 0; i < 32; i++) pc[pcConv[i]] = EMPTY;
  let idx = 0;
  for (let i = 0; i < 16; i++) {
    const v = s.charCodeAt(i) - 97;   // 'a' is 0
    let c0 = Math.floor(v / 5);       // first cell
    let c1 = v % 5;                   // second cell
    pc[pcConv[idx++]] = enc[c0];
    pc[pcConv[idx++]] = enc[c1];
  }
}

// ====== QUERY ENDGAME DB ======

// [ LH ][ LP ][ DH ][ DP ]  1=Draw, 2=LWin, 3=Llost
const dxMap = new Map([
  [1001, 2], [ 110, 3], [ 101, 1], [1010, 1], // 2p
  [2010, 2], [1020, 3], [1110, 2], [1011, 3], [ 210, 2], [1002, 3], // 3p
  [2001, 2], [ 120, 3], [1101, 2], [ 111, 3], [ 201, 2], [ 102, 3],
  [2020, 1], [2011, 2], [2002, 2], [ 220, 3], [ 211, 3], [ 202, 1], 
  [1120, 3], [1111, 1], [1102, 2], // 4p
  [2110, 2], [2101, 2], [1021, 3], [ 121, 3],
  [1210, 2], [1201, 2], [1012, 3], [ 112, 3],
  [3010, 2], [3001, 2], [1030, 3], [ 130, 3],
  [ 310, 2], [ 301, 2], [1003, 3], [ 103, 3],
]);
function getdx(code){ return dxMap.get(code) ?? 0; }


/*
// Zobrist hash position
function ttHash32(s) {
  const zp = zobrist_piece32;
  let h = 0 >>> 0;
  for (let i = 0; i < 32; i++) {
    const sq = pcConv[i];
    const p  = pc[sq];
    if (p >= 0 && p < 5) h ^= zp[i][p];
  }
  //if (s === DARK) h ^= zobrist_side32;
  return h >>> 0;
}

// ---- 32-bit Zobrist (for EGDB) ----
function rand32(seed) { return (seed * 1664525 + 1013904223) >>> 0; }

let zobrist_piece32 = null; // [sq][p] -> uint32
let zobrist_side32 = 0;

function initZobrist32(seedInit = 123456) {
  // seedInit: 32-bit integer seed
  let seed = seedInit >>> 0;
  zobrist_piece32 = [];
  for (let sq = 0; sq < 32; sq++) {
    zobrist_piece32[sq] = new Uint32Array(6); // p in 0..4 used, keep extra slot safe
    for (let p = 0; p < 10; p++) {              // allocate a bit extra
      seed = rand32(seed);
      zobrist_piece32[sq][p] = seed >>> 0;
    }
  }
  zobrist_side32 = rand32(seed) >>> 0;
}
*/
/* ------------------------ End of Endgame patch ---------------------- */


/******************** BOOK ************************
 
         #####    #####    #####   ##   ## 
         ##  ##  ##   ##  ##   ##  ##  ##  
         #####   ##   ##  ##   ##  #####   
         ##  ##  ##   ##  ##   ##  ##  ##  
         #####    #####    #####   ##   ## 

 *************************************************/


// ---------------- BOOK DATABASE -----------------
const bk_map = new Map();     // key → bestmove
let bkdbLoaded = 0;

// ---------------- LOAD BOOK ----------------------
async function loadBKDB(zipUrl = "DB0508.zip", innerFile = "DB0508.txt") {
  try {
    bk_map.clear(); bkdbLoaded = 0;
    const response = await fetch(zipUrl);
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    const blob = await response.blob();
    const zip = await JSZip.loadAsync(blob);
    const file = zip.file(innerFile);
    if (!file) throw new Error(`File ${innerFile} not found`);
    const text = await file.async("text");
    const lines = text.split('\n').map(x => x.trim())
      .filter(x => x.length >= 21);   // 16 hex + 5 hex = 21 chars min
    for (const line of lines) {
      const boardHex = line.substring(0, 16);
      const moveHex  = line.substring(16, 21);
      const key = BigInt("0x" + boardHex);
      const mov = Number("0x" + moveHex);
      if (!bk_map.has(key)) bk_map.set(key, []); // create array
      bk_map.get(key).push(mov); // add move to array
      bkdbLoaded++;
    }
    //console.log("BOOK LOADED", bkdbLoaded);
  } catch (err) {
    //console.error("BOOK LOAD FAILED:", err);
  }
}

function bkProbe() {
  const key = boardEncode();
  const list = bk_map.get(key);
  if (!list) return null;
  let mov = list[Math.floor(Math.random() * list.length)];
  mov = BITS(mov) | RTO(63-TO(mov)) | (63-FM(mov));
  //console.log("BK", key.toString(16), list.length, BITS(mov).toString(16), TO(mov), FM(mov));
  return mov;
}

// Encode the current board, tuned for speed
function boardEncode() { 
  /*
  const enc = [4n, 5n, 6n, 7n];
  let l = 0n;
  for (let i = 0; i < 32; i++) { 
    const p = pc[pcConv[i]]; 
    l = (l * (p >= EMPTY ? 2n : 8n)) | (p >= EMPTY ? 0n : enc[p]); 
  }
  /*/
  const isLght = (side === LGHT); 
  const enc = (isLght ? [4n, 5n, 6n, 7n] : [5n, 4n, 7n, 6n]); 
  let l = 0n; 
  if (isLght) { 
    for (let i = 0; i < 32; i++) { 
      const p = pc[pcConv[i]]; 
      l = (l * (p >= EMPTY ? 2n : 8n)) | (p >= EMPTY ? 0n : enc[p]); 
    }
  } else { 
    for (let i = 31; i >= 0; i--) { 
      const p = pc[pcConv[i]]; 
      l = (l * (p >= EMPTY ? 2n : 8n)) | (p >= EMPTY ? 0n : enc[p]); 
    } 
  } 
  return l; 
}


// for debug purpose
function boardToText(){
  const sym = ["o","x","@","#","."," "];
  let s = "";
  for(let r=0;r<8;r++){
    for(let c=0;c<8;c++) s += sym[pc[r*8+c]];
    s += "\n";
  }
  return s;
}

function revSide() { side = side===LGHT ? DARK : LGHT; xside = side===LGHT ? DARK : LGHT; }


/* Expose minimal API for HTML buttons */
/*window.newgameClicked = async ()=>{ 
  gameOver(-1); await holdMs(500); await startGame(); gameState=GS_LGHT; 
};*/
window.init = init;
