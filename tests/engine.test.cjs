'use strict';
const test = require('node:test');
const assert = require('node:assert/strict');
const { Game, chooseComputerMove } = require('../game/engine.js');

function play(rows, columns, sequence) {
  const g = new Game(rows, columns);
  for (const c of sequence) assert.equal(g.drop(c).ok, true, `illegal move ${c} in ${sequence}`);
  return g;
}
function referenceWinner(g) {
  const winners = new Set();
  for (let c = 0; c < g.columns; c++) for (let r = 0; r < g.rows; r++) {
    const p = g.cell(c, r); if (!p) continue;
    for (const [dx, dy] of [[1,0],[0,1],[1,1],[1,-1]]) {
      if ([1,2,3].every(n => g.cell(c + n*dx, r + n*dy) === p)) winners.add(p);
    }
  }
  return [...winners];
}

test('gravity, alternating turns, invalid moves and full columns leave state intact', () => {
  const g = new Game(2, 3);
  assert.deepEqual(g.drop(1).move, { column:1, row:0, player:1 });
  assert.deepEqual(g.drop(1).move, { column:1, row:1, player:2 });
  const old = JSON.stringify(g.toRecord());
  for (const c of [1, -1, 3, 1.5, '0', NaN, null]) assert.equal(g.drop(c).ok, false);
  assert.equal(JSON.stringify(g.toRecord()), old);
});

test('horizontal and vertical wins stop play immediately', () => {
  for (const g of [play(6,7,[0,0,1,1,2,2,3]), play(4,2,[0,1,0,1,0,1,0])]) {
    assert.equal(g.status,'won'); assert.equal(g.winner,1); assert.equal(g.winningCells.length,4);
    assert.equal(g.drop(g.legalColumns()[0] ?? 0).ok,false);
    assert.equal(g.undo(),true); assert.equal(g.status,'playing'); assert.equal(g.turn,1);
  }
});

test('both diagonal orientations are detected from legal move sequences', () => {
  const seq=[0,1,1,2,3,2,2,3,4,3,3];
  for (const moves of [seq,seq.map(c=>6-c)]) {
    const g=play(6,7,moves);assert.equal(g.status,'won');assert.equal(g.winner,1);
    assert.equal(g.winningCells.length,4);
  }
});

test('a win on the last empty square takes precedence over a full-board draw', () => {
  // White completes the top horizontal line on move 12, without an earlier win.
  const result=play(3,4,[0,0,1,0,1,1,2,3,2,2,3,3]);
  assert.equal(result.status,'won');assert.equal(result.winner,2);assert.equal(result.moves.length,12);
  assert.deepEqual(referenceWinner(result),[2]);
});

test('horizontal detection never wraps across a board edge', () => {
  const g=play(6,7,[4,0,5,1,6,2,0]);
  assert.equal(g.status,'playing');assert.deepEqual(referenceWinner(g),[]);
});

test('small boards with no possible four fill to a draw and can be undone', () => {
  for (const [r,c] of [[1,1],[1,3],[3,1],[3,3]]) {
    const g=new Game(r,c);
    while(g.status==='playing')g.drop(g.legalColumns()[0]);
    assert.equal(g.status,'draw');assert.equal(g.winner,null);assert.equal(g.moves.length,r*c);
    assert.ok(g.undo());assert.equal(g.status,'playing');
    while(g.undo());assert.equal(g.moves.length,0);assert.equal(g.turn,1);
  }
});

test('records replay their moves rather than trusting claimed board or winner fields', () => {
  const g=play(6,7,[0,1,0,1,0]);
  assert.deepEqual(Game.fromRecord(g.toRecord()).board,g.board);
  assert.notEqual(g.clone().board,g.board);
  for(const record of [null,{}, {...g.toRecord(),rows:0}, {...g.toRecord(),columns:21},
    {...g.toRecord(),moves:[0]}, {...g.toRecord(),moves:[1.5]},
    {format:'gravity-connect-four',version:1,rows:1,columns:1,moves:[1,1]},
    {format:'gravity-connect-four',version:1,rows:6,columns:7,moves:[1,1,2,2,3,3,4,5]}])
    assert.throws(()=>Game.fromRecord(record));
  const extra={...g.toRecord(),winner:2,board:[[2,2,2,2]]};
  assert.equal(Game.fromRecord(extra).winner,null);
});

test('all 400 dimension pairs: legal random play agrees with an independent whole-board detector', () => {
  let seed=431791;
  const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296};
  for(let rows=1;rows<=20;rows++)for(let columns=1;columns<=20;columns++) {
    const g=new Game(rows,columns);
    while(g.status==='playing') {
      const legal=g.legalColumns();g.drop(legal[Math.floor(random()*legal.length)]);
      const wins=referenceWinner(g);
      assert.deepEqual(wins,g.status==='won'?[g.winner]:[],`${rows}x${columns}`);
      assert.equal(g.board.reduce((n,col)=>n+col.length,0),g.moves.length);
      assert.ok(g.board.every(col=>col.length<=rows));
    }
    assert.ok(g.moves.length<=rows*columns);
  }
});

test('computer takes wins, blocks single immediate threats, returns legal moves and never mutates its input', () => {
  const win=play(6,7,[0,1,0,1,0,2]);assert.equal(chooseComputerMove(win),0);
  const block=play(6,7,[1,0,2,0,5,0]);assert.equal(chooseComputerMove(block),0);
  for(const [r,c] of [[1,1],[2,4],[6,7],[20,20]]) {
    const g=new Game(r,c);
    for(let n=0;n<Math.min(80,r*c)&&g.status==='playing';n++) {
      const before=JSON.stringify(g);
      const col=chooseComputerMove(g);
      assert.equal(JSON.stringify(g),before);assert.ok(g.legalColumns().includes(col));g.drop(col);
    }
    if(g.status!=='playing')assert.equal(chooseComputerMove(g),null);
  }
});

test('dimensions reject zero, oversized, nonintegers and implicit coercion', () => {
  for(const size of [0,21,-1,2.5,'6',null,NaN,Infinity])assert.throws(()=>new Game(size,7));
});
