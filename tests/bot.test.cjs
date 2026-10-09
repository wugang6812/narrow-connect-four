'use strict';
const test=require('node:test');
const assert=require('node:assert/strict');
const fs=require('node:fs');
const zlib=require('node:zlib');
const vm=require('node:vm');
const crypto=require('node:crypto');
const {Game}=require('../game/engine.js');
let bot,policySize=0;
test.before(async()=>{
  const bytes=fs.readFileSync(require.resolve('../game/bot.wasm'));
  const module=await WebAssembly.compile(bytes);
  assert.deepEqual(WebAssembly.Module.imports(module).map(x=>x.module+'.'+x.name),['env.now']);
  bot=(await WebAssembly.instantiate(module,{env:{now:()=>performance.now()}})).exports;
  const sandbox={window:{}};
  vm.runInNewContext(fs.readFileSync(require.resolve('../game/standard-policy.js'),'utf8'),sandbox);
  const data=sandbox.window.CONNECT4_POLICY;
  const raw=zlib.gunzipSync(Buffer.from(data.gzipBase64,'base64'));
  assert.equal(raw.length,data.bytes);
  assert.equal(crypto.createHash('sha256').update(raw).digest('hex'),data.sha256);
  new Uint8Array(bot.memory.buffer).set(raw,bot.bot_policy_pointer());policySize=raw.length;
});
function choose(game,level=1,size=policySize){
  new Uint8Array(bot.memory.buffer).set(game.moves.map(m=>m.column),bot.bot_history_pointer());
  return bot.bot_choose(game.rows,game.columns,level,game.moves.length,size);
}
function replay(r,c,moves){const g=new Game(r,c);for(const m of moves)assert.ok(g.drop(m).ok);return g;}

test('all levels take immediate wins; Normal and Super hard block single immediate threats',()=>{
  for(const level of [1,2,3]){
    assert.equal(choose(replay(6,7,[0,1,0,1,0,2]),level),0);
    if(level>1)assert.equal(choose(replay(6,7,[1,0,2,0,5,0]),level),0);
    const diagonal=replay(6,7,[0,1,1,2,3,2,2,3,4,3]);
    assert.equal(choose(diagonal,level),3);
  }
});

test('C accepts all 400 allowed board sizes and returns a legal move',()=>{
  for(let r=1;r<=20;r++)for(let c=1;c<=20;c++){
    const g=new Game(r,c);const selected=choose(g,1);
    assert.ok(g.legalColumns().includes(selected),`${r}x${c}: ${selected}`);
  }
});

test('C rejects bad dimensions, bad histories and terminal games',()=>{
  assert.equal(bot.bot_choose(0,7,1,0,0),-1);
  assert.equal(bot.bot_choose(6,21,1,0,0),-1);
  assert.equal(bot.bot_choose(6,7,4,0,0),-1);
  new Uint8Array(bot.memory.buffer).set([0,0],bot.bot_history_pointer());
  assert.equal(bot.bot_choose(1,1,1,2,0),-1);
  assert.equal(choose(replay(1,1,[0]),1),-2);
  assert.equal(choose(replay(6,7,[0,0,1,1,2,2,3]),1),-2);
});

test('super hard follows every standard-board root and wins sampled complete games, including mirrored continuations',()=>{
  let seed=928481,positions=0;
  const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296};
  for(let firstWhite=0;firstWhite<7;firstWhite++)for(let trial=0;trial<40;trial++){
    const g=new Game(6,7);
    assert.equal(choose(g,3),3);assert.equal(bot.bot_source(),2);g.drop(3);g.drop(firstWhite);
    while(g.status==='playing'){
      const c=choose(g,3);positions++;
      assert.equal(bot.bot_source(),2,`policy escaped: ${g.toRecord().moves}`);
      assert.ok(g.legalColumns().includes(c));g.drop(c);
      if(g.status!=='playing')break;
      const choices=g.legalColumns();g.drop(choices[Math.floor(random()*choices.length)]);
    }
    assert.equal(g.status,'won');assert.equal(g.winner,1);
  }
  assert.ok(positions>1000);
});

test('off-policy standard positions still get a searched legal move',()=>{
  const g=replay(6,7,[0,3]);
  assert.ok(g.legalColumns().includes(choose(g,2)));
  assert.notEqual(bot.bot_source(),2);
});

test('a completed small-board search agrees with an independent exact minimax',()=>{
  function exact(g){
    if(g.status==='won')return -1;if(g.status==='draw')return 0;
    let best=-1;
    for(const c of g.legalColumns()){g.drop(c);const value=g.status==='won'?1:g.status==='draw'?0:-exact(g);g.undo();best=Math.max(best,value);if(best===1)break;}
    return best;
  }
  for(const moves of [[],[0,0],[0,1,1],[0,0,1,2]]){
    const g=replay(2,4,moves),value=exact(g),move=choose(g,3);
    g.drop(move);const chosen=g.status==='won'?1:g.status==='draw'?0:-exact(g);
    assert.equal(chosen,value);
  }
});
