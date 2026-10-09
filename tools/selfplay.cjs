/* MIT licensed. A paired, empty-board tournament using the actual C difficulty budgets. */
'use strict';
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),zlib=require('node:zlib'),crypto=require('node:crypto');
const {Game}=require('../game/engine.js');
const root=path.resolve(__dirname,'..');
const boards=[[3,3],[4,4],[6,4],[7,4],[6,7],[8,5],[10,10],[20,20]];
const names={1:'Easy',2:'Normal',3:'Super hard'};
const report={status:'running',started_at:new Date().toISOString(),
  design:'Each difficulty pair plays twice from the empty board, exchanging Black and White. No repeated identical trials or randomized openings.',
  budgets_ms:{1:'one-ply heuristic',2:150,3:1800},
  bot_source_sha256:crypto.createHash('sha256').update(fs.readFileSync(path.join(root,'game/bot.c'))).digest('hex'),
  bot_wasm_sha256:crypto.createHash('sha256').update(fs.readFileSync(path.join(root,'game/bot.wasm'))).digest('hex'),
  boards:boards.map(([rows,columns])=>({rows,columns})),games:[]};
const file=path.join(root,'audit/selfplay.json');
function save(){fs.writeFileSync(file+'.tmp',JSON.stringify(report,null,2)+'\n');fs.renameSync(file+'.tmp',file);}
async function main(){
  const instance=await WebAssembly.instantiate(fs.readFileSync(path.join(root,'game/bot.wasm')),{env:{now:()=>performance.now()}});
  const bot=instance.instance.exports;
  const context={window:{}};vm.runInNewContext(fs.readFileSync(path.join(root,'game/standard-policy.js'),'utf8'),context);
  const source=context.window.CONNECT4_POLICY;
  const policy=zlib.gunzipSync(Buffer.from(source.gzipBase64,'base64'));
  if(crypto.createHash('sha256').update(policy).digest('hex')!==source.sha256)throw Error('Policy hash mismatch');
  new Uint8Array(bot.memory.buffer).set(policy,bot.bot_policy_pointer());save();
  let completed=0;
  for(const [rows,columns] of boards)for(const [a,b] of [[1,2],[1,3],[2,3]])for(const [black,white] of [[a,b],[b,a]]){
    const game=new Game(rows,columns),begin=performance.now(),trace=[];
    while(game.status==='playing'){
      const difficulty=game.turn===1?black:white;
      new Uint8Array(bot.memory.buffer).set(game.moves.map(m=>m.column),bot.bot_history_pointer());
      const started=performance.now();
      const column=bot.bot_choose(rows,columns,difficulty,game.moves.length,policy.length);
      if(!game.legalColumns().includes(column))throw Error('Illegal C move in self-play');
      trace.push({player:game.turn,level:difficulty,column:column+1,depth:bot.bot_depth(),nodes:bot.bot_nodes(),source:bot.bot_source(),milliseconds:Math.round(performance.now()-started)});
      game.drop(column);
      // Persist progress at move boundaries, without truncating games for a time limit.
      report.current_game={rows,columns,black,white,moves:game.moves.length};
      if(game.moves.length%10===0)save();
    }
    const item={rows,columns,black,white,status:game.status,winner:game.winner,
      winning_level:game.winner===1?black:game.winner===2?white:null,
      moves:game.moves.length,milliseconds:Math.round(performance.now()-begin),record:game.toRecord(),trace};
    report.games.push(item);completed++;save();
    console.log(JSON.stringify({game:completed,total:48,board:`${rows}x${columns}`,black:names[black],white:names[white],winner:item.winning_level?names[item.winning_level]:'draw',moves:item.moves,seconds:Math.round(item.milliseconds/1000)}));
  }
  const summaries=[];
  for(const [rows,columns] of boards){
    const row={rows,columns,levels:{}};
    for(const level of [1,2,3]){
      const games=report.games.filter(g=>g.rows===rows&&g.columns===columns&&(g.black===level||g.white===level));
      const wins=games.filter(g=>g.winning_level===level).length,draws=games.filter(g=>g.winning_level===null).length;
      row.levels[level]={games:games.length,wins,draws,losses:games.length-wins-draws,win_percent:100*wins/games.length};
    }summaries.push(row);
  }
  report.summary=summaries;report.status='complete';report.completed_at=new Date().toISOString();delete report.current_game;save();
  console.log('COMPLETE',JSON.stringify(summaries));
}
main().catch(error=>{report.status='failed';report.error=String(error.stack||error);save();console.error(error);process.exitCode=1;});
