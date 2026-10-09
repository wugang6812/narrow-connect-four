/* MIT licensed. Runs the C/WebAssembly bot off the UI thread. */
(function () {
  'use strict';
  let worker = null, pending = null, serial = 0, policySent = false;
  let policyBuffer = null, policyPromise = null;
  const source = `
    let engine, policySize=0;
    const ready=WebAssembly.instantiate(Uint8Array.from(atob("${window.CONNECT4_BOT_WASM}"),c=>c.charCodeAt(0)),{env:{now:()=>performance.now()}}).then(r=>engine=r.instance.exports);
    self.onmessage=async event=>{
      const m=event.data;
      try {
        await ready;
        const memory=new Uint8Array(engine.memory.buffer);
        if(m.policy) { policySize=m.policy.byteLength;memory.set(new Uint8Array(m.policy),engine.bot_policy_pointer()); }
        memory.set(m.moves,engine.bot_history_pointer());
        const column=engine.bot_choose(m.rows,m.columns,m.level,m.moves.length,policySize);
        if(column<0)throw new Error('The bot rejected the position.');
        self.postMessage({id:m.id,column,depth:engine.bot_depth(),nodes:engine.bot_nodes(),source:engine.bot_source(),score:engine.bot_score()});
      } catch(error) {self.postMessage({id:m.id,error:String(error.message||error)});}
    };`;

  function getWorker() {
    if (worker) return worker;
    const url = URL.createObjectURL(new Blob([source], { type: 'application/javascript' }));
    worker = new Worker(url); URL.revokeObjectURL(url); policySent = false;
    worker.onmessage = event => {
      if (!pending || event.data.id !== pending.id) return;
      const p = pending; pending = null;
      if (event.data.error) p.reject(new Error(event.data.error)); else p.resolve(event.data);
    };
    worker.onerror = event => {
      if (pending) { const p = pending; pending = null; p.reject(new Error(event.message || 'Bot worker failed.')); }
      worker.terminate(); worker = null; policySent = false;
    };
    return worker;
  }
  async function loadPolicy() {
    if (policyBuffer) return policyBuffer;
    if (policyPromise) return policyPromise;
    policyPromise = (async () => {
      if (!window.CONNECT4_POLICY) await new Promise((resolve, reject) => {
        const script = document.createElement('script');script.src = 'standard-policy.js';
        script.onload = resolve;script.onerror = () => reject(new Error('Policy file unavailable.'));
        document.head.append(script);
      });
      const data = window.CONNECT4_POLICY;
      const compressed = Uint8Array.from(atob(data.gzipBase64), c => c.charCodeAt(0));
      const stream = new Blob([compressed]).stream().pipeThrough(new DecompressionStream('gzip'));
      const buffer = await new Response(stream).arrayBuffer();
      if (buffer.byteLength !== data.bytes) throw new Error('Policy size mismatch.');
      const digest = await crypto.subtle.digest('SHA-256', buffer);
      const hash = Array.from(new Uint8Array(digest), b => b.toString(16).padStart(2,'0')).join('');
      if (hash !== data.sha256) throw new Error('Policy hash mismatch.');
      policyBuffer = buffer;
      // Retain the decoded policy, not its large base64 literal.
      delete data.gzipBase64;
      return buffer;
    })();
    try { return await policyPromise; }
    catch (e) { policyPromise = null; throw e; }
  }
  function cancel() {
    serial++;
    if (pending) { pending.reject(new DOMException('Cancelled','AbortError'));pending=null; }
    if (worker) { worker.terminate();worker=null;policySent=false; }
  }
  async function think(game, level, progress) {
    const id = ++serial, record = game.toRecord();let policy = null, unavailable = false;
    if (level === 3 && record.rows === 6 && record.columns === 7 && game.turn === 1 && record.moves.length >= 2 && record.moves[0] === 4) {
      if (progress) progress('policyLoading');
      try { policy = await loadPolicy(); } catch (_) { unavailable = true; }
    }
    if (id !== serial) throw new DOMException('Cancelled','AbortError');
    const bot = getWorker();
    return new Promise((resolve,reject) => {
      pending = { id, resolve: result => { result.policyUnavailable=unavailable;resolve(result); }, reject };
      bot.postMessage({id,rows:record.rows,columns:record.columns,level,
        moves:Uint8Array.from(record.moves,c=>c-1),policy:policy&&!policySent?policy:null});
      if (policy) policySent=true;
    });
  }
  window.ConnectBot = { think, cancel };
})();
