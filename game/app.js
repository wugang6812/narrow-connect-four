/* MIT licensed. Browser UI and C-worker integration; original proof sources are preserved separately. */
(function () {
  'use strict';
  const { Game, chooseComputerMove } = window.ConnectFour;
  const $ = id => document.getElementById(id);
  const key = 'narrow-connect-four:game:v1';
  const labels = {
    zh: {
      offline:'本地运行',eyebrow:'一颗棋子，一列选择。',title:'让四颗棋子连成一线。',
      lead:'棋子落到底部，黑白轮流落子。横、竖或斜向，谁先连成四颗就赢。',
      scrollHint:'大棋盘可以左右滑动；点击列号或格子落子。',undo:'↶ 悔棋',restart:'重新开始',
      keyboard:'← → 选列 · 空格落子',setup:'设置一局',rows:'行数 / 高度 M',columns:'列数 / 宽度 N',
      mode:'对局模式',twoPlayers:'双人轮流',computer:'与电脑对弈',yourSide:'你执哪一方',
      difficulty:'电脑难度',easy:'简单',normal:'普通',super:'超级难',
      blackFirst:'黑方，先手',whiteSecond:'白方，后手',newGame:'开始新对局 →',
      settingsHelp:'每边 1～20 格。棋盘尺寸需开始新对局；模式和难度立即生效。',researchLabel:'从游戏到证明',
      paperZh:'中文论文 ↗',paperEn:'English paper ↗',leanProof:'Lean 定理 ↗',records:'棋谱',
      export:'导出 JSON',import:'导入棋谱',footer:'C 语言电脑支持三档难度，超级难会优先采用已有的标准棋盘先手策略。',
      policyLoading:'正在加载已有的先手策略…',certified:'本手采用已验收的先手策略。',
      policyFallback:'策略文件暂未加载成功，本手采用搜索。',botFallback:'电脑模块暂不可用，本手采用备用走法。',
      black:'黑方',white:'白方',turn:p=>`轮到${p}落子`,thinking:'电脑正在选择一列…',
      win:p=>`${p}连成四颗，获胜！`,draw:'棋盘已满，本局和棋。',
      size:(r,c)=>`${r} 行 × ${c} 列 · 黑方先手`,count:(n,total)=>`${n} / ${total} 手`,
      column:n=>`第 ${n} 列`,cell:(c,r,p)=>`第${c}列，自底第${r}排，${p || '空格'}`,
      emptyHistory:'棋谱会在落子后显示。',move:(p,c)=>`${p === 1 ? '黑' : '白'}${c}`,
      full:'这一列已满，请选择其他列。',ended:'本局已经结束，可以悔棋或开始新对局。',
      waiting:'现在轮到电脑，请稍等。',invalidSize:'行数和列数都须为 1～20 的整数。',
      imported:'棋谱已导入，所有落子已按规则重新检查。',badRecord:'棋谱无效：格式、尺寸或落子顺序不符合规则。',
      tooLarge:'棋谱文件过大，请使用本游戏导出的 JSON。',undoNotice:'已撤回上一轮落子。',
      resumed:'已恢复上次在此浏览器中的对局。',savedBad:'上次保存的对局无效，已开始新对局。',
      newNotice:'新对局已开始。',standardTitle:'试试不同宽度',
      narrowTitle:'这类空盘，最优策略下是和棋。',
      narrowText:'本仓库证明了宽度 1～4、任意有限高度的空盘双方均有不败策略。实际对局仍可能因走法失误分出胜负。',
      otherText:'当前棋盘宽度大于 4，不属于本仓库窄棋盘和棋定理的范围。小游戏演示的是重力与先四连获胜的规则。',
      restoreAi:'导入棋谱后使用双人模式，可继续探索双方走法。'
    },
    en: {
      offline:'Runs locally',eyebrow:'ONE PIECE. ONE COLUMN.',title:'Four in a row. Gravity does the rest.',
      lead:'Black and White take turns. Pieces fall to the bottom. The first horizontal, vertical or diagonal four wins.',
      scrollHint:'Swipe sideways on large boards. Click a column number or a cell to drop a piece.',undo:'↶ Undo',restart:'Restart',
      keyboard:'← → select · Space to drop',setup:'Set up a game',rows:'Rows / height M',columns:'Columns / width N',
      mode:'Players',twoPlayers:'Two players',computer:'Play the computer',yourSide:'Your side',
      difficulty:'Difficulty',easy:'Easy',normal:'Normal',super:'Super hard',
      blackFirst:'Black, moves first',whiteSecond:'White, moves second',newGame:'Start a new game →',
      settingsHelp:'Each dimension: 1–20. Start a new game to resize. Mode and difficulty apply immediately.',researchLabel:'FROM PLAY TO PROOF',
      paperZh:'Chinese paper ↗',paperEn:'English paper ↗',leanProof:'Lean theorem ↗',records:'Game record',
      export:'Export JSON',import:'Import record',footer:'Three C-powered difficulty levels. Super hard prefers the existing standard-board first-player policy.',
      policyLoading:'Loading the existing first-player policy…',certified:'This move follows the accepted first-player policy.',
      policyFallback:'Policy data unavailable; using search for this move.',botFallback:'Computer module unavailable; using a backup move.',
      black:'Black',white:'White',turn:p=>`${p} to move`,thinking:'The computer is choosing a column…',
      win:p=>`${p} connects four and wins!`,draw:'Full board. This game is a draw.',
      size:(r,c)=>`${r} rows × ${c} columns · Black starts`,count:(n,total)=>`${n} / ${total} moves`,
      column:n=>`Column ${n}`,cell:(c,r,p)=>`Column ${c}, row ${r} from bottom: ${p || 'empty'}`,
      emptyHistory:'Moves will appear here.',move:(p,c)=>`${p === 1 ? 'B' : 'W'}${c}`,
      full:'That column is full. Choose another column.',ended:'This game has ended. Undo or start a new game.',
      waiting:'It is the computer’s turn. Please wait.',invalidSize:'Rows and columns must both be integers from 1 to 20.',
      imported:'Record imported. Every move was checked against the rules.',badRecord:'Invalid record: check its format, dimensions and moves.',
      tooLarge:'The record is too large. Use JSON exported by this game.',undoNotice:'The previous round has been undone.',
      resumed:'Your previous game in this browser has been restored.',savedBad:'The saved record was invalid. A new game has started.',
      newNotice:'A new game has started.',standardTitle:'Explore different widths',
      narrowTitle:'These empty boards are draws under optimal play.',
      narrowText:'This project proves non-losing strategies for both players at widths 1–4 and every finite height. Actual play can still end in a win after a mistake.',
      otherText:'This board is wider than four columns and falls outside this project’s narrow-board draw theorem. The game illustrates gravity and the first-four-wins rules.',
      restoreAi:'Imported records use two-player mode so you can explore either side.'
    }
  };
  let game = new Game(), lang = 'zh', mode = 'two', human = 1, level = 1;
  let timer = null, busy = false, selected = 0, lastAnimation = -1, generation = 0;
  let initialNotice = null;
  const t = (name, ...args) => typeof labels[lang][name] === 'function' ? labels[lang][name](...args) : labels[lang][name];
  const playerName = p => t(p === 1 ? 'black' : 'white');

  try {
    const saved = localStorage.getItem(key);
    if (saved) {
      const data = JSON.parse(saved);
      game = Game.fromRecord(data.game);
      lang = data.lang === 'en' ? 'en' : 'zh';
      mode = data.mode === 'computer' ? 'computer' : 'two';
      human = data.human === 2 ? 2 : 1;
      level = [1,2,3].includes(data.level) ? data.level : 1;
      initialNotice = 'resumed';
    }
  } catch (_) { initialNotice = 'savedBad'; }

  function save() {
    try { localStorage.setItem(key, JSON.stringify({ game: game.toRecord(), lang, mode, human, level })); }
    catch (_) { /* Game remains playable when browser storage is unavailable. */ }
  }
  function notice(name) { $('notice').textContent = name ? t(name) : ''; }
  function cancelComputer() { generation++; if (timer !== null) clearTimeout(timer); timer = null; busy = false; if(window.ConnectBot)window.ConnectBot.cancel(); }
  function syncSettings() {
    $('rows').value = game.rows; $('columns').value = game.columns;
    $('mode').value = mode; $('human').value = human;
    $('side-label').hidden = mode !== 'computer';
    $('difficulty-label').hidden = mode !== 'computer';$('difficulty').value = level;
  }
  function translate() {
    document.documentElement.lang = lang === 'zh' ? 'zh-CN' : 'en';
    document.body.classList.toggle('en', lang === 'en');
    document.querySelectorAll('[data-i18n]').forEach(el => { el.textContent = t(el.dataset.i18n); });
    $('language').textContent = lang === 'zh' ? 'English' : '中文';
    $('board').setAttribute('aria-label', lang === 'zh' ? '重力四子棋棋盘' : 'Gravity Connect Four board');
    $('column-buttons').setAttribute('aria-label', lang === 'zh' ? '选择落子列' : 'Choose a column');
  }

  function render() {
    const canMove = game.status === 'playing' && !busy && (mode === 'two' || game.turn === human);
    $('board-shell').style.setProperty('--columns', game.columns);
    const buttons = document.createDocumentFragment();
    for (let c = 0; c < game.columns; c++) {
      const button = document.createElement('button');
      button.type = 'button'; button.dataset.column = c;
      button.textContent = c + 1; button.title = t('column', c + 1);
      button.setAttribute('aria-label', t('column', c + 1));
      button.disabled = !canMove || game.board[c].length >= game.rows;
      button.classList.toggle('selected', c === selected);
      buttons.append(button);
    }
    $('column-buttons').replaceChildren(buttons);
    const cells = document.createDocumentFragment();
    const winning = new Set(game.winningCells.map(p => p.join(',')));
    const last = game.moves[game.moves.length - 1];
    for (let row = game.rows - 1; row >= 0; row--) {
      const rowElement = document.createElement('div'); rowElement.className = 'board-row';
      rowElement.setAttribute('role','row'); rowElement.setAttribute('aria-rowindex',game.rows-row);
      for (let column = 0; column < game.columns; column++) {
      const value = game.cell(column, row), cell = document.createElement('div');
      cell.className = 'cell'; cell.dataset.column = column; cell.dataset.row = row;
      cell.setAttribute('role', 'gridcell');
      cell.setAttribute('aria-rowindex', game.rows - row);
      cell.setAttribute('aria-colindex', column + 1);
      cell.setAttribute('aria-label', t('cell', column + 1, row + 1, value ? playerName(value) : ''));
      if (winning.has(`${column},${row}`)) cell.classList.add('win');
      if (value) {
        const disc = document.createElement('span'); disc.className = 'disc ' + (value === 1 ? 'black' : 'white');
        if (last && last.column === column && last.row === row) {
          disc.classList.add('last');
          if (lastAnimation === game.moves.length) disc.classList.add('falling');
        }
        cell.append(disc);
      }
      rowElement.append(cell);
      }
      cells.append(rowElement);
    }
    $('board').replaceChildren(cells);
    $('board').setAttribute('aria-rowcount', game.rows);
    $('board').setAttribute('aria-colcount', game.columns);
    const falling = $('board').querySelector('.falling');
    if (falling) {
      const topRow = game.rows - 1 - last.row;
      const step = falling.parentElement.getBoundingClientRect().height + 5;
      falling.style.setProperty('--drop', `${-(topRow + 1) * step}px`);
    }
    lastAnimation = -1;
    const status = game.status === 'won' ? t('win', playerName(game.winner)) : game.status === 'draw' ? t('draw') : busy ? t('thinking') : t('turn', playerName(game.turn));
    $('status').textContent = status;
    $('turn-token').className = 'turn-token ' + (game.status === 'draw' ? 'draw' : (game.winner || game.turn) === 1 ? 'black' : 'white');
    $('board-description').textContent = t('size', game.rows, game.columns);
    $('move-count').textContent = t('count', game.moves.length, game.rows * game.columns);
    $('undo').disabled = game.moves.length === 0 || (mode === 'computer' && human === 2 && game.moves.length === 1 && !busy);
    $('scroll-hint').hidden = game.columns < 12;
    $('research-title').textContent = t(game.columns <= 4 ? 'narrowTitle' : 'standardTitle');
    $('research-description').textContent = t(game.columns <= 4 ? 'narrowText' : 'otherText');
    $('history').textContent = game.moves.length ? game.moves.map(m => t('move', m.player, m.column + 1)).join(' · ') : t('emptyHistory');
    preview(selected);
  }

  function preview(column) {
    $('board').querySelectorAll('.preview').forEach(c => c.classList.remove('preview'));
    if (game.status !== 'playing' || busy || (mode === 'computer' && game.turn !== human)) return;
    const row = game.board[column] ? game.board[column].length : game.rows;
    const cell = $('board').querySelector(`[data-column="${column}"][data-row="${row}"]`);
    if (cell) cell.classList.add('preview');
  }
  function maybeComputer() {
    if (timer !== null || mode !== 'computer' || game.status !== 'playing' || game.turn === human) return;
    busy = true; render();
    const epoch = generation;
    timer = setTimeout(async () => {
      timer = null;let answer=null;
      try {
        answer=await window.ConnectBot.think(game,level,name=>{if(epoch===generation)notice(name)});
      } catch(error) {
        if(error.name==='AbortError'||epoch!==generation)return;
        answer={column:chooseComputerMove(game),fallback:true};
      }
      if(epoch!==generation)return;
      busy=false;
      if(answer.column!==null) { game.drop(answer.column);lastAnimation=game.moves.length; }
      save();render();
      notice(answer.fallback?'botFallback':answer.policyUnavailable?'policyFallback':answer.source===2?'certified':null);
    }, 180);
  }
  function play(column) {
    if (busy || (mode === 'computer' && game.turn !== human && game.status === 'playing')) { notice('waiting'); return; }
    const result = game.drop(column);
    if (!result.ok) { notice(result.reason === 'full-column' ? 'full' : 'ended'); return; }
    selected = column; lastAnimation = game.moves.length; notice(null); save(); render(); maybeComputer();
  }
  function begin(rows, columns, newMode, newHuman) {
    cancelComputer(); game = new Game(rows, columns); mode = newMode; human = newHuman;
    selected = Math.min(selected, columns - 1); syncSettings(); save(); render(); notice('newNotice'); maybeComputer();
  }
  $('column-buttons').addEventListener('click', event => {
    const button = event.target.closest('[data-column]'); if (button) play(Number(button.dataset.column));
  });
  $('board').addEventListener('click', event => {
    const cell = event.target.closest('[data-column]'); if (cell) play(Number(cell.dataset.column));
  });
  for (const id of ['board','column-buttons']) {
    $(id).addEventListener('pointerover', event => {
      const cell = event.target.closest('[data-column]'); if (cell) preview(Number(cell.dataset.column));
    });
    $(id).addEventListener('pointerleave', () => preview(selected));
  }
  document.addEventListener('keydown', event => {
    if (event.ctrlKey || event.metaKey || event.altKey || ['INPUT','SELECT','TEXTAREA','A'].includes(event.target.tagName)) return;
    if (event.key === 'ArrowLeft' || event.key === 'ArrowRight') {
      event.preventDefault(); selected = (selected + (event.key === 'ArrowLeft' ? -1 : 1) + game.columns) % game.columns;
      $('column-buttons').querySelectorAll('button').forEach(b => b.classList.toggle('selected', Number(b.dataset.column) === selected));
      preview(selected);
    } else if ((event.code === 'Space' || event.key === 'Enter') && event.target.tagName !== 'BUTTON' && !event.repeat) {
      event.preventDefault(); play(selected);
    }
  });
  $('new-game').addEventListener('click', () => {
    const r = $('rows').value.trim(), c = $('columns').value.trim();
    if (!/^\d+$/.test(r) || !/^\d+$/.test(c) || Number(r) < 1 || Number(r) > 20 || Number(c) < 1 || Number(c) > 20) { notice('invalidSize'); return; }
    begin(Number(r), Number(c), $('mode').value === 'computer' ? 'computer' : 'two', Number($('human').value) === 2 ? 2 : 1);
  });
  document.querySelectorAll('[data-preset]').forEach(button => button.addEventListener('click', () => {
    const [rows, columns] = button.dataset.preset.split(','); $('rows').value = rows; $('columns').value = columns;
  }));
  $('mode').addEventListener('change', () => {
    cancelComputer();mode=$('mode').value==='computer'?'computer':'two';
    human=Number($('human').value)===2?2:1;
    $('side-label').hidden=mode!=='computer';$('difficulty-label').hidden=mode!=='computer';
    save();render();notice(null);maybeComputer();
  });
  $('human').addEventListener('change', () => {cancelComputer();human=Number($('human').value)===2?2:1;save();render();notice(null);maybeComputer();});
  $('difficulty').addEventListener('change', () => {cancelComputer();level=Number($('difficulty').value);save();render();notice(null);maybeComputer();});
  $('restart').addEventListener('click', () => begin(game.rows, game.columns, mode, human));
  $('undo').addEventListener('click', () => {
    if ($('undo').disabled) return;
    cancelComputer(); game.undo();
    if (mode === 'computer' && game.turn !== human && game.moves.length) game.undo();
    save(); render(); notice('undoNotice'); maybeComputer();
  });
  $('language').addEventListener('click', () => { lang = lang === 'zh' ? 'en' : 'zh'; translate(); render(); notice(null); save(); });
  $('export').addEventListener('click', () => {
    const blob = new Blob([JSON.stringify(game.toRecord(), null, 2) + '\n'], { type:'application/json' });
    const url = URL.createObjectURL(blob), a = document.createElement('a');
    a.href = url; a.download = `connect-four-${game.rows}x${game.columns}.json`; document.body.append(a); a.click(); a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  });
  $('import').addEventListener('click', () => $('record-file').click());
  $('record-file').addEventListener('change', async event => {
    const file = event.target.files[0]; event.target.value = '';
    if (!file) return;
    if (file.size > 65536) { notice('tooLarge'); return; }
    try {
      const loaded = Game.fromRecord(JSON.parse(await file.text()));
      cancelComputer(); game = loaded; mode = 'two'; selected = 0;
      syncSettings(); save(); render(); notice('imported');
    } catch (_) { notice('badRecord'); }
  });
  syncSettings(); translate(); render(); if (initialNotice) notice(initialNotice); maybeComputer();
})();
