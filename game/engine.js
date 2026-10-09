/* Original browser game code, MIT licensed. No verified optimal strategy is implemented. */
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.ConnectFour = factory();
})(typeof globalThis !== 'undefined' ? globalThis : this, function () {
  'use strict';
  const MAX_SIZE = 20;
  const directions = [[1, 0], [0, 1], [1, 1], [1, -1]];

  function dimension(value) {
    if (!Number.isInteger(value) || value < 1 || value > MAX_SIZE)
      throw new RangeError('Rows and columns must be integers from 1 to 20.');
    return value;
  }

  class Game {
    constructor(rows = 6, columns = 7) {
      this.rows = dimension(rows);
      this.columns = dimension(columns);
      this.board = Array.from({ length: columns }, () => []);
      this.moves = [];
      this.turn = 1;
      this.status = 'playing';
      this.winner = null;
      this.winningCells = [];
    }

    cell(column, row) {
      if (column < 0 || column >= this.columns || row < 0 || row >= this.rows) return 0;
      return this.board[column][row] || 0;
    }

    legalColumns() {
      if (this.status !== 'playing') return [];
      return this.board.flatMap((column, index) => column.length < this.rows ? [index] : []);
    }

    linesThrough(column, row, player) {
      const cells = new Map();
      for (const [dx, dy] of directions) {
        const line = [[column, row]];
        for (const sign of [-1, 1]) {
          let x = column + sign * dx, y = row + sign * dy;
          while (this.cell(x, y) === player) {
            line.push([x, y]); x += sign * dx; y += sign * dy;
          }
        }
        if (line.length >= 4) for (const point of line) cells.set(point.join(','), point);
      }
      return [...cells.values()];
    }

    drop(column) {
      if (!Number.isInteger(column) || column < 0 || column >= this.columns)
        return { ok: false, reason: 'invalid-column' };
      if (this.status !== 'playing') return { ok: false, reason: 'game-over' };
      if (this.board[column].length >= this.rows) return { ok: false, reason: 'full-column' };
      const player = this.turn, row = this.board[column].length;
      this.board[column].push(player);
      const move = { column, row, player };
      this.moves.push(move);
      this.winningCells = this.linesThrough(column, row, player);
      // First four wins, including on the last empty square.
      if (this.winningCells.length) { this.status = 'won'; this.winner = player; }
      else if (this.moves.length === this.rows * this.columns) this.status = 'draw';
      else this.turn = 3 - player;
      return { ok: true, move: { ...move }, status: this.status, winner: this.winner };
    }

    undo() {
      const move = this.moves.pop();
      if (!move) return false;
      this.board[move.column].pop();
      this.turn = move.player;
      this.status = 'playing'; this.winner = null; this.winningCells = [];
      return true;
    }

    toRecord() {
      return { format: 'gravity-connect-four', version: 1, rows: this.rows,
        columns: this.columns, moves: this.moves.map(move => move.column + 1) };
    }

    clone() { return Game.fromRecord(this.toRecord()); }

    static fromRecord(record) {
      if (!record || record.format !== 'gravity-connect-four' || record.version !== 1 || !Array.isArray(record.moves))
        throw new Error('Unsupported game record.');
      const game = new Game(record.rows, record.columns);
      if (record.moves.length > record.rows * record.columns) throw new Error('Too many moves.');
      for (const column of record.moves) {
        if (!Number.isInteger(column) || !game.drop(column - 1).ok)
          throw new Error('The record contains an illegal move or continues after the game ended.');
      }
      return game;
    }
  }

  function immediateWins(game, player) {
    const wins = [];
    for (const column of game.legalColumns()) {
      const row = game.board[column].length;
      game.board[column].push(player);
      try { if (game.linesThrough(column, row, player).length) wins.push(column); }
      finally { game.board[column].pop(); }
    }
    return wins;
  }

  // A bounded tactical opponent: win now, block now, and prefer safe threats.
  // This is neither a solver nor the strategy supplied by the Lean proof.
  function chooseComputerMove(game) {
    if (!(game instanceof Game)) throw new TypeError('Expected a game.');
    const legal = game.legalColumns();
    if (!legal.length) return null;
    const player = game.turn, enemy = 3 - player;
    const ownWins = immediateWins(game, player);
    if (ownWins.length) return ownWins[0];
    const enemyWins = immediateWins(game, enemy);
    let best = legal[0], bestScore = -Infinity;
    for (const column of legal) {
      const next = game.clone(); next.drop(column);
      const danger = next.status === 'playing' ? immediateWins(next, enemy).length : 0;
      const threats = next.status === 'playing' ? immediateWins(next, player).length : 0;
      let score = -danger * 10000 + threats * 30 - Math.abs(column - (game.columns - 1) / 2);
      if (enemyWins.includes(column)) score += 100;
      // Local two/three-piece windows, with explicit row/column boundaries.
      const row = next.board[column].length - 1;
      for (const [dx, dy] of directions) for (let offset = -3; offset <= 0; offset++) {
        let own = 0, valid = true;
        for (let step = 0; step < 4; step++) {
          const x = column + (offset + step) * dx, y = row + (offset + step) * dy;
          if (x < 0 || x >= game.columns || y < 0 || y >= game.rows || next.cell(x, y) === enemy) { valid = false; break; }
          if (next.cell(x, y) === player) own++;
        }
        if (valid) score += own * own;
      }
      if (score > bestScore) { bestScore = score; best = column; }
    }
    return best;
  }
  return { Game, MAX_SIZE, chooseComputerMove };
});
