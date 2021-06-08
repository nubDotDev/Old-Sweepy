const MAX_CALLS = 100000; // TODO Delete this
const MAX_ITERS = 2 ** 17;
const GUESS_FACTOR = 2 ** 6;

function arrayIncludesTile(arr, tile) {
  return arr.some(i => i[0] === tile[0] && i[1] === tile[1]);
}

// Inspired by https://gist.github.com/axelpale/3118596
function combinations(set, k) {
	if (k > set.length || k <= 0) {
		return [];
	}
	if (k === set.length) {
		return [set];
	}
	let combs = [];
	if (k === 1) {
		for (let i = 0; i < set.length; i++) {
			combs.push([set[i]]);
		}
		return combs;
	}
	for (let i = 0; i <= set.length - k; i++) {
		const head = set.slice(i, i + 1);
		combs.push(...combinations(set.slice(i + 1), k - 1).map(x => head.concat(x)));
	}
	return combs;
}

function stringToTile(str) {
  return str.split(',').map(x => parseInt(x));
}

class Game {
  constructor(width, height, mines, board = [...Array(height)].map(() => Array(width).fill(-2))) {
    this.width = width;
    this.height = height;
    this.mines = mines;
    this.board = board;
    this.updateGroups();
  }

  updateBoard(board) {
    for (let i = 0; i < this.width; i++) {
      for (let j = 0; j < this.height; j++) {
        if (this.board[j][i] !== -1) {
          this.board[j][i] = board[j][i];
        }
      }
    }
  }

  isFresh() {
    for (let i = 0; i < this.width; i++) {
      for (let j = 0; j < this.height; j++) {
        if (this.board[j][i] !== -2) {
          return false;
        }
      }
    }
    return true;
  }

  flag(tile) {
    if (this.getValue(tile) !== -1) {
      const [x, y] = tile;
      this.board[y][x] = -1;
      this.mines--;
    }
  }

  getValue(tile) {
    const [x, y] = tile;
    return this.board[y][x];
  }

  getNeighbors(tile, visited = []) {
    const neighbors = [];
    const [x, y] = tile;
    for (let i = Math.max(x - 1, 0); i <= Math.min(x + 1, this.width - 1); i++) {
      for (let j = Math.max(y - 1, 0); j <= Math.min(y + 1, this.height - 1); j++) {
        const neighbor = [i, j];
        if ((i !== x || j !== y) && !arrayIncludesTile(visited, neighbor)) {
          neighbors.push(neighbor);
        }
      }
    }
    return neighbors;
  }

  isUnsolved(tile) {
    return this.getValue(tile) > 0 && this.getBlankNeighbors(tile).length > 0;
  }

  getBlankNeighbors(tile, visited = []) {
    return this.getNeighbors(tile, visited).filter(i => this.getValue(i) === -2);
  }

  getFlaggedNeighbors(tile, visited = []) {
    return this.getNeighbors(tile, visited).filter(i => this.getValue(i) === -1);
  }

  getUnsolvedNeighbors(tile, visited = []) {
    return this.getNeighbors(tile, visited).filter(i => this.isUnsolved(i));
  }

  getGroup(tile, visited = [], group = []) {
    group.push(tile);
    for (let i of this.getBlankNeighbors(tile, visited)) {
      visited.push(i);
      for (let j of this.getUnsolvedNeighbors(i, visited)) {
        visited.push(j);
        if (!arrayIncludesTile(group, j)) {
          this.getGroup(j, visited, group);
        }
      }
    }
    return group;
  }

  updateGroups() {
    const groups = [];
    const visited = [];
    for (let i = 0; i < this.width; i++) {
      for (let j = 0; j < this.height; j++) {
        const tile = [i, j];
        if (this.isUnsolved(tile) && !arrayIncludesTile(visited, tile)) {
          visited.push(tile);
          groups.push(this.getGroup(tile, visited));
        }
      }
    }
    this.groups = groups;
  }

  makeSimpleMove() {
    if (this.mines === 0) {
      for (let i = 0; i < this.width; i++) {
        for (let j = 0; j < this.height; j++) {
          const tile = [i, j];
          if (this.getValue(tile) === -2) {
            return { uncover: [tile], flag: [] };
          }
        }
      }
    } else if (this.isFresh()) {
      return { uncover: [[Math.floor(this.width / 2), Math.floor(this.height / 2)]], flag: [] };
    } else {
      for (let group of this.groups) {
        for (let tile of group) {
          const val = this.getValue(tile);
          const blankNeighbors = this.getBlankNeighbors(tile);
          const numFlaggedNeighbors = this.getFlaggedNeighbors(tile).length;
          if (blankNeighbors.length === val - numFlaggedNeighbors) {
            for (let neighbor of blankNeighbors) {
              this.flag(neighbor);
              return { uncover: [], flag: [neighbor] };
            }
          } else if (numFlaggedNeighbors === val) {
            for (let neighbor of blankNeighbors) {
              return { uncover: [neighbor], flag: [] };
            }
          }
        }
      }
    }
    return { uncover: [], flag: [] };
  }

  makeSimpleMoves() {
    const moves = { uncover: [], flag: [] };
    if (this.mines === 0) {
      for (let i = 0; i < this.width; i++) {
        for (let j = 0; j < this.height; j++) {
          const tile = [i, j];
          if (this.getValue(tile) === -2) {
            moves.uncover.push(tile);
          }
        }
      }
    } else if (this.isFresh()) {
      moves.uncover.push([Math.floor(this.width / 2), Math.floor(this.height / 2)]);
    } else {
      for (let group of this.groups) {
        for (let tile of group) {
          const val = this.getValue(tile);
          const blankNeighbors = this.getBlankNeighbors(tile);
          const numFlaggedNeighbors = this.getFlaggedNeighbors(tile).length;
          if (blankNeighbors.length === val - numFlaggedNeighbors) {
            for (let neighbor of blankNeighbors) {
              if (!arrayIncludesTile(moves.flag, neighbor)) {
                moves.flag.push(neighbor);
                this.flag(neighbor);
              }
            }
          } else if (numFlaggedNeighbors === val) {
            for (let neighbor of blankNeighbors) {
              if (!arrayIncludesTile(moves.uncover, neighbor)) {
                moves.uncover.push(neighbor);
              }
            }
          }
        }
      }
    }
    return moves;
  }

  getGroupSentences(group) {
    const sentences = [];
    const newSentences = [];
    group.forEach(tile => sentences.push({ tiles: this.getBlankNeighbors(tile), value: this.getValue(tile) - this.getFlaggedNeighbors(tile).length }));
    for (let sentence1 of sentences) {
      for (let sentence2 of sentences) {
        if (sentence1 !== sentence2 && sentence1.tiles.length > sentence2.tiles.length) {
          const difference = sentence1.tiles.filter(tile => !arrayIncludesTile(sentence2.tiles, tile));
          if (difference.length > 0 && difference.length === sentence1.tiles.length - sentence2.tiles.length) {
            newSentences.push({ tiles: difference, value: sentence1.value - sentence2.value });
          }
        }
      }
    }
    sentences.push(...newSentences);
    return sentences;
  }

  makeComplexMove() {
    for (let group of this.groups) {
      for (let sentence of this.getGroupSentences(group)) {
        if (sentence.value === sentence.tiles.length) {
          this.flag(sentence.tiles[0]);
          return { uncover: [], flag: [sentence.tiles[0]] };
        } else if (sentence.value === 0) {
          return { uncover: [sentence.tiles[0]], flag: [] };
        }
      }
    }
    return { uncover: [], flag: [] }
  }

  makeComplexMoves() {
    const moves = { uncover: [], flag: [] };
    for (let group of this.groups) {
      for (let sentence of this.getGroupSentences(group)) {
        if (sentence.value === sentence.tiles.length) {
          sentence.tiles.forEach(tile => this.flag(tile));
          moves.flag.push(...sentence.tiles);
        } else if (sentence.value === 0) {
          moves.uncover.push(...sentence.tiles);
        }
      }
    }
    return moves;
  }

  getProbabilities() {
    const mineProbs = {};
    if (this.groups.length > 0) {
      for (let group of this.groups) {
        const blankNeighbors = {};
        const allBlankNeighbors = [];
        const mineCounts = {};
        for (let tile of group) {
          const neighbors = this.getBlankNeighbors(tile);
          blankNeighbors[tile] = neighbors;
          for (let neighbor of neighbors) {
            if (!arrayIncludesTile(allBlankNeighbors, neighbor)) {
              allBlankNeighbors.push(neighbor);
            }
            mineCounts[neighbor] = 0;
          }
        }
        const mineCombos = group.map(tile =>
            combinations(blankNeighbors[tile], this.getValue(tile) - this.getFlaggedNeighbors(tile).length));
        let calls = 0;
        let count = 0;

        // const checkCombo = (combo = [], i = 0, visited = []) => {
        //   calls++;
        //   if (calls >= MAX_CALLS) {
        //     return;
        //   }
        //   if (i === group.length) {
        //     if (combo.length <= this.mines) {
        //       let valid = true;
        //       for (let tile of group) {
        //         const mines = blankNeighbors[tile].filter(blank => arrayIncludesTile(combo, blank)).length;
        //         if (mines !== this.getValue(tile) - this.getFlaggedNeighbors(tile).length) {
        //           valid = false;
        //         }
        //       }
        //       if (valid) {
        //         combo.forEach(tile => mineCounts[tile]++);
        //         count++;
        //       }
        //     }
        //   } else {
        //     for (let mineCombo of mineCombos[i]) {
        //       let valid = true;
        //       for (let tile of mineCombo) {
        //         if (!arrayIncludesTile(combo, tile)) {
        //           for (let prev of visited) {
        //             if (arrayIncludesTile(blankNeighbors[prev], tile)) {
        //               valid = false;
        //             }
        //           }
        //         }
        //       }
        //       if (valid) {
        //         checkCombo(combo.concat(mineCombo.filter(tile => !arrayIncludesTile(combo, tile))), i + 1, visited.concat([group[i]]));
        //       }
        //     }
        //   }
        // }
        // checkCombo();

        // // Initialize the slots to hold the current iteration value for each depth
        // const slots = Array(group.length).fill(0);
        // let iters = 0;
        // let index = 0;
        // console.log(mineCombos.map(x => x.length).reduce((prod, x) => prod * x));
        // iter: {
        //   while (true) {
        //     let combo = [];
        //     let valid = true;
        //     for (let i = 0; i < slots.length; i++) {
        //       combo.push(...mineCombos[i][slots[i]].filter(tile => !arrayIncludesTile(combo, tile)));
        //       if (combo.length > this.mines) {
        //         valid = false;
        //         break;
        //       }
        //     }
        //     if (valid) {
        //       for (let tile of group) {
        //         const mines = blankNeighbors[tile].filter(blank => arrayIncludesTile(combo, blank)).length;
        //         if (mines !== this.getValue(tile) - this.getFlaggedNeighbors(tile).length) {
        //           valid = false;
        //           break;
        //         }
        //       }
        //       if (valid) {
        //         combo.forEach(tile => mineCounts[tile]++);
        //         count++;
        //       }
        //     }
        //     iters++;
        //     if (iters >= MAX_ITERS) {
        //       break;
        //     }
        //     // Increment
        //     slots[0]++;
        //     // Carry
        //     while (slots[index] === mineCombos[index].length) {
        //       // Overflow, we're done
        //       if (index === slots.length - 1) {
        //           console.log('breaks');
        //           break iter;
        //       }
        //       slots[index++] = 0;
        //       slots[index]++;
        //     }
        //     index = 0;
        //   }
        // }

        // console.log('pow of 2', 2 ** allBlankNeighbors.length);
        // console.log('combos', mineCombos.map(x => x.length).reduce((prod, x) => prod * x));
        // if (2 ** allBlankNeighbors.length < MAX_ITERS)
        // // Initialize the slots to hold the current iteration value for each depth
        // const slots = Array(allBlankNeighbors.length).fill(0);
        // let index = 0;
        // let iters = 0;
        // iter: {
        //   while (true) {
        //     let combo = [];
        //     let valid = true;
        //     for (let i = 0; i < slots.length; i++) {
        //       if (slots[i]) {
        //         combo.push(allBlankNeighbors[i]);
        //         if (combo.length > this.mines) {
        //           valid = false;
        //           break;
        //         }
        //       }
        //     }
        //     if (valid) {
        //       for (let tile of group) {
        //         const mines = blankNeighbors[tile].filter(blank => arrayIncludesTile(combo, blank)).length;
        //         if (mines !== this.getValue(tile) - this.getFlaggedNeighbors(tile).length) {
        //           valid = false;
        //           break;
        //         }
        //       }
        //       if (valid) {
        //         combo.forEach(tile => mineCounts[tile]++);
        //         count++;
        //       }
        //     }
        //     iters++;
        //     if (iters >= 1000000) {
        //       break;
        //     }
        //     // Increment
        //     slots[0]++;
        //     // Carry
        //     while (slots[index] === 2) {
        //       // Overflow, we're done
        //       if (index === slots.length - 1) {
        //           console.log('breaks');
        //           break iter;
        //       }
        //       slots[index++] = 0;
        //       slots[index]++;
        //     }
        //     index = 0;
        //   }
        // }

        const checkCombo = (combo) => { // TODO This doesn't have to be anonymous
          let valid = true;
          for (let tile of group) {
            const mines = blankNeighbors[tile].filter(blank => arrayIncludesTile(combo, blank)).length;
            if (mines !== this.getValue(tile) - this.getFlaggedNeighbors(tile).length) {
              valid = false;
              break;
            }
          }
          if (valid) {
            combo.forEach(tile => mineCounts[tile]++);
            count++;
          }
        }

        const numCombos = 2 ** allBlankNeighbors.length;
        if (numCombos <= MAX_ITERS) {
          // Initialize the slots to hold the current iteration value for each depth
          const slots = Array(allBlankNeighbors.length).fill(0);
          let index = 0;
          iter: {
            while (true) {
              let combo = [];
              let valid = true;
              for (let i = 0; i < slots.length; i++) {
                if (slots[i]) {
                  combo.push(allBlankNeighbors[i]);
                  if (combo.length > this.mines) {
                    valid = false;
                    break;
                  }
                }
              }
              if (valid) {
                checkCombo(combo);
              }
              // Increment
              slots[0]++;
              // Carry
              while (slots[index] === 2) {
                // Overflow, we're done
                if (index === slots.length - 1) {
                  break iter;
                }
                slots[index++] = 0;
                slots[index]++;
              }
              index = 0;
            }
          }
        } else if (numCombos <= MAX_ITERS * GUESS_FACTOR) {
          for (let _ = 0; _ < MAX_ITERS; _++) {
            const combo = [];
            let serialized = Math.floor(Math.random() * numCombos);
            let valid = true;
            for (let i = 0; serialized !== 0; i++) {
              if (serialized & 1) {
                combo.push(allBlankNeighbors[i]);
                if (combo.length > this.mines) {
                  valid = false;
                  break;
                }
              }
              serialized >>= 1;
            }
            if (valid) {
              checkCombo(combo);
            }
          }
        }

        if (count === 0) {
          const neighbors = blankNeighbors[group[Math.floor(Math.random() * group.length)]];
          mineProbs[neighbors[Math.floor(Math.random() * neighbors.length)]] = 0;
        } else {
          for (let key in mineCounts) {
            const tile = stringToTile(key);
            mineProbs[tile] = mineCounts[tile] / count;
          }
        }
      }
    } else {
      board: {
        for (let i = 0; i < this.width; i++) {
          for (let j = 0; j < this.height; j++) {
            if (this.board[j][i] === -2) {
              mineProbs[[i, j]] = 0;
              break board;
            }
          }
        }
      }
    }
    return mineProbs;
  }

  makeProbableMove() {
    const mineProbs = this.getProbabilities();
    const keys = Object.keys(mineProbs);
    const vals = Object.values(mineProbs);
    if (vals.includes(0) || vals.includes(1)) {
      const tile = stringToTile(keys.find(tile => mineProbs[tile] === 0));
      if (tile) {
        return { uncover: [tile], flag: [] };
      }
      tile = stringToTile(keys.find(tile => mineProbs[tile] === 1));
      this.flag(tile);
      return { uncover: [], flag: [tile] };
    } else {
      const minProb = Math.min(...vals);
      return { uncover: [stringToTile(keys.find(tile => mineProbs[tile] === minProb))], flag: [] };
    }
  }

  makeProbableMoves() {
    const moves = { uncover: [], flag: [] };
    const mineProbs = this.getProbabilities();
    const keys = Object.keys(mineProbs);
    const vals = Object.values(mineProbs);
    if (vals.includes(0) || vals.includes(1)) {
      moves.uncover = keys.filter(tile => mineProbs[tile] === 0).map(str => stringToTile(str));
      const toFlag = keys.filter(tile => mineProbs[tile] === 1).map(str => stringToTile(str));
      moves.flag = toFlag;
      toFlag.forEach(tile => this.flag(tile));
    } else {
      const minProb = Math.min(...vals);
      moves.uncover = [stringToTile(keys.find(tile => mineProbs[tile] === minProb))];
    }
    return moves;
  }
}

function getValueFromClass(name) {
  if (name.startsWith('open')) {
    return parseInt(name[4]);
  }
  return name === 'bombflagged' ? -1 : -2;
}

class Minesweeper {
  constructor() {
    this.width = 0;
    for (let i = 1;; i++) {
      const square = document.getElementById('1_' + i);
      if (!square || square.style.display === 'none') {
        break;
      }
      this.width++;
    }
    this.height = 0;
    for (let i = 1;; i++) {
      const square = document.getElementById(i + '_1');
      if (!square || square.style.display === 'none') {
        break;
      }
      this.height++;
    }
    const mines = 100 * parseInt(document.getElementById('mines_hundreds').className[4]) +
        10 * parseInt(document.getElementById('mines_tens').className[4]) +
        parseInt(document.getElementById('mines_ones').className[4]);
    this.game = new Game(this.width, this.height, mines);
    this.update();
  }

  update() {
    const board = [...Array(this.height)].map(() => Array(this.width));
    const squares = document.getElementsByClassName('square');
    for (let square of squares) {
      const [y, x] = square.id.split('_').map(i => parseInt(i));
      if (x !== 0 && y !== 0 && x <= this.width && y <= this.height) {
        board[y - 1][x - 1] = getValueFromClass(square.classList[1]);
      }
    }
    this.game.updateBoard(board);
    this.game.updateGroups();
  }

  uncover(tile) {
    const [x, y] = tile;
    const elem = document.getElementById((y + 1) + '_' + (x + 1));
    const e = document.createEvent('MouseEvents');
    e.initMouseEvent('mouseup', true, true, window, 0, 0, 0, elem.clientLeft, elem.clientTop, false, false, false, false, 0, null);
    elem.dispatchEvent(e);
  }

  flag(tile) {
    const [x, y] = tile;
    const elem = document.getElementById((y + 1) + '_' + (x + 1));
    const down = document.createEvent('MouseEvents');
    down.initMouseEvent('mousedown', true, true, window, 0, 0, 0, elem.clientLeft, elem.clientTop, false, false, false, false, 2, null);
    elem.dispatchEvent(down);
    const up = document.createEvent('MouseEvents');
    up.initMouseEvent('mouseup', true, true, window, 0, 0, 0, elem.clientLeft, elem.clientTop, false, false, false, false, 2, null);
    elem.dispatchEvent(up);
  }

  checkWin() {
    if (document.getElementsByClassName('facesmile').length) {
      return 0;
    } else if (document.getElementsByClassName('facedead').length) {
      return -1;
    } else if (document.getElementsByClassName('facewin').length) {
      return 1;
    }
  }

  execute(moves) {
    moves.uncover.forEach(tile => this.uncover(tile));
    moves.flag.forEach(tile => this.flag(tile));
    this.update();
  }

  solve() {
    const timeout = parseInt(document.getElementById('solve-interval').value);
    const move = () => {
      let moves = this.game.makeSimpleMoves();
      if (moves.uncover.length === 0 && moves.flag.length === 0) {
        moves = this.game.makeComplexMoves();
        if (moves.uncover.length === 0 && moves.flag.length === 0) {
          moves = this.game.makeProbableMoves();
        }
      }
      this.execute(moves);
      if (!this.checkWin()) {
        setTimeout(move, timeout);
      }
    };
    if (!this.checkWin()) {
      setTimeout(move, timeout);
    }
  }

  step() {
    let moves = this.game.makeSimpleMove();
    if (moves.uncover.length === 0 && moves.flag.length === 0) {
      moves = this.game.makeComplexMove();
      if (moves.uncover.length === 0 && moves.flag.length === 0) {
        moves = this.game.makeProbableMove();
      }
    }
    this.execute(moves);
  }

  check() {
    let moves = this.game.makeSimpleMove();
    if (moves.uncover.length === 0 && moves.flag.length === 0) {
      moves = this.game.makeComplexMove();
      if (moves.uncover.length === 0 && moves.flag.length === 0) {
        return true;
      }
    }
    return false;
  }
}

const rightColumn = document.getElementsByClassName('right-column')[0];
const div = document.createElement('div');
const solveButton = document.createElement('button');
const stepButton = document.createElement('button');
const solveInterval = document.createElement('input');
const guessCheckButton = document.createElement('button');
const guessCheckP = document.createElement('p');
solveInterval.id = 'solve-interval';
solveInterval.type = 'number';
solveInterval.min = 0;
solveInterval.placeholder = 'Solve Interval (ms)';
div.appendChild(solveButton);
div.appendChild(stepButton);
div.appendChild(solveInterval);
div.appendChild(guessCheckButton);
div.appendChild(guessCheckP);
solveButton.innerHTML = 'Solve';
stepButton.innerHTML = 'Step';
guessCheckButton.innerHTML = 'Do I have to guess?'
solveButton.addEventListener('click', () => {
  const ms = new Minesweeper();
  ms.solve();
});
stepButton.addEventListener('click', () => {
  const ms = new Minesweeper();
  ms.step();
});
guessCheckButton.addEventListener('click', () => {
  guessCheckP.innerHTML = 'Checking...'
  const ms = new Minesweeper();
  guessCheckP.innerHTML = ms.check() ? 'Yes!' : 'No!'
})
rightColumn.insertBefore(div, rightColumn.firstChild);