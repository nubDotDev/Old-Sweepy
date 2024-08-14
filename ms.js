// Cell states
const CLOSED = -3; // Not clicked
const CLEAR = -2; // Not a mine, but value unknown
const MINE = -1;

// Game states
const LOST = -1;
const IN_PROGRESS = 0;
const WON = 1;

function swapRows(a, b, i, j) {
    const tmpRow = a[i];
    a[i] = a[j];
    a[j] = tmpRow;
    const tmpNum = b[i];
    b[i] = b[j];
    b[j] = tmpNum;
}

function factorialFactory() {
    const cache = {};
    return (n) => {
        if (n in cache) {
            return cache[n];
        }
        let res = 1n;
        for (let i = 2n; i <= n; i++) {
            res *= i;
        }
        return (cache[n] = res);
    };
}

const factorial = factorialFactory();

function binomFactory(n) {
    const cache = {};
    return (k) => {
        if (k in cache) {
            return cache[k];
        }
        const lo = k > n / 2 ? k : n - k;
        let res = 1n;
        for (let i = BigInt(lo); i <= n; i++) {
            res *= i;
        }
        res /= factorial(n - lo);
        return (cache[k] = res);
    };
}

function invPerm(sigma) {
    const tau = {};
    sigma.forEach((i, j) => (tau[i] = j));
    return tau;
}

function bigIntDivide(a, b, minPlaces = 5) {
    let scale;
    if (a >= b) {
        scale = minPlaces;
    } else {
        const aStr = a.toString();
        const bStr = b.toString();
        scale = Math.max(minPlaces, bStr.length - aStr.length);
    }
    scale = Math.pow(10, scale);
    return Number((a * BigInt(scale)) / b) / scale;
}

class Game {
    setDims(width, height) {
        this.width = width;
        this.height = height;
        this.n = width * height;
        this.board = Array(this.n).fill(CLOSED);
    }

    get(i) {
        return this.board[i];
    }

    set(i, val) {
        this.board[i] = val;
    }

    clear(i) {
        this.set(i, CLEAR);
    }

    flag(i) {
        if (this.get(i) === MINE) {
            return;
        }
        this.set(i, MINE);
        this.mines--;
    }

    xytoi(x, y) {
        return y * this.width + x;
    }

    itoxy(i) {
        return [i % this.width, Math.floor(i / this.width)];
    }

    getNeighbors(i) {
        const neighbors = [];
        const [x, y] = this.itoxy(i);
        for (
            let y1 = Math.max(y - 1, 0);
            y1 < Math.min(y + 2, this.height);
            y1++
        ) {
            for (
                let x1 = Math.max(x - 1, 0);
                x1 < Math.min(x + 2, this.width);
                x1++
            ) {
                if (x1 !== x || y1 !== y) {
                    neighbors.push(this.xytoi(x1, y1));
                }
            }
        }
        return neighbors;
    }

    countNeighboringMines(i) {
        let neighboringMines = 0;
        for (let i1 of this.getNeighbors(i)) {
            if (this.get(i1) === MINE) {
                neighboringMines++;
            }
        }
        return neighboringMines;
    }

    getClosedNeighbors(i) {
        const closedNeighbors = [];
        for (let i1 of this.getNeighbors(i)) {
            if (this.get(i1) === CLOSED) {
                closedNeighbors.push(i1);
            }
        }
        return closedNeighbors;
    }

    isActive(i) {
        if (this.get(i) !== CLOSED) {
            return false;
        }
        for (let i1 of this.getNeighbors(i)) {
            if (this.get(i1) >= 0) {
                return true;
            }
        }
        return false;
    }

    getActiveNeighbors(i) {
        const activeNeighbors = [];
        for (let i1 of this.getNeighbors(i)) {
            if (this.isActive(i1)) {
                activeNeighbors.push(i1);
            }
        }
        return activeNeighbors;
    }

    /**
     * Frontier cells are those which are neighbors of closed cells
     * Active cells are the neighbors of frontier cells
     *
     * @returns {{ activeCells: number[], frontierCells: number[] }} `activeCells` may be out of order
     */
    getActiveAndFrontierCells() {
        const activeCells = [];
        const frontierCells = [];
        const visited = new Set();
        for (let i = 0; i < this.n; i++) {
            if (this.get(i) <= 0) {
                continue;
            }
            const closedNeighbors = this.getClosedNeighbors(i);
            if (closedNeighbors.length === 0) {
                continue;
            }
            closedNeighbors.forEach((i1) => {
                if (!visited.has(i1)) {
                    activeCells.push(i1);
                    visited.add(i1);
                }
            });
            frontierCells.push(i);
        }
        activeCells.sort((a, b) => a - b);
        return { activeCells, frontierCells };
    }

    getClosedCells() {
        const closedCells = [];
        for (let i = 0; i < this.n; i++) {
            if (this.get(i) === CLOSED) {
                closedCells.push(i);
            }
        }
        return closedCells;
    }
}

class Solver {
    constructor(game) {
        this.game = game;
    }

    /**
     * Solves the game using the simple, linear algebra,
     * and brute force methods in that order
     *
     * @param {boolean} [guess=false] Whether to guess if needed
     *
     * @returns {{ mines: Set<number>, clears: Set<number> }}
     */
    solve(guess = false) {
        // Start in the middle
        if (this.game.getClosedCells().length === this.game.n) {
            return {
                mines: new Set(),
                clears: new Set([
                    this.game.xytoi(
                        Math.floor(this.game.width / 2),
                        Math.floor(this.game.height / 2)
                    ),
                ]),
            };
        }

        const solution = {};

        const simple = this.simpleSolve();
        solution.simple = simple;
        if (simple.mines.size || simple.clears.size) {
            return solution;
        }
        const linAlg = this.linAlgSolve();
        solution.linAlg = { mines: linAlg.mines, clears: linAlg.clears };
        if (linAlg.mines.size || linAlg.clears.size) {
            return solution;
        }
        const brute = this.bruteSolve(
            linAlg.a,
            linAlg.b,
            linAlg.sigma,
            linAlg.tau
        );
        solution.brute = brute;
        if (!guess || linAlg.mines.size || linAlg.clears.size) {
            return solution;
        }
        solution.guess = this.guess(brute.probabilities);
        return solution;
    }

    /**
     * Solves the game using four rules:
     *   1. if (cell value) - (# flagged neighbors) = (# closed neighbors),
     *      then flag all closed neighbors
     *   2. if (cell value) - (# flagged nieghbors) = 0,
     *      then clear all closed neighbors
     *   3. if (# flags) = (# mines),
     *      then clear all closed cells
     *   4. if (# closed cells) = (# mines) - (# flags),
     *      then flag all closed cells
     *
     * @returns {{ mines: Set<number>, clears: Set<number> }}
     */
    simpleSolve() {
        const mines = new Set();
        const clears = new Set();

        let cont = true;
        while (cont) {
            cont = false;

            for (let i = 0; i < this.game.n; i++) {
                const closedNeighbors = this.game.getClosedNeighbors(i);
                const val = this.game.get(i);
                if (closedNeighbors.length === 0) {
                    continue;
                }
                const remainingMines = val - this.game.countNeighboringMines(i);
                // Rule 1
                if (remainingMines === closedNeighbors.length) {
                    closedNeighbors.forEach((i1) => {
                        mines.add(i1);
                        this.game.flag(i1);
                        cont = true;
                    });
                }
                // Rule 2
                else if (remainingMines === 0) {
                    closedNeighbors.forEach((i1) => {
                        clears.add(i1);
                        this.game.clear(i1);
                        cont = true;
                    });
                }
            }

            const closedCells = this.game.getClosedCells();
            // Rule 3
            if (this.game.mines === 0) {
                cont = false;
                closedCells.forEach((i) => {
                    clears.add(i);
                    this.game.clear(i);
                });
            }
            // Rule 4
            else if (closedCells.length === this.game.mines) {
                cont = false;
                closedCells.forEach((i) => {
                    mines.add(i);
                    this.game.flag(i);
                });
            }
        }

        return { mines, clears };
    }

    /**
     * Solves the game as a linear system of binary variables
     *
     * @returns {{ mines: Set<number>, clears: Set<number> }}
     */
    linAlgSolve() {
        const mines = new Set();
        const clears = new Set();

        let a, b, sigma, n;

        /**
         * After each row operation, check for mines and clears
         *
         * A row is solved if the right hand side is equal to either
         * the sum of the negative entries or
         * the sum of the positive entries
         */
        function analyzeRow(x, y, deleteSolved = false) {
            let min = 0;
            let max = 0;
            const pos = [];
            const neg = [];
            for (let x1 = x; x1 < n; x1++) {
                if (a[y][x1] === 0) {
                    continue;
                }
                if (a[y][x1] > 0) {
                    max += a[y][x1];
                    pos.push(sigma[x1]);
                } else {
                    min += a[y][x1];
                    neg.push(sigma[x1]);
                }
            }
            const mineFn = (i) => {
                mines.add(i);
                this.game.flag(i);
                cont = true;
            };
            const clearFn = (i) => {
                clears.add(i);
                this.game.clear(i);
                cont = true;
            };
            if (b[y] === min) {
                neg.forEach((i) => mineFn(i));
                pos.forEach((i) => clearFn(i));
            } else if (b[y] === max) {
                pos.forEach((i) => mineFn(i));
                neg.forEach((i) => clearFn(i));
            } else {
                return;
            }
            if (deleteSolved) {
                a.splice(y);
                b.splice(y);
            }
        }

        let cont = true;
        while (cont) {
            cont = false;

            // Gaussian elimination

            ({ a, b, sigma } = this.linAlgArgs());
            n = (a[0] ?? { length: 0 }).length;

            for (let y = 0; y < a.length; y++) {
                analyzeRow.call(this, 0, y);
            }

            // Forward
            let x = 0;
            let y = 0;
            while (x < n && y < a.length) {
                let piv_y = y;
                let piv = Math.abs(a[piv_y][x]);
                for (let y1 = y + 1; y1 < a.length; y1++) {
                    if (Math.abs(a[y1][x]) > piv) {
                        piv_y = y1;
                        piv = Math.abs(a[y1][x]);
                    }
                }
                if (piv === 0) {
                    x += 1;
                    continue;
                }
                if (y !== piv_y) {
                    swapRows(a, b, y, piv_y);
                }
                let s = 1 / a[y][x];
                a[y][x] = 1;
                b[y] *= s;
                for (let x1 = x + 1; x1 < n; x1++) {
                    a[y][x1] *= s;
                }
                for (let y1 = y + 1; y1 < a.length; y1++) {
                    if (a[y1][x] === 0) {
                        continue;
                    }
                    s = a[y1][x];
                    a[y1][x] = 0;
                    b[y1] -= b[y] * s;
                    for (let x1 = x + 1; x1 < n; x1++) {
                        a[y1][x1] -= a[y][x1] * s;
                    }
                    analyzeRow.call(this, x + 1, y1);
                }
                x++;
                y++;
            }

            // Backward
            x = 0;
            y = 0;
            while (x < n && y < a.length) {
                if (a[y][x] === 0) {
                    x++;
                    continue;
                }
                for (let y1 = 0; y1 < y; y1++) {
                    if (a[y1][x] === 0) {
                        continue;
                    }
                    const s = a[y1][x];
                    a[y1][x] = 0;
                    b[y1] -= b[y] * s;
                    for (let x1 = x + 1; x1 < n; x1++) {
                        a[y1][x1] -= a[y][x1] * s;
                    }
                    analyzeRow.call(this, 0, y1);
                }
                x++;
                y++;
            }

            for (let y = 0; y < a.length; y++) {
                analyzeRow.call(this, 0, y, true);
            }
        }

        return { mines, clears };
    }

    /**
     * Solves the game by trying every possible placement of mines
     *
     * @returns {{ mines: Set<number>, clears: Set<number>, probabilities: number[] }}
     */
    bruteSolve(linAlg = undefined) {
        const mines = new Set();
        const clears = new Set();
        const probabilities = {};

        if (typeof linAlg === "undefined") {
            const linAlg = this.linAlgSolve();
            linAlg.mines.forEach((i) => mines.add(i));
            linAlg.clears.forEach((i) => clears.add(i));
        }
        const { a, b, sigma } = this.linAlgArgs();

        const n = (a[0] ?? { length: 0 }).length;

        // Get rid of rows that only contain 0
        for (let y = a.length - 1; y >= 0; y--) {
            if (a[y].every((x) => x === 0)) {
                a.splice(y, 1);
                b.splice(y, 1);
            } else {
                break;
            }
        }

        // To improve efficiency, separate the active cells according to
        // the connected components of their incidence graph
        const ds = new DisjointSet(n);
        for (let y = 0; y < a.length; y++) {
            let x = 0;
            while (a[y][x] === 0) {
                x++;
                continue;
            }
            for (let x1 = x + 1; x1 < n; x1++) {
                if (a[y][x1] !== 0) {
                    ds.union(x1, x);
                }
            }
        }
        const cellPartitionObj = {};
        for (let i = 0; i < n; i++) {
            const r = ds.find(i);
            if (r in cellPartitionObj) {
                cellPartitionObj[r].push(i);
            } else {
                cellPartitionObj[r] = [i];
            }
        }
        const as = [];
        const bs = [];
        Object.values(cellPartitionObj).forEach((part) => {
            const newA = [];
            const newB = [];
            a.forEach((row, y) => {
                if (part.some((x) => row[x] !== 0)) {
                    newA.push(row);
                    newB.push(b[y]);
                }
            });
            as.push(newA);
            bs.push(newB);
        });

        const { activeCells } = this.game.getActiveAndFrontierCells();
        const closedCells = this.game.getClosedCells();

        const groupCounts = [];
        const groupCountCounts = [];
        const groupTotalCombos = [];

        const binomInactive = binomFactory(
            closedCells.length - activeCells.length
        );

        for (let group = 0; group < as.length; group++) {
            let a1 = as[group];
            let b1 = bs[group];

            const counts = {};
            const countCounts = {};
            let totalCombos = 0n;

            const stack = [0];
            let newMines = 0;

            function backtrack() {
                while (
                    stack.at(-1) === 1 ||
                    a1.every((row) => row[stack.length - 1] === 0)
                ) {
                    newMines -= stack.at(-1);
                    stack.pop();
                }
                if (stack.length > 0) {
                    stack[stack.length - 1] = 1;
                    newMines++;
                }
            }

            while (stack.length > 0) {
                let valid = true;

                if (newMines > this.game.mines) {
                    valid = false;
                } else {
                    for (let y = 0; y < a1.length; y++) {
                        let max = 0;
                        for (let x = stack.length; x < n; x++) {
                            if (a1[y][x] === 1) {
                                max++;
                            }
                        }

                        const rhs = stack.reduce(
                            (acc, elem, idx) => acc - elem * a1[y][idx],
                            b1[y]
                        );
                        if (
                            rhs > max ||
                            rhs < 0 ||
                            (stack.length >= n && rhs !== 0)
                        ) {
                            valid = false;
                        }
                    }
                }

                if (valid) {
                    if (stack.length >= n) {
                        // Combinatorics
                        const toAdd =
                            binomInactive(this.game.mines - newMines) || 1n;

                        for (let i = 0; i < stack.length; i++) {
                            if (stack[i] === 0) {
                                continue;
                            }
                            const i1 = sigma[i];
                            if (i1 in counts) {
                                counts[i1] += toAdd;
                            } else {
                                counts[i1] = toAdd;
                            }
                        }

                        totalCombos += toAdd;

                        if (newMines in countCounts) {
                            countCounts[newMines]++;
                        } else {
                            countCounts[newMines] = 1;
                        }

                        backtrack();
                    } else {
                        stack.push(0);
                    }
                } else {
                    if (
                        stack.at(-1) === 0 &&
                        !a1.every((row) => row[stack.length - 1] === 0)
                    ) {
                        stack[stack.length - 1] = 1;
                        newMines++;
                    } else {
                        backtrack();
                    }
                }
            }

            groupCounts.push(counts);
            groupCountCounts.push(countCounts);
            groupTotalCombos.push(totalCombos);
        }

        function setProbability(i, probability) {
            probabilities[i] = probability;
            if (probabilities[i] === 1) {
                mines.add(i);
                this.game.flag(i);
            } else if (probabilities[i] === 0) {
                clears.add(i);
                this.game.clear(i);
            }
        }

        const countCounts = {};

        function generateCombinations(curr, i) {
            if (i === groupCountCounts.length) {
                const sum = curr.reduce((acc, [key]) => acc + key, 0);

                if (
                    this.game.mines - sum >
                        closedCells.length - activeCells.length ||
                    sum > this.game.mines
                ) {
                    return;
                }

                const prod = curr.reduce((acc, [, value]) => acc * value, 1);
                if (sum in countCounts) {
                    countCounts[sum] += prod;
                } else {
                    countCounts[sum] = prod;
                }
                return;
            }

            for (const [key, value] of Object.entries(groupCountCounts[i])) {
                generateCombinations.call(
                    this,
                    [...curr, [parseInt(key), value]],
                    i + 1
                );
            }
        }

        generateCombinations.call(this, [], 0);

        let inactiveProb = 0;
        let total = 0;
        for (let count in countCounts) {
            total += countCounts[count];
            inactiveProb +=
                (countCounts[count] * (this.game.mines - count)) /
                (closedCells.length - activeCells.length);
        }
        inactiveProb /= total;

        groupCounts.forEach((counts, group) => {
            for (let i in counts) {
                setProbability.call(
                    this,
                    i,
                    bigIntDivide(counts[i] ?? 0n, groupTotalCombos[group])
                );
            }
        });
        closedCells.forEach((i) => {
            if (!(i in probabilities)) {
                setProbability.call(this, i, inactiveProb);
            }
        });
        mines.forEach((i) => setProbability.call(this, i, 1));
        clears.forEach((i) => setProbability.call(this, i, 0));

        return { mines, clears, probabilities };
    }

    /**
     * Clears the cell that has lowest probability of being a mine
     *
     * If there are multiple, then preference is given to active cells
     *
     * If there are still multiple, choose a cell with the most active neighbors
     */
    guess(probabilities = undefined) {
        if (typeof probabilities === "undefined") {
            probabilities = this.bruteSolve().probabilities;
        }

        let best = -1;
        let minProb = 1;
        let isBestActive = false;
        let maxActiveNeighbors = -1;
        for (let i in probabilities) {
            if (probabilities[i] > minProb) {
                continue;
            }
            const isActive = this.game.isActive(i);
            const numActiveNeighbors = this.game.getActiveNeighbors(i).length;
            if (
                probabilities[i] < minProb ||
                (!isBestActive && isActive) ||
                (isBestActive === isActive &&
                    numActiveNeighbors > maxActiveNeighbors)
            ) {
                best = i;
                minProb = probabilities[i];
                isBestActive = isActive;
                maxActiveNeighbors = numActiveNeighbors;
                continue;
            }
        }

        this.game.clear(best);

        return best;
    }

    linAlgArgs() {
        const { activeCells: sigma, frontierCells } =
            this.game.getActiveAndFrontierCells();
        const tau = invPerm(sigma);
        const m = sigma.length;
        const a = [];
        const b = [];
        for (let i of frontierCells) {
            const val = this.game.get(i);
            if (val <= 0) {
                continue;
            }
            const closedNeighbors = this.game.getClosedNeighbors(i);
            if (closedNeighbors.length === 0) {
                continue;
            }
            const eq = Array(m).fill(0);
            for (let i1 of this.game.getClosedNeighbors(i)) {
                eq[tau[i1]] = 1;
            }
            b.push(val - this.game.countNeighboringMines(i));
            a.push(eq);
        }
        if (sigma.length === this.game.getClosedCells().length) {
            a.push(Array(m).fill(1));
            b.push(this.game.mines);
        }
        return { a, b, sigma, tau };
    }
}

class DisjointSet {
    constructor(n) {
        this.parent = [...Array(n).keys()];
    }

    find(i) {
        if (this.parent[i] === i) {
            return i;
        }
        return this.find(this.parent[i]);
    }

    union(i, j) {
        this.parent[this.find(i)] = this.find(j);
    }
}

const div = document.createElement("div");

class Website {
    constructor() {
        this.game = new Game();
        this.solver = new Solver(this.game);
        this.load().then(() => this.update());
    }

    async load() {
        return Promise.resolve();
    }

    executeSolution(solution) {
        solution.mines?.forEach((i) => this.flag(i));
        solution.clears?.forEach((i) => this.clear(i));
        solution.simple?.mines.forEach((i) => this.flag(i));
        solution.simple?.clears.forEach((i) => this.clear(i));
        solution.linAlg?.mines.forEach((i) => this.flag(i));
        solution.linAlg?.clears.forEach((i) => this.clear(i));
        solution.brute?.mines.forEach((i) => this.flag(i));
        solution.brute?.clears.forEach((i) => this.clear(i));
        if ("guess" in solution && solution.guess !== -1) {
            this.clear(solution.guess);
        }
        this.update();
        return (
            solution.mines?.size ||
            solution.clears?.size ||
            solution.simple?.mines.size ||
            solution.simple?.clears.size ||
            solution.linAlg?.mines.size ||
            solution.linAlg?.clears.size ||
            solution.brute?.mines.size ||
            solution.brute?.clears.size ||
            solution.guess
        );
    }

    update() {
        this.game.setDims(...this.getDims());

        for (let x = 0; x < this.game.width; x++) {
            for (let y = 0; y < this.game.height; y++) {
                this.game.set(
                    this.game.xytoi(x, y),
                    this.getValue(this.getCell(x, y))
                );
            }
        }

        this.game.mines = this.getMineCount();
    }

    clear(i) {
        const [x, y] = this.game.itoxy(i);
        const elem = this.getCell(x, y);
        if (this.clearMouseDown) {
            const down = new MouseEvent("mousedown", {
                bubbles: true,
                clientX: elem.clientLeft,
                clientY: elem.clientTop,
                button: 1,
            });
            elem.dispatchEvent(down);
        }
        const up = new MouseEvent("mouseup", {
            bubbles: true,
            clientX: elem.clientLeft,
            clientY: elem.clientTop,
            button: 1,
        });
        elem.dispatchEvent(up);
        elem.click();
    }

    flag(i) {
        const [x, y] = this.game.itoxy(i);
        const elem = this.getCell(x, y);
        const down = new MouseEvent("mousedown", {
            bubbles: true,
            clientX: elem.clientLeft,
            clientY: elem.clientTop,
            button: 2,
        });
        elem.dispatchEvent(down);
        const up = new MouseEvent("mouseup", {
            bubbles: true,
            clientX: elem.clientLeft,
            clientY: elem.clientTop,
            button: 2,
        });
        elem.dispatchEvent(up);
    }

    showProbabilities(probabilities) {
        for (let x = 0; x < this.game.width; x++) {
            for (let y = 0; y < this.game.height; y++) {
                const i = this.game.xytoi(x, y);
                const elem = this.getCell(x, y);
                if (i in probabilities) {
                    elem.style.fontSize = "8px";
                    elem.style.display = "flex";
                    elem.style.justifyContent = "center";
                    elem.style.alignItems = "center";
                    elem.innerHTML = Math.round(probabilities[i] * 100);
                } else {
                    elem.innerHTML = "";
                }
            }
        }
    }

    hideProbabilities() {
        for (let x = 0; x < this.game.width; x++) {
            for (let y = 0; y < this.game.height; y++) {
                this.getCell(x, y).innerHTML = "";
            }
        }
    }

    inject() {
        throw new Error("Not implemented");
    }

    getDims() {
        throw new Error("Not implemented");
    }

    getCell() {
        throw new Error("Not implemented");
    }

    getValue() {
        throw new Error("Not implemented");
    }

    getMineCount() {
        throw new Error("Not implemented");
    }

    getState() {
        throw new Error("Not implemented");
    }
}

class MinesweeperOnlineCom extends Website {
    inject() {
        const rightColumn = document.getElementsByClassName("right-column")[0];
        rightColumn.insertBefore(div, rightColumn.firstChild);
    }

    getDims() {
        let width = 0;
        for (let i = 1; ; i++) {
            const elem = document.getElementById("1_" + i);
            if (!elem || elem.style.display === "none") {
                break;
            }
            width++;
        }
        let height = 0;
        for (let i = 1; ; i++) {
            const elem = document.getElementById(i + "_1");
            if (!elem || elem.style.display === "none") {
                break;
            }
            height++;
        }
        return [width, height];
    }

    getCell(x, y) {
        return document.getElementById(y + 1 + "_" + (x + 1));
    }

    getValue(elem) {
        const name = elem.classList[1];
        if (name.startsWith("open")) {
            return parseInt(name[4]);
        }
        return name === "bombflagged" ? MINE : CLOSED;
    }

    getMineCount() {
        return (
            100 *
                parseInt(
                    document.getElementById("mines_hundreds").className[4]
                ) +
            10 * parseInt(document.getElementById("mines_tens").className[4]) +
            parseInt(document.getElementById("mines_ones").className[4])
        );
    }

    getState() {
        if (document.getElementsByClassName("facesmile").length) {
            return IN_PROGRESS;
        } else if (document.getElementsByClassName("facedead").length) {
            return LOST;
        } else if (document.getElementsByClassName("facewin").length) {
            return WON;
        }
        throw new Error("Unknown state");
    }
}

class MinesweeperOnline extends Website {
    constructor() {
        super();
        this.clearMouseDown = true;
    }

    load() {
        return new Promise((resolve) => {
            function check() {
                const elem = document.getElementById("game");
                if (elem) {
                    resolve();
                } else {
                    setTimeout(check, 1000);
                }
            }
            check();
        });
    }

    inject() {
        document.getElementsByClassName("main-column")[0].appendChild(div);
    }

    getDims() {
        let width = 0;
        for (let i = 0; ; i++) {
            const elem = document.getElementById("cell_" + i + "_0");
            if (!elem) {
                break;
            }
            width++;
        }
        let height = 0;
        for (let i = 0; ; i++) {
            const elem = document.getElementById("cell_0_" + i);
            if (!elem) {
                break;
            }
            height++;
        }
        return [width, height];
    }

    getCell(x, y) {
        return document.getElementById("cell_" + x + "_" + y);
    }

    getValue(elem) {
        if (elem.classList.contains("hdd_opened")) {
            return parseInt(
                Array.from(elem.classList).find((name) =>
                    name.startsWith("hdd_type")
                )[8]
            );
        }
        return elem.classList.contains("hdd_flag") ? MINE : CLOSED;
    }

    getMineCount() {
        return [100, 10, 1].reduce(
            (acc, elem) =>
                acc +
                parseInt(
                    elem *
                        Array.from(
                            document.getElementById("top_area_mines_" + elem)
                                .classList
                        ).find((name) =>
                            name.startsWith("hdd_top-area-num")
                        )[16]
                ),
            0
        );
    }

    getState() {
        if (
            document.getElementsByClassName("hdd_top-area-face-unpressed")
                .length
        ) {
            return IN_PROGRESS;
        } else if (
            document.getElementsByClassName("hdd_top-area-face-lose").length
        ) {
            return LOST;
        } else if (
            document.getElementsByClassName("hdd_top-area-face-win").length
        ) {
            return WON;
        }
        throw new Error("Unknown state");
    }

    executeSolution(solution) {
        const res = super.executeSolution(solution);
        let cont = true;
        for (let x = 0; cont && x < this.game.width; x++) {
            for (let y = 0; y < this.game.height; y++) {
                if (this.getCell(x, y).classList.contains("start")) {
                    this.clear(this.game.xytoi(x, y));
                    cont = false;
                    break;
                }
            }
        }
        return res;
    }
}

const alpha = [
    "A",
    "B",
    "C",
    "D",
    "E",
    "F",
    "G",
    "H",
    "I",
    "J",
    "K",
    "L",
    "M",
    "N",
    "O",
    "P",
];

class CardGamesIO extends Website {
    constructor() {
        super();
        document.head.insertAdjacentHTML(
            "beforeend",
            "<style>" +
                "td.closed { color: black; font-size: 8px !important; }" +
                "#puzzle td { font-size: 0px; }" +
                "td.nr { font-size: 16px !important; }</style>"
        );
    }

    inject() {
        document.getElementById("board").insertAdjacentElement("afterend", div);
    }

    getDims() {
        switch (document.getElementsByClassName("pressed")[0].id) {
            case "beginner":
                return [8, 8];
            case "intermediate":
                return [16, 16];
            case "expert":
                return [31, 16];
        }
    }

    getCell(x, y) {
        return document.getElementById(alpha[y] + (x + 1));
    }

    getValue(elem) {
        switch (elem.className) {
            case "flag":
                return MINE;
            case "closed":
                return CLOSED;
            case "blank":
                return 0;
            default:
                return parseInt(elem.className[5]);
        }
    }

    getMineCount() {
        return parseInt(document.getElementById("mines-left").innerHTML);
    }

    getState() {
        if (document.getElementsByClassName("dead").length) {
            return LOST;
        } else if (document.getElementsByClassName("winner").length) {
            return WON;
        } else if (
            document
                .getElementsByClassName("face-top-player")[0]
                .classList.contains("normal")
        ) {
            return IN_PROGRESS;
        }
        throw new Error("Unknown state");
    }

    showProbabilities(probabilities) {
        for (let x = 0; x < this.game.width; x++) {
            for (let y = 0; y < this.game.height; y++) {
                const i = this.game.xytoi(x, y);
                const elem = this.getCell(x, y);
                if (i in probabilities) {
                    elem.innerHTML = Math.round(probabilities[i] * 100);
                }
            }
        }
    }

    hideProbabilities() {
        for (let x = 0; x < this.game.width; x++) {
            for (let y = 0; y < this.game.height; y++) {
                if (this.game.get(this.game.xytoi(x, y)) === CLOSED) {
                    this.getCell(x, y).innerHTML = "";
                }
            }
        }
    }
}

const websiteFactory = () => {
    let website = undefined;
    return () => {
        if (typeof website === "undefined") {
            if (window.location.href === "https://minesweeperonline.com/") {
                website = new MinesweeperOnlineCom();
            } else if (
                /^https:\/\/minesweeper\.online\/game\/\d+$/.test(
                    window.location.href
                )
            ) {
                website = new MinesweeperOnline();
            } else if (
                window.location.href === "https://cardgames.io/minesweeper/"
            ) {
                website = new CardGamesIO();
            }
            website.inject();
        }
        return website;
    };
};

const website = websiteFactory()();

const cheatDiv = document.createElement("div");
const solveButton = document.createElement("button");
const stepButton = document.createElement("button");
const guessLabel = document.createElement("label");
const guessCheckbox = document.createElement("input");
const solveInterval = document.createElement("input");
const probabilitiesDiv = document.createElement("div");
const probabilitiesLabel = document.createElement("label");
const probabilitiesCheckbox = document.createElement("input");
const guessCheckDiv = document.createElement("div");
const guessCheckButton = document.createElement("button");
const guessCheckSpan = document.createElement("span");
const howHardDiv = document.createElement("div");
const howHardButton = document.createElement("button");
const howHardSpan = document.createElement("span");
guessLabel.for = "guess";
guessCheckbox.id = "guess";
guessCheckbox.type = "checkbox";
guessCheckbox.checked = true;
solveInterval.id = "solve-interval";
solveInterval.type = "number";
solveInterval.min = 10;
solveInterval.value = 500;
solveInterval.placeholder = "Solve Interval (ms)";
probabilitiesLabel.for = "probabilities";
probabilitiesCheckbox.id = "probabilities";
probabilitiesCheckbox.type = "checkbox";
div.append(cheatDiv);
cheatDiv.appendChild(solveButton);
cheatDiv.appendChild(stepButton);
cheatDiv.appendChild(guessLabel);
cheatDiv.appendChild(guessCheckbox);
div.appendChild(solveInterval);
div.appendChild(probabilitiesDiv);
probabilitiesDiv.appendChild(probabilitiesLabel);
probabilitiesDiv.appendChild(probabilitiesCheckbox);
div.appendChild(guessCheckDiv);
guessCheckDiv.appendChild(guessCheckButton);
guessCheckDiv.appendChild(guessCheckSpan);
div.appendChild(howHardDiv);
howHardDiv.appendChild(howHardButton);
howHardDiv.appendChild(howHardSpan);
solveButton.innerHTML = "Solve";
stepButton.innerHTML = "Step";
guessLabel.innerHTML = "Guess?";
probabilitiesLabel.innerHTML = "Show probabilities";
guessCheckButton.innerHTML = "Do I have to guess?";
howHardButton.innerHTML = "How hard is this?";
const checkInProgress = (fn) => () => {
    if (website.getState() !== IN_PROGRESS) {
        return;
    }
    return fn();
};
solveButton.addEventListener("click", () => {
    website.update();
    const timeout = parseInt(document.getElementById("solve-interval").value);
    website.solving = !website.solving;
    if (website.solving) {
        solveButton.innerHTML = "Stop";
        const step = checkInProgress(() => {
            if (website.solving) {
                if (
                    website.executeSolution(
                        website.solver.solve(guessCheckbox.checked)
                    )
                ) {
                    if (website.getState() === IN_PROGRESS) {
                        setTimeout(step, timeout);
                    }
                } else {
                    website.solving = false;
                    solveButton.innerHTML = "Solve";
                }
            }
        });
        step();
    } else {
        solveButton.innerHTML = "Solve";
    }
});
stepButton.addEventListener(
    "click",
    checkInProgress(() => {
        website.update();
        website.executeSolution(website.solver.solve(guessCheckbox.checked));
    })
);
probabilitiesCheckbox.addEventListener(
    "click",
    checkInProgress(() => {
        website.update();
        if (probabilitiesCheckbox.checked) {
            website.showProbabilities(
                website.solver.bruteSolve().probabilities
            );
        } else {
            website.hideProbabilities();
        }
    })
);
guessCheckButton.addEventListener(
    "click",
    checkInProgress(() => {
        website.update();
        const solution = website.solver.solve(true);
        guessCheckSpan.innerHTML = "guess" in solution ? "Yes!" : "No!";
    })
);
howHardButton.addEventListener(
    "click",
    checkInProgress(() => {
        website.update();
        const solution = website.solver.solve();
        if (solution.mines?.size || solution.clears?.size) {
            howHardSpan.innerHTML = "You can clear any space";
        } else if (
            solution.simple?.mines.size ||
            solution.simple?.clears.size
        ) {
            howHardSpan.innerHTML = "You need basic logic to progress";
        } else if (
            solution.linAlg?.mines.size ||
            solution.linAlg?.clears.size
        ) {
            howHardSpan.innerHTML = "You need advanced logic to progress";
        } else if (solution.brute?.mines.size || solution.brute?.clears.size) {
            howHardSpan.innerHTML =
                "You need brute force or advanced mine-counting to progress";
        } else {
            howHardSpan.innerHTML = "You need to guess";
        }
    })
);
