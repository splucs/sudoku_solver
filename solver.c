#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#define MAXN 21
#define NUM_BUFS 5

typedef unsigned char bool;
#define true 1
#define false 0

#define MAX_MASK_COUNT 5
#define MAX_MASKS 5009
int masksByBitCount[MAX_MASK_COUNT][MAX_MASKS];
int maskCountByBitCount[MAXN];
#define isBitOn(mask, i) ((mask) & (1<<(i)))
#define flipBit(mask, i) (mask ^= (1<<(i)))
#define turnBitOn(mask, i) (mask |= (1<<(i)))
#define turnBitOff(mask, i) (mask &= ~(1<<(i)))
#define bitCount(mask) __builtin_popcount(mask)
#define lastBitPos(mask) __builtin_ctz(mask)
#define lastBitOnly(mask) ((mask) & -(mask))
#define turnLastBitOff(mask) (mask &= ~lastBitOnly(mask))

clock_t startTime;
FILE *inputFile, *outputFile, *instructionFile;

void cleanUp() {
    if (inputFile != stdin) {
        fclose(inputFile);
    }
    if (outputFile != stdout) {
        fclose(outputFile);
    }
    if (instructionFile != stdout && instructionFile != outputFile) {
        fclose(instructionFile);
    }
}

bool debug, verbose, instructions, noGuessing, help;

char fmtBufs[NUM_BUFS][1009];
int fmtBufIndex = 0;
const char* fmt(const char* template, ...) {
    if (!debug && !verbose && !instructions) {
        return "";
    }
    va_list args;
    va_start(args, template);
    int i = fmtBufIndex;
    fmtBufIndex = (fmtBufIndex + 1) % NUM_BUFS;
    vsprintf(fmtBufs[i], template, args);
    va_end(args);
    return fmtBufs[i];
}

void levelLog(const char* level, const char* msg) {
    clock_t curTime = clock();
    clock_t elapsedTime = curTime - startTime;
    int timeMs = elapsedTime * 1000 / CLOCKS_PER_SEC;
    printf("[%dms][%s]: %s\n", timeMs, level, msg);
}

void debugf(const char* msg) {
    if (debug) {
        levelLog("DEBUG", msg);
    }
}

void infof(const char* msg) {
    if (verbose) {
        levelLog("INFO", msg);
    }
}

void fatalf(const char* msg) {
    levelLog("FATAL", msg);
    cleanUp();
    exit(1);
}

int numberList[NUM_BUFS][MAXN];
int numberListIndex = 0;
const int* maskToList(int mask) {
    int sz = 0, u;
    int i = numberListIndex;
    numberListIndex = (numberListIndex + 1) % NUM_BUFS;
    while (mask > 0) {
        u = lastBitPos(mask);
        numberList[i][sz++] = u;
        turnBitOff(mask, u);
    }
    return numberList[i];
}

char numbersBuf[NUM_BUFS][1009];
char numbersBufIndex = 0;
const char* prettyBufNumbers(const int *arr, int n) {
    int i = numbersBufIndex;
    numbersBufIndex = (numbersBufIndex + 1) % NUM_BUFS;
    char numberBuf[5];
    strcpy(numbersBuf[i], "[");
    int sz = strlen(numbersBuf[i]);
    for (int j = 0; j < n; j++) {
        sprintf(numberBuf, "%d ", arr[j]);
        strcpy(numbersBuf[i] + sz, numberBuf);
        sz += strlen(numberBuf);
    }
    numbersBuf[i][sz-1] = ']';
    return numbersBuf[i];
}

char sudokuBuf[1009];
const char* prettyBufSudoku(int sudoku[MAXN][MAXN], int nm) {
    sudokuBuf[0] = '\0';
    char numberBuf[5];
    char template[10];
    if (nm < 10) {
        sprintf(template, "%%d ");
    } else {
        sprintf(template, "%%2d ");
    }
    int sz = 0;
    for (int i = 0; i < nm; i++) {
        for (int j = 0; j < nm; j++) {
            sprintf(numberBuf, template, sudoku[i][j]);
            strcpy(sudokuBuf + sz, numberBuf);
            sz += strlen(numberBuf);
        }
        sudokuBuf[sz-1] = '\n';
    }
    return sudokuBuf;
}

int n, m, nm;
int sudoku[MAXN][MAXN], initialDiscoveries;
bool restricted, impossible, done;

#define DISCOVER 1
#define CANNOT_BE 2
#define REASON_BUF 209
#define MAXEVENTS 10009
typedef struct event {
    int type;
    int i, j, u;
    char reason[REASON_BUF];
} event;

event events[MAXEVENTS];
int eventCount = 0;

#define ROW 0
#define COL 1
#define QUA 2

typedef struct block {
    int index;
    int dimensionId;
    const char *dimensionName;
    int canBePosMask[MAXN];
    int it[MAXN];
    int jt[MAXN];
} block;

block blocks[3][MAXN];
block *blocksByPos[MAXN][MAXN][3];

int discoveries, guesses, steps;

int canBeMask[MAXN][MAXN];
#define canBe(i, j, u) isBitOn(canBeMask[i][j], u)
#define canBeCount(i, j) bitCount(canBeMask[i][j])
#define canBeLast(i, j) lastBitPos(canBeMask[i][j])

void rollbackEvents(const int eventIndex) {
    while (eventCount > eventIndex) {
        event e = events[--eventCount];
        if (e.type == DISCOVER) {
            sudoku[e.i][e.j] = 0;
            discoveries--;
        } else if (e.type == CANNOT_BE) {
            turnBitOn(canBeMask[e.i][e.j], e.u);
            for (int d = 0; d < 3; d++) {
                block *b = blocksByPos[e.i][e.j][d];
                for (int t = 0; t < nm; t++) {
                    int ni = b->it[t], nj = b->jt[t];
                    if (ni == e.i && nj == e.j) {
                        turnBitOn(b->canBePosMask[e.u], t);
                        break;
                    }
                }
            }
        } else {
            fatalf(fmt("Found event of unknown type %d.", e.type));
        }
    }
}

void applyEvent(const event e) {
    events[eventCount++] = e;
    steps++;

    if (e.type == DISCOVER) {
        sudoku[e.i][e.j] = e.u;
        discoveries++;
        debugf(fmt("Discovered number %d at position (%d,%d); reason: %s; discoveries: %d.", e.u, e.i, e.j, e.reason, discoveries));
        if (discoveries == nm*nm) {
            done = true;
        }
    } else if (e.type == CANNOT_BE) {
        turnBitOff(canBeMask[e.i][e.j], e.u);
        for (int d = 0; d < 3; d++) {
            block *b = blocksByPos[e.i][e.j][d];
            for (int t = 0; t < nm; t++) {
                int ni = b->it[t], nj = b->jt[t];
                if (ni == e.i && nj == e.j) {
                    turnBitOff(b->canBePosMask[e.u], t);
                    break;
                }
            }
        }

        int cnt = canBeCount(e.i, e.j);
        const int *canBeList = maskToList(canBeMask[e.i][e.j]);
        debugf(fmt("Number %d cannot be at (%d,%d); reason: %s; possiblities left: %s.", e.u, e.i, e.j, e.reason, prettyBufNumbers(canBeList, cnt)));
    } else {
        fatalf(fmt("Found event of unknown type %d.", e.type));
    }

    // signal that we made progress this round
    restricted = true;
}

void discover(int i, int j, int u, const char *reason) {
    if (impossible) {
        return;
    }
    if (sudoku[i][j] != 0) {
        if (sudoku[i][j] != u) {
            debugf(fmt("Inconsistency in discovery; found %d and %d at (%d,%d); reason for latest: %s.", sudoku[i][j], u, i, j, reason));
            impossible = true;
        }
        return;
    }

    // create event
    event e;
    e.type = DISCOVER;
    e.i = i;
    e.j = j;
    e.u = u;
    if (reason != NULL) {
        strcpy(e.reason, reason);
    }

    // change state of the world
    applyEvent(e);
}

void cannotBe(int i, int j, int u, const char *reason) {
    if (impossible || !canBe(i, j, u)) {
        return;
    }

    // create event
    event e;
    e.type = CANNOT_BE;
    e.i = i;
    e.j = j;
    e.u = u;
    if (reason != NULL) {
        strcpy(e.reason, reason);
    }

    // change state of the world
    applyEvent(e);
    
    // hidden single
    for (int d = 0; d < 3; d++) {
        block *b = blocksByPos[i][j][d];
        int left = bitCount(b->canBePosMask[u]);
        if (left == 0) {
            debugf(fmt("Inconsistency in restriction of (%d,%d) to %d; no remaining possibilities for the number in %s %d; reason for latest: %s.", i, j, u, b->dimensionName, b->index, reason));
            impossible = true;
            return;
        } else if (left == 1) {
            int t = lastBitPos(b->canBePosMask[u]);
            int ni = b->it[t], nj = b->jt[t];
            if (canBe(ni, nj, u)) {
                discover(ni, nj, u, fmt("it is the last possibility for the %s; discoveries: %d", b->dimensionName, discoveries+1));
            }
        }
    }

    // naked single
    if (canBeCount(i, j) == 1) {
        discover(i, j, canBeLast(i, j), fmt("it is the last possibility for the cell; discoveries: %d", discoveries+1));
    }
}

void init() {
    // reset global control variables
    done = impossible = false;
    // reset global statistics variables
    guesses = steps = 0;
    // reset events
    eventCount = 0;
    // reset discoveries to identify when the game is done
    discoveries = initialDiscoveries;
    // set canBeMask to 111..1110 (nm 1's)
    for (int i = 0; i < nm; i++) {
        for (int j = 0; j < nm; j++) {
            canBeMask[i][j] = ((1<<nm)-1)<<1;
        }
    }
    // build row blocks
    for(int r = 0; r < nm; r++) {
        blocks[ROW][r].index = r;
        blocks[ROW][r].dimensionId = ROW;
        blocks[ROW][r].dimensionName = "row";
        for (int u = 1; u <= nm; u++) {
            blocks[ROW][r].canBePosMask[u] = (1<<nm)-1;
        }
        for (int t = 0; t < nm; t++) {
            blocks[ROW][r].it[t] = r;
            blocks[ROW][r].jt[t] = t;
        }
    }
    // build columns blocks
    for(int c = 0; c < nm; c++) {
        blocks[COL][c].index = c;
        blocks[COL][c].dimensionId = COL;
        blocks[COL][c].dimensionName = "column";
        for (int u = 1; u <= nm; u++) {
            blocks[COL][c].canBePosMask[u] = (1<<nm)-1;
        }
        for (int t = 0; t < nm; t++) {
            blocks[COL][c].it[t] = t;
            blocks[COL][c].jt[t] = c;
        }
    }
    // build quadrant blocks
    for(int q = 0; q < nm; q++) {
        blocks[ROW][q].index = q;
        blocks[QUA][q].dimensionId = QUA;
        blocks[QUA][q].dimensionName = "quadrant";
        for (int u = 1; u <= nm; u++) {
            blocks[QUA][q].canBePosMask[u] = (1<<nm)-1;
        }
        int bi = (q/n)*n, bj = (q%n)*m;
        for (int t = 0; t < nm; t++) {
            blocks[QUA][q].it[t] = bi + (t/m);
            blocks[QUA][q].jt[t] = bj + (t%m);
        }
    }
    // set blocksByPos
    for (int d = 0; d < 3; d++) {
        for (int bt = 0; bt < nm; bt++) {
            block *b = &blocks[d][bt];
            for (int t = 0; t < nm; t++) {
                int i = b->it[t], j = b->jt[t];
                blocksByPos[i][j][d] = b;
            }
        }
    }
    // set masksByBitCount
    memset(maskCountByBitCount, 0, sizeof maskCountByBitCount);
    for (int mask = 0; mask < (1<<nm); mask++) {
        int cnt = bitCount(mask);
        if (cnt >= MAX_MASK_COUNT) {
            continue;
        }
        if (maskCountByBitCount[cnt] == MAX_MASKS) {
            fatalf("Overflow while computing number of masks");
        }
        masksByBitCount[cnt][maskCountByBitCount[cnt]++] = mask;
    }

    debugf("Initialized solver variables.");
}

void restrictDiscoveries() {
    for (int i = 0; i < nm; i++) {
        for (int j = 0; j < nm; j++) {
            int u = sudoku[i][j];
            if (u == 0) {
                continue;
            }
            for (int canBeMaskIt = canBeMask[i][j]; canBeMaskIt; turnLastBitOff(canBeMaskIt)) {
                int v = lastBitPos(canBeMaskIt);
                if (v == u) {
                    continue;
                }
                cannotBe(i, j, v, fmt("discovered number %d in its place", u));
            }
            for (int d = 0; d < 3; d++) {
                block *b = blocksByPos[i][j][d];
                for (int posMaskIt = b->canBePosMask[u]; posMaskIt; turnLastBitOff(posMaskIt)) {
                    int t = lastBitPos(posMaskIt);
                    int ni = b->it[t], nj = b->jt[t];
                    if (ni == i && nj == j) {
                        continue;
                    }
                    cannotBe(ni, nj, u, fmt("discovered the number %d at the same %s at position (%d,%d)", u, b->dimensionName, i, j));
                }
            }
        }
    }
}

bool restrictedPointers[3][MAXN][3][MAXN];
void restrictPointer(block *b1, int d2, int u) {
    if (restrictedPointers[b1->dimensionId][b1->index][d2][u]) {
        return;
    }
    block *b2 = NULL;
    for (int posMaskIt = b1->canBePosMask[u]; posMaskIt; turnLastBitOff(posMaskIt)) {
        int t = lastBitPos(posMaskIt);
        int i = b1->it[t], j = b1->jt[t];
        block *cand = blocksByPos[i][j][d2];
        if (b2 == NULL || cand == b2) {
            b2 = cand;
        } else {
            return;
        }
    }
    if (b2 == NULL) {
        impossible = true;
        return;
    }
    debugf(fmt("At %s %d, number %d can only be at %s %d; removing possibilites for this %s in other %ss.", b1->dimensionName, b1->index, u, b2->dimensionName, b2->index, b2->dimensionName, b1->dimensionName));
    
    restrictedPointers[b1->dimensionId][b1->index][d2][u] = true;
    for (int posMaskIt = b2->canBePosMask[u]; posMaskIt; turnLastBitOff(posMaskIt)) {
        int t = lastBitPos(posMaskIt);
        int i = b2->it[t], j = b2->jt[t];
        if (blocksByPos[i][j][b1->dimensionId] == b1) {
            continue;
        }
        cannotBe(i, j, u, fmt("%s %d definitely has this number in this %s", b1->dimensionName, b1->index, b2->dimensionName));
    }
}

void restrictNaked(block *b, int posMask) {
    int valueMask = 0;
    for (int posMaskIt = posMask; posMaskIt; turnLastBitOff(posMaskIt)) {
        int t = lastBitPos(posMaskIt);
        int i = b->it[t], j = b->jt[t];
        valueMask |= canBeMask[i][j];
    }
    if (bitCount(posMask) != bitCount(valueMask)) {
        return;
    }
    const int *valueMaskList = maskToList(valueMask);
    const char *valueMaskBuf = prettyBufNumbers(valueMaskList, bitCount(valueMask));
    const int *posMaskList = maskToList(posMask);
    const char *posMaskBuf = prettyBufNumbers(posMaskList, bitCount(posMask));
    for (int posMaskIt = (((1<<nm)-1)^posMask); posMaskIt; turnLastBitOff(posMaskIt)) {
        int t = lastBitPos(posMaskIt);
        int i = b->it[t], j = b->jt[t];
        for (int valueMaskIt = valueMask; valueMaskIt; turnLastBitOff(valueMaskIt)) {
            int u = lastBitPos(valueMaskIt);
            cannotBe(i, j, u, fmt("naked combination along %s %d of numbers %s at indexes %s found at cell", b->dimensionName, b->index, valueMaskBuf, posMaskBuf));
        }
    }
}

void restrictHidden(block *b, int valueMask) {
    int posMask = 0;
    for (int valueMaskIt = valueMask; valueMaskIt; turnLastBitOff(valueMaskIt)) {
         int u = lastBitPos(valueMaskIt);
         posMask |= b->canBePosMask[u];
    }
    if (bitCount(posMask) != bitCount(valueMask)) {
        return;
    }
    const int *valueMaskList = maskToList(valueMask);
    const char *valueMaskBuf = prettyBufNumbers(valueMaskList, bitCount(valueMask));
    const int *posMaskList = maskToList(posMask);
    const char *posMaskBuf = prettyBufNumbers(posMaskList, bitCount(posMask));
    for (int posMaskIt = posMask; posMaskIt; turnLastBitOff(posMaskIt)) {
        int t = lastBitPos(posMaskIt);
        int i = b->it[t], j = b->jt[t];
        for (int valueMaskIt = ((((1<<nm)-1)<<1)^valueMask)&canBeMask[i][j]; valueMaskIt; turnLastBitOff(valueMaskIt)) {
            int u = lastBitPos(valueMaskIt);
            cannotBe(i, j, u, fmt("hidden combination along %s %d of numbers %s at indexes %s found at cell", b->dimensionName, b->index, valueMaskBuf, posMaskBuf));
        }
    }
}

void restrictXWing(int d, int u) {
    int btMask = 0;
    for (int b1t = 0; b1t < nm; b1t++) {
        block *b1 = &blocks[d][b1t];
        if (bitCount(b1->canBePosMask[u]) != 2) {
            continue;
        }
        for (int btMaskIt = btMask; btMaskIt; turnLastBitOff(btMaskIt)) {
            int b2t = lastBitPos(btMaskIt);
            block *b2 = &blocks[d][b2t];
            if (b1->canBePosMask[u] != b2->canBePosMask[u]) {
                continue;
            }
            const int *posMaskList = maskToList(b1->canBePosMask[u]);
            const char *posMaskBuf = prettyBufNumbers(posMaskList, bitCount(b1->canBePosMask[u]));
            for (int bt = 0; bt < nm; bt++) {
                if (bt == b1t || bt == b2t) {
                    continue;
                }
                block *b = &blocks[d][bt];
                for (int posMaskIt = (b1->canBePosMask[u])&(b->canBePosMask[u]); posMaskIt; turnLastBitOff(posMaskIt)) {
                    int t = lastBitPos(posMaskIt);
                    int i = b->it[t], j = b->jt[t];
                    cannotBe(i, j, u, fmt("X wing of number %d found in %ss %d and %d at indexes %s", u, b->dimensionName, b2t, b1t, posMaskBuf));
                }
            }
        }
        turnBitOn(btMask, b1t);
    }
}

void restrictAll() {
    restrictDiscoveries();
    for (int bt = 0; bt < nm; bt++) {
        for (int u = 1; u <= nm; u++) {
            restrictPointer(&blocks[ROW][bt], QUA, u);
            restrictPointer(&blocks[COL][bt], QUA, u);
            restrictPointer(&blocks[QUA][bt], ROW, u);
            restrictPointer(&blocks[QUA][bt], COL, u);
        }
    }
    if (restricted || impossible) {
        return;
    }
    for (int cnt = 2; cnt < 4; cnt++) {
        for (int maskt = 0; maskt < maskCountByBitCount[cnt]; maskt++) {
            int mask = masksByBitCount[cnt][maskt];
            for (int d = 0; d < 3; d++) {
                for (int t = 0; t < nm; t++) {
                    if (restrictNaked(&blocks[d][t], mask), restricted || impossible) {
                        return;
                    }
                    if (restrictHidden(&blocks[d][t], mask<<1), restricted || impossible) {
                        return;
                    }
                }
            }
        }
    }
    for (int u = 1; u <= nm; u++) {
        if (restrictXWing(ROW, u), restricted || impossible) {
            return;
        }
        if (restrictXWing(COL, u), restricted || impossible) {
            return;
        }
    }
    for (int maskt = 0; maskt < maskCountByBitCount[4]; maskt++) {
        int mask = masksByBitCount[4][maskt];
        for (int d = 0; d < 3; d++) {
            for (int t = 0; t < nm; t++) {
                if (restrictNaked(&blocks[d][t], mask), restricted || impossible) {
                    return;
                }
                if (restrictHidden(&blocks[d][t], mask<<1), restricted || impossible) {
                    return;
                }
            }
        }
    }
}

void searchBestGuess(int *ri, int *rj, int *ru, char *reason) {
    int minPossibilities = nm+1;
    debugf(fmt("Searching for best guess. discoveries: %d.", discoveries));
    for (int i = 0; i < nm && minPossibilities > 2; i++) {
        for (int j = 0; j < nm && minPossibilities > 2; j++) {
            if (sudoku[i][j] != 0) {
                continue;
            }
            int possibilities = canBeCount(i, j);
            int u = canBeLast(i, j);
            if (minPossibilities > possibilities) {
                minPossibilities = possibilities;
                *ri = i;
                *rj = j;
                *ru = u;
                strcpy(reason, fmt("%d possibilities at cell; discoveries: %d", possibilities, discoveries+1));
                debugf(fmt("Candidate %d at (%d,%d); %d possibilities at %s.", u, i, j, possibilities, "cell"));
            }
        }
    }
    for (int d = 0; d < 3 && minPossibilities > 2; d++) {
        for (int bt = 0; bt < nm && minPossibilities > 2; bt++) {
            block *b = &blocks[d][bt];
            for (int u = 1; u <= nm && minPossibilities > 2; u++) {
                int t = lastBitPos(b->canBePosMask[u]);
                int i = b->it[t], j = b->jt[t];
                if (sudoku[i][j] != 0) {
                    continue;
                }
                int possibilities = bitCount(b->canBePosMask[u]);
                if (minPossibilities > possibilities) {
                    minPossibilities = possibilities;
                    *ri = i;
                    *rj = j;
                    *ru = u;
                    strcpy(reason, fmt("%d possibilities at %s %d; discoveries: %d", possibilities, b->dimensionName, b->index, discoveries+1));
                    debugf(fmt("Candidate %d at (%d,%d); %d possibilities at %s.", u, i, j, possibilities, b->dimensionName));
                }
            }
        }
    }
    if (minPossibilities == 1) {
        fatalf("Attempted guess when there is a single opportunity forward.");
    }
    if (minPossibilities == nm+1) {
        fatalf("Attempted guess when Sudoku is already full.");
    }
    debugf(fmt("Guessing %d at (%d,%d); %d possibilities; %d discoveries.", *ru, *ri, *rj, minPossibilities, discoveries));
}

bool solve() {
    // reset pointer restriction cache
    memset(restrictedPointers, false, sizeof restrictedPointers);

    do {
        restricted = false;
        restrictAll();
    } while(restricted && !impossible && !done);

    if (impossible) {
        return false;
    }
    if (done || noGuessing) {
        return true;
    }

    int ri, rj, ru;
    char reason[109];
    searchBestGuess(&ri, &rj, &ru, reason);
    guesses++;
    
    // save state in case we need to rollback
    int tmpEventCount = eventCount;
    discover(ri, rj, ru, fmt("guess with reason: %s", reason));
    if (solve()) {
        return true;
    }

    // guess failed, rollback and try the opposite guess
    rollbackEvents(tmpEventCount);
    impossible = false;
    cannotBe(ri, rj, ru, fmt("failed guess with reason: %s", reason));
    if (solve()) {
        return true;
    }

    // if it can and cannot be, we failed an upstream guess
    return false;
}

bool validate() {
    for (int i = 0; i < nm; i++) {
        for (int j = 0; j < nm; j++) {
            if (sudoku[i][j] == 0) {
                return false;
            }
            for (int d = 0; d < 3; d++) {
                block *b = blocksByPos[i][j][d];
                for (int t = 0; t < nm; t++) {
                    int ni = b->it[t], nj = b->jt[t];
                    if (ni == i && nj == j) {
                        continue;
                    }
                    if (sudoku[i][j] == sudoku[ni][nj]) {
                        return false;
                    }
                }
            }
        }
    }
    return true;
}

bool read() {
    if (feof(inputFile)) {
        return false;
    }
    if (fscanf(inputFile, "%d %d ", &n, &m) == EOF) {
        return false;
    }
    nm = n * m;
    if (n >= MAXN || m >= MAXN || nm >= MAXN) {
        fatalf(fmt("n, m and n*m cannot be over %d", MAXN-1));
    }
    infof(fmt("Read input header; n = %d and m = %d", n, m));

    initialDiscoveries = 0;
    for (int i = 0; i < nm; i++) {
        for (int j = 0; j < nm; j++) {
            fscanf(inputFile, " %d ", &sudoku[i][j]);
            if (sudoku[i][j] != 0) {
                initialDiscoveries++;
            }
        }
    }
    infof(fmt("Read input with sudoku:\n%s", prettyBufSudoku(sudoku, nm)));
    return true;
}

bool write() {
    const char *out = prettyBufSudoku(sudoku, nm);
    fprintf(outputFile, "%d %d\n%s", n, m, out);
    infof(fmt("Wrote output with sudoku:\n%s", out));
    return true;
}

void processArgs(int argc, char *argv[]) {
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            help = true;
        } else if (strcmp(argv[i], "--debug") == 0 || strcmp(argv[i], "-d") == 0) {
            debug = verbose = true;
        } else if (strcmp(argv[i], "--verbose") == 0 || strcmp(argv[i], "-v") == 0) {
            verbose = true;
        } else if (strcmp(argv[i], "--instructions") == 0 || strcmp(argv[i], "-s") == 0) {
            instructions = true;
        } else if (strcmp(argv[i], "--no-guessing") == 0 || strcmp(argv[i], "-g") == 0) {
            noGuessing = true;
        } else if (strcmp(argv[i], "--input") == 0 || strcmp(argv[i], "-i") == 0) {
            i++;
            inputFile = fopen(argv[i], "r");
        } else if (strcmp(argv[i], "--output") == 0 || strcmp(argv[i], "-o") == 0) {
            i++;
            outputFile = fopen(argv[i], "w");
        } else if (strcmp(argv[i], "--instructions-output") == 0 || strcmp(argv[i], "-O") == 0) {
            i++;
            instructionFile = fopen(argv[i], "w");
        } else {
            printf("Unknown flag %s.", argv[i]);
            exit(1);
        }
    }

    if (instructionFile == NULL) {
        instructionFile = outputFile;
    }

    char argsBuf[1009];
    for (int i = 0, argsBufEnd = 0; i < argc; i++) {
        sprintf(argsBuf + argsBufEnd, "%s ", argv[i]);
        argsBufEnd += strlen(argv[i]);
    }
    debugf(fmt("Processed %d args: %s.", argc, argsBuf));
}

void printHelpMessage() {
    printf("This CLI solves Sudoku puzzles of sizes with n*m <= %d.\n\n", MAXN-1);
    printf("usage: [--input $PATH] [--output $PATH] [--instructions-output $PATH] [--debug] [--instructions] [--verbose]\n\n");
    printf("Flags:\n");
    printf("--help/-h               Prints the help message.\n");
    printf("--debug/-d              Enables DEBUG logging.\n");
    printf("--verbose/-v            Enables INFO logging.\n");
    printf("--instructions/-s       When set, prints instructions on how to solve.\n");
    printf("--no-guessing/-g        When set, makes as much progress as possible without making a guess.\n");
    printf("--input/-i              Sets the input file to read puzzles from. Defaults to stdin.\n");
    printf("--output/-o             Sets the output file to write solutions to. Defaults to stdout.\n");
    printf("--instruction-output/-O Sets the output file to write instructions to. Defaults to the output file.\n");
}

void printInstructions(int caseNum) {
    fprintf(instructionFile, "Instructions for case number %d:\n", caseNum);
    for (int i = 0; i < eventCount; i++) {
        event e = events[i];
        if (e.type == DISCOVER) {
            fprintf(instructionFile, "%d: Discovered number %d at position (%d,%d); reason: %s.\n", i+1, e.u, e.i, e.j, e.reason);
        } else if (e.type == CANNOT_BE) {
            int cnt = canBeCount(e.i, e.j);
            const int *canBeList = maskToList(canBeMask[e.i][e.j]);
            fprintf(instructionFile, "%d: Number %d cannot be at (%d,%d); reason: %s; possiblities left: %s.\n", i+1, e.u, e.i, e.j, e.reason, prettyBufNumbers(canBeList, cnt));
        } else {
            fatalf(fmt("Found event of unknown type %d.", e.type));
        }
    }
}

int main(int argc, char *argv[]) {
    inputFile = stdin;
    outputFile = stdout;
    startTime = clock();
    processArgs(argc, argv);

    if (help) {
        printHelpMessage();
        return 0;
    }

    for(int caseNum = 1; read(); caseNum++) {
        init();
        infof(fmt("Solving case num %d...", caseNum));
        if (!solve()) {
            infof(fmt("Could not solve Sudoku case %d.", caseNum));
            continue;
        }
        if (!validate()) {
            infof(fmt("Sudoku case %d failed validation.", caseNum));
            continue;
        }
        if (instructions) {
            printInstructions(caseNum);
        }
        infof(fmt("Case num %d solved. Steps: %d Guesses: %d.", caseNum, steps, guesses));
        write();
    }

    cleanUp();
    return 0;
}