/*
 * Omar Rifki 
 *   Code modified from an initial code of Christine Solnon.
 *   It solves the TSPTW with two objective functions:
 *   Makespan and travel times.
 *
 * To compile: gcc -o prog -O3 TSPTW-DP.c
 *
 * To execute: ./prog < n40w60.002.txt
 *
 */

#include <limits.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define HASHSIZE 992451653

typedef unsigned __int128 set;

set un = 1;
int nbVertices;  // Number of vertices: must be smaller than or equal to 128
int** cost;      // cost[i][j] = cost of (i,j)
int* ew;         // earliest time window of vertex i
int* lw;         // latest time window of vertex i
int* service;    // service[i] = service time of visiting i

//
// library of binary sets
//

bool isElementOf(int e, set s) {
    if ((s & (un << (e - 1))) != 0) return true;
    return false;
}

bool isEmpty(set s) { return (s == 0); }

set removeElement(set s, int e) {
    return (s ^ (un << (e - 1)));
}

set addElement(set s, int e) {
    return (s | (un << (e - 1)));
}

set createset(int nbVertices) {
    return (un << (nbVertices - 1)) - un;
}

void printSet(set s) {
    int i = 1;
    while (s != 0) {
        if (s % 2 != 0) printf(" %d", i);
        s /= 2;
        i++;
    }
}

//
//  data
//

void readData() {
    int ret = scanf("%d", &nbVertices);

    cost = (int**)malloc(nbVertices * sizeof(int**));
    for (int i = 0; i < nbVertices; i++) {
        cost[i] = (int*)malloc(nbVertices * sizeof(int*));
        for (int j = 0; j < nbVertices; j++)
            ret = scanf("%d", &(cost[i][j]));
    }

    service = (int*)malloc(nbVertices * sizeof(int*));
    for (int i = 0; i < nbVertices; i++)
        service[i] = 0;

    ew = (int*)malloc(nbVertices * sizeof(int));
    lw = (int*)malloc(nbVertices * sizeof(int));
    for (int i = 0; i < nbVertices; i++)
        ret = scanf("%d %d", &(ew[i]), &(lw[i]));
}

int travelTime(int i, int j) {
    return cost[i][j];
}

//
//  hash table
//

typedef struct context_htable {  // hash table context
    int sizeH;                   // hash table size
    char* memi;                  // state (i) - last visited point
    int* memt;                   // state (t) - arrive time at i
    set* mems;                   // state (s) - visited vertices before i
    int* memd;                   // smallest traveltime of (i,t,s) state
    int* memp;                   // last parent of (i,t,s) state
    int* mempt;                  // arrival time of last parent of (i,t,s)
    long nbStates;               // number of states
    long nbCollisions;           // number of collisions
} context_htable;

int hash(int i, set s, int nbVertices, int sizeH) {
    long long int h = (i + (s - 1) * nbVertices) % sizeH;
    if (h < 0) return (-h);
    return h;
}

int hash2d(int i, int t, set s, int nbVertices, int sizeH) {
    long long int h = (i + t + (s - 1) * (t + 1) * nbVertices) % sizeH;
    if (h < 0) return (-h);
    return h;
}

void initHash(context_htable* ctx) {
    ctx->sizeH = HASHSIZE;
    ctx->nbStates = 0;
    ctx->nbCollisions = 0;
    ctx->memi = (char*)malloc(ctx->sizeH * sizeof(char));
    ctx->memt = (int*)malloc(ctx->sizeH * sizeof(int));
    ctx->mems = (set*)malloc(ctx->sizeH * sizeof(set));
    ctx->memd = (int*)malloc(ctx->sizeH * sizeof(int));
    ctx->memp = (int*)malloc(ctx->sizeH * sizeof(int));
    ctx->mempt = (int*)malloc(ctx->sizeH * sizeof(int));

    memset(ctx->memi, 0, ctx->sizeH);
    memset(ctx->memt, 0, ctx->sizeH);
    memset(ctx->mems, 0, ctx->sizeH * sizeof(set));
}

void freeMemory(context_htable* ctx) {
    free(ctx->memi);
    free(ctx->memt);
    free(ctx->mems);
    free(ctx->memd);
    free(ctx->memp);
    free(ctx->mempt);

    free(ew);
    free(lw);
    free(service);
    for (int i = 0; i < nbVertices; i++)
        free(cost[i]);
    free(cost);
}

//
// dynamic programming 
//

int computeD_travelTime(int i, int t, set s, context_htable* ctx) {
    int start, end;
    if (s == 0) {  // base case
        start = ew[0] + service[0] + travelTime(0, i);
        end = lw[i];
        if (t >= start && t <= end)
            return travelTime(0, i);
        return INT_MAX;
    }

    if (t < 0 || t > lw[i])
        return INT_MAX;  // arrive at i after the end of the time window

    // search for (i,t,s) in the hash table
    int h = hash2d(i, t, s, nbVertices, ctx->sizeH);
    int nb = 0;
    while (ctx->memi[h] > 0 && (ctx->memi[h] != i || ctx->memt[h] != t || ctx->mems[h] != s)) {
        h++;
        if (h == ctx->sizeH) h = 0;
        nb++;
        if (nb > ctx->sizeH) {
            printf("Hash table is full -> increase sizeH\n");
            exit(0);
        }
    }
    ctx->nbCollisions += nb;
    if (ctx->memi[h] == i && ctx->memt[h] == t && ctx->mems[h] == s)  // direct call
        return ctx->memd[h];

    // state (i,t,s) not filled in the hash table => compute dp
    int j, k, tj, nbCand = 0;
    int cand[nbVertices];
    for (j = 1; j < nbVertices; j++) {
        if (isElementOf(j, s)) {
            cand[nbCand++] = j;
            start = ew[j] + service[j] + travelTime(j, i);
            end = lw[i];
            if (start > end) return INT_MAX;  // it is not possible to serve j before i
        }
    }

    ctx->memi[h] = i;
    ctx->memt[h] = t;
    ctx->mems[h] = s;
    ctx->memd[h] = INT_MAX;
    ctx->memp[h] = INT_MAX;
    ctx->mempt[h] = INT_MAX;
    ctx->nbStates++;
    for (k = 0; k < nbCand; k++) {
        j = cand[k];  // case where j is visited just before i
        start = ew[j];
        end = t - travelTime(j, i) - service[j];
        for (tj = start; tj <= end; tj++) {
            int d = computeD_travelTime(j, tj, removeElement(s, j), ctx);
            if (d < INT_MAX) {
                d += travelTime(j, i);
                if (d < ctx->memd[h]) {
                    ctx->memd[h] = d;
                    ctx->memp[h] = j;
                    ctx->mempt[h] = tj;
                }
            }
        }
    }
    return ctx->memd[h];
}

int computeD_makespan(int i, set s, context_htable* ctx) {
    if (s == 0) return ew[0] + service[0] + travelTime(0, i);
    // search for (i,s) in the hash table
    int h = hash(i, s, nbVertices, ctx->sizeH);
    int nb = 0;
    while (ctx->memi[h] > 0 && (ctx->memi[h] != i || ctx->mems[h] != s)) {
        h++;
        if (h == ctx->sizeH) h = 0;
        nb++;
        if (nb > ctx->sizeH) {
            printf("Hash table is full -> increase sizeH\n");
            exit(0);
        }
    }
    ctx->nbCollisions += nb;
    if (ctx->memi[h] == i && ctx->mems[h] == s) return ctx->memt[h];
    // (i,s) isn't in the hash table -> compute the earliest arrival time
    int nbCand = 0;
    int cand[nbVertices];
    for (int j = 1; j < nbVertices; j++) {
        if (isElementOf(j, s)) {
            cand[nbCand++] = j;
            if (ew[j] > lw[i])
                return INT_MAX;  // it is not possible to serve j before i
        }
    }
    ctx->memi[h] = i;
    ctx->mems[h] = s;
    ctx->memt[h] = INT_MAX;
    ctx->nbStates++;
    for (int k = 0; k < nbCand; k++) {
        int j = cand[k];  // Case where j is visited just before i
        int t = computeD_makespan(j, removeElement(s, j),
                                  ctx);  // t=min travel time 0 -> j
        if (t < INT_MAX) {
            t += service[j] + travelTime(j, i);
            int start = ew[i];
            int end = lw[i];
            if (t < start) t = start;  // wait for the beginning of the time window
            if (t > end)
                t = INT_MAX;  // after the end of the time window
            if (t < ctx->memt[h]) {
                ctx->memt[h] = t;
                ctx->memp[h] = j;
            }
        }
    }
    return ctx->memt[h];
}

int* getSolution(int lastParent, int arrivetime, bool isMakespan, context_htable* ctx) {
    int* solution = (int*)malloc((nbVertices + 1) * sizeof(int));
    int h = 0, count = 0;
    int t = arrivetime - service[lastParent] - travelTime(lastParent, 0);
    solution[nbVertices - count++] = 0;
    solution[nbVertices - count++] = lastParent;
    set s = createset(nbVertices);
    while (!isEmpty(s)) {
        s = removeElement(s, lastParent);
        if (isMakespan) {
            h = hash(lastParent, s, nbVertices, ctx->sizeH);
            while (ctx->memi[h] > 0 &&
                   (ctx->memi[h] != lastParent || ctx->mems[h] != s)) {
                h++;
                if (h == ctx->sizeH) h = 0;
            }
            if (ctx->memi[h] == lastParent && ctx->mems[h] == s) {
                lastParent = ctx->memp[h];
                solution[nbVertices - count++] = lastParent;
            }
        } else {  // traveltime
            h = hash2d(lastParent, t, s, nbVertices, ctx->sizeH);
            while (ctx->memi[h] > 0 &&
                   (ctx->memi[h] != lastParent || ctx->memt[h] != t || ctx->mems[h] != s)) {
                h++;
                if (h == ctx->sizeH) h = 0;
            }
            if (ctx->memi[h] == lastParent && ctx->memt[h] == t && ctx->mems[h] == s) {
                int after = lastParent;
                lastParent = ctx->memp[h];
                t = ctx->mempt[h];
                solution[nbVertices - count++] = lastParent;
            }
        }
    }
    solution[0] = 0;
    return solution;
}

void printSolution(int* solution) {
    printf("Solution = ");
    for (int i = 0; i < nbVertices; i++)
        printf("%d ", solution[i]);
    printf("%d end\n", solution[0]);
}

int getTravelTime(int* solution) {
    int i, dmin = 0, current, next;
    for (i = 0; i < nbVertices; i++) {
        current = solution[i];
        next = solution[i + 1];
        dmin += travelTime(current, next);
    }
    return dmin;
}

int main(int argc, char** argv) {
    readData();
    bool isMakespan = 0; //= 1 for travel times obj
    context_htable ctx;
    initHash(&ctx);

    // DP start
    bool feas = false;
    int tmin = INT_MAX;
    int dmin = INT_MAX;
    int lastParent, j, tj, start, end, t, d;
    set s = createset(nbVertices);

    clock_t startTime = clock();
    for (j = 1; j < nbVertices; j++) {
        if (isMakespan) {
            t = computeD_makespan(j, removeElement(s, j), &ctx);
            if (t < INT_MAX) {
                t += service[j] + travelTime(j, 0);
                if (t < tmin) {
                    feas = true;
                    tmin = t;
                    lastParent = j;
                }
            }
        } else { // traveltime
            start = ew[0] + service[0] + travelTime(0, j);
            end = lw[j];
            for (tj = start; tj <= end; tj++) {
                d = computeD_travelTime(j, tj, removeElement(s, j), &ctx);
                if (d < INT_MAX) {
                    d += travelTime(j, 0);
                    t = tj + service[j] + travelTime(j, 0);
                    if (d < dmin && t <= lw[0]) {
                        feas = true;
                        dmin = d;
                        tmin = t;
                        lastParent = j;
                    }
                }
            }
        }
    }
    double cpu = ((double)(clock() - startTime)) / CLOCKS_PER_SEC;
    //  DP end

    if (feas) {  // found a solution
        int* solution = getSolution(lastParent, tmin, isMakespan, &ctx);
        if (isMakespan) {
            d = getTravelTime(solution);
            printSolution(solution);
            printf(
                "Best makespan = %d; travel time = %d; CPU time = %.3fs; Number of states = %ld; Number of collisions = %ld\n",
                tmin, d, cpu, ctx.nbStates, ctx.nbCollisions);
        } else {  // traveltime
            printSolution(solution);
            printf(
                "Best travel time = %d; makespan = %d; cpu time = %.3fs; Number of states = %ld; Number of collisions = %ld\n",
                dmin, tmin, cpu, ctx.nbStates, ctx.nbCollisions);
        }
        free(solution);
    } else
        printf("No feasible solution; cpu time = %.3fs\n; Number of states = %ld; Number of collisions = %ld\n",
               cpu, ctx.nbStates, ctx.nbCollisions);

    freeMemory(&ctx);
    return 0;
}
