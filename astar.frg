#lang forge/temporal 
open "gridworld.frg"

option run_sterling "astar.cnd" 

/*
  Modeling A* search. 
  While this model is somewhat generic, the main application is expected to be gridworlds. 

  This is not intended to model any specific *IMPLEMENTATION* of A*. Rather, we are modeling
  the algorithm in the abstract, to help us explore its invariants etc.

  There are a lot of potential variants of this algorithm, some buggy and some not. When
  I was learning the algorithm, it wasn't immediately clear to me _why_ we use, say,
  the heuristic in one place and not in others. So let's use this model to explore.

  Note that the helper function "heuristic" can be used to adjust the heuristic in A*.
  This lets us swap easily between the taxicab-distance defined in gridworld.frg and 
  the 0-heuristic of Dijkstra's algorithm.

  MODELING NOTE: we could likely make this more efficient in at least 2 ways.
    (1) Make start and end one sigs, so that a specific atom will be allocated.
    (2) Use a partial instance to limit available weights and locations. 

  FOR ALLOY USERS: Forge has some features Alloy doesn't, but it also elides some Alloy 
  features. For example, here are 3 differences:
    - There are no `fact`s in Forge; you must be explicit in each `run`.
    - Field definition types must be products of sigs. Moreover, Forge doesn't include 
      the `A -> one B` type syntax, instead we use `pfunc` and `func` annotations.
    - Options are set explicitly in each file. 

*/

---------------------------------------------------------------------
-- Data Definitions
---------------------------------------------------------------------

/** State of the search */
one sig AStar {
    start: one Room,
    goal: one Room,

    /** The shortest-path tree we're building */
    var tree: set Room -> Room,
    /** The best actual path cost to reach each room we've found so far. No entry ~= +Inf. */
    var realCost: pfunc Room -> Int,
    /** The best estimate we have for the cost to reach a room so far. No entry ~= +Inf. */
    var estimatedCost: pfunc Room -> Int,
    /** The rooms we have a explored and thus have an upper-bound on cost for, 
        but have not yet explored past. This is sometimes called the "open set". */
    var frontier: set Room,
    /** The rooms we have actually finalized costs for. 
        This is sometimes called the "closed set". */
    var finalized: set Room
}

fun heuristic[r1, r2: Room]: one Int {
    // Change this to 0 to get Dijkstra's-algorithm behavior. 
    distance[r1, r2]
}

---------------------------------------------------------------------
-- Transition System
---------------------------------------------------------------------

/** Initial state for A* search */
pred init {
    no tree
    AStar.frontier = AStar.start
    no AStar.finalized 
    AStar.realCost = AStar.start -> 0
    // heuristic[AStar.start,AStar.start] should be 0 in this setting.
    AStar.estimatedCost = AStar.start -> heuristic[AStar.start, AStar.start]
}

/** A useful debugging technique. Which transition (or sub-transition) is happening?
  You can also make the monitor more fine-grained, as here: which sub-transition is 
  applying to each room? Good for finding uncovered cases, e.g., if the value is 
  not in the set of labels. E.g., I have 0, 1, 2, and 3 below. If the value 7 appeared,
  it would mean that some room isn't being properly constrained. 
  (Beware: as written, we know that *if* a specific constraint block applies, we will
   see the expected value. But the converse is not necessarily true. Even without
   refactoring, however, a non-expected value indicates a problem. */
one sig Monitor {
    /** 
      0: the frontier node about to be finalized;
      1: a neighbor that we have improved the estimate for;
      2: a neighbor that we have not improved the estimated for;
      3: some other room */
    var kind: func Room -> Int
}

/** A step of A* search. 
    TODO: expand this into helpers! */
pred step {
    // GUARD
    some AStar.frontier
    AStar.goal not in AStar.finalized

    // ACTION
    // Find a frontier room with minimal estimated cost. This is the node we will finalize.
    let cheapestFrontierCost = min[AStar.realCost[AStar.frontier]] |
    let cheapestFrontierRooms = AStar.realCost.cheapestFrontierCost & AStar.frontier | 
    some expandAt: cheapestFrontierRooms | {
        // Finalize the real cost for this room and then explore its neighbors.
        AStar.finalized' = AStar.finalized + expandAt
        Monitor.kind[expandAt] = 0 // DEBUG TRACE

        // Assume: no self-loops. Identify the neighbors that aren't yet finalized.
        let neighbors = expandAt.doors.Int - AStar.finalized | {
            // The new frontier will be expanded if we haven't discovered any neighbors yet.
            AStar.frontier' = AStar.frontier - expandAt + neighbors

            // For each, can we do better than the current guess via expandAt? 
            all neighbor: neighbors | { 
                // "good" version
                let new_cost = add[AStar.realCost[expandAt], expandAt.doors[neighbor]] | {
                // "buggy" version
                //let new_cost = add[AStar.estimatedCost[expandAt], expandAt.doors[neighbor]] | {
                    
                    ((no AStar.realCost[neighbor] or AStar.realCost[neighbor] > new_cost) => {
                         AStar.realCost'[neighbor] = new_cost and
                         AStar.estimatedCost'[neighbor] = add[new_cost, heuristic[neighbor, AStar.goal]] and
                         AStar.tree'[neighbor] = expandAt and
                         Monitor.kind[neighbor] = 1 // DEBUG TRACE
                    } else {
                        AStar.realCost'[neighbor] = AStar.realCost[neighbor] and
                        AStar.estimatedCost'[neighbor] = AStar.estimatedCost[neighbor] and
                        AStar.tree'[neighbor] = AStar.tree[neighbor] and
                        Monitor.kind[neighbor] = 2 // DEBUG TRACE
                    })

                }
            } // end all neighbors
            
            // FRAME: Unaffected rooms same values. This includes non-neighbors,
            // but also all finalized (in the pre-state) rooms, including expandAt.
            all r: Room - neighbors | {
                AStar.realCost'[r] = AStar.realCost[r]
                AStar.estimatedCost'[r] = AStar.estimatedCost[r]
                AStar.tree'[r] = AStar.tree[r]
                (r != expandAt) => Monitor.kind[r] = 3 // DEBUG TRACE
            }
        }
    }
}

/** A* is done. We've either found the goal or nothing remains to explore. */
pred haltEnabled {
    (no AStar.frontier) or (AStar.goal in AStar.finalized)
}
pred halt {
    // GUARD
    haltEnabled
    // ACTION
    tree' = tree
    frontier' = frontier
    finalized' = finalized
    realCost' = realCost 
    estimatedCost' = estimatedCost
}

---------------------------------------------------------------------
-- System traces
---------------------------------------------------------------------

pred astarTrace {
    init 
    always {step or halt}
}

// Forge doesn't use "Time" in scopes like Alloy 6 does. Instead, we set an option.
option max_tracelength 12

/** An example run of A* on a non-trivial gridworld. */
astar_on_gridworld_6rooms_nontrivial: run {
    allConnected
    gridworld
    allEdgesGTZero
    astarTrace
    AStar.start != AStar.goal
    not noUndirectedCycle // I want to see examples that aren't linear.
} for exactly 6 Room

/** Extract the set of edges used in the shortest-path tree from start to goal. */
fun usedEdges: set Room -> Room {
    {r1, r2: Room | r1->r2 in AStar.tree and 
                    AStar.start not in AStar.goal.^(AStar.tree - r1->r2)}}
