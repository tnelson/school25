#lang forge/temporal 
open "gridworld.frg"
open "astar.frg"
option run_sterling "astar.optimality.cnd"

/*
  This module contains a demo of a bug I introduced when I originally wrote it. 
  Read with that in mind! The ordering in the module isn't chronological.

  The idea is: we want to show that once the system starts running `halt` transitions, 
    realCost[goal] is optimal among valid paths. Because the trace gives us a means of 
    referring to the A*-produced cost directly, we can ask Forge for a counterexample 
    without needing higher-order universal quantification. But this is easier
    to do in a separate module.

  Overflow presents a challenge. It's possible that the optimal path length would not 
  overflow, but the candidate cheaper path length would, and thus _appear_ to be cheaper. 
  Since overflow protection introduces new problems for the transition system, we'll 
  have to deal with this manually. I chose to accumulate length-so-far for every node 
  in both paths, and detect if for some hop n1 -> n2, the increase in length-so-far <0.

  Note on expanding this:

  We could use the same technique to check optimality for the entire shortest-path
  /tree/, because a counterexample is still a single path from the start to some room. 
*/

option max_tracelength 8

one sig Helper {
    /** The candidate alternative path to be found */
    cheaper: set Room -> Room -> Int,
    
    /** Simulated "loop" to help detect overflow in path weights. 
        The`sumCheaper` function will total all edges, without regard to overflow.
        But by defining the sum of edges _up to a room_, we can detect a point where 
        the sum-so-far is _reduced_. This is only safe if edge weights are non-negative. 
        
    For the candidate: */
    ofTotalC: pfunc Room -> Int,
    /** For the A* result: */
    ofTotalA: pfunc Room -> Int
}

fun cheapEdges: set Room -> Room { Helper.cheaper.Int }

/** This version is wrong! It leads to an apparent verification success. */
pred cheaper_wellformed_orig {
    // Subset of the graph edges
    Helper.cheaper in doors 
    // An acyclic set (and thus also undirected)
    no r: Room | r in r.^cheapEdges
    // Start from start
    one (cheapEdges).Room // unique start
    AStar.start not in (cheapEdges[Room]) // not RHS
    AStar.start in (cheapEdges).Room  // yes LHS
    // End at end
    one (cheapEdges[Room]) // unique end
    AStar.goal in (cheapEdges[Room]) // yes RHS
    AStar.goal not in (cheapEdges).Room  // not LHS
    // Linear between rooms on the path
    all r: Room | lone r.cheapEdges and lone cheapEdges.r
}

/** This version is fixed. It reveals a problem: overflow! */
pred cheaper_wellformed_fixed {
    // Subset of the graph edges
    Helper.cheaper in doors 
    // Start at Start
    one AStar.start.cheapEdges
    no AStar.start.~cheapEdges
    // End at Goal
    no AStar.goal.cheapEdges 
    one AStar.goal.~cheapEdges
    // Connected linear: (domain+codomain) reachable from start.
    AStar.start.*cheapEdges = (cheapEdges[Room] + cheapEdges.Room)
    // No double-successors
    all r: cheapEdges.Room | lone r.cheapEdges
    // No cycles in candidate (not even symmetric edges), since it's an alternate path
} 

/** Predicate describing that the cost-so-far totals for nodes are well-formed. */
pred wellformed_ofTotals {
    // Prefix weight for candidate
    Helper.ofTotalC[AStar.start] = 0
    all r: cheapEdges[Room] | {
        Helper.ofTotalC[r] = add[Helper.ofTotalC[r.~cheapEdges], r.~cheapEdges.doors[r]]
    }
    all r: Room-(cheapEdges[Room] + AStar.start) | no Helper.ofTotalC[r]

    // Prefix weight for generated A* path
    Helper.ofTotalA[AStar.start] = 0
    all r: usedEdges[Room] | {
        Helper.ofTotalC[r] = add[Helper.ofTotalC[r.~usedEdges], r.~usedEdges.doors[r]]
    }
    all r: Room-(usedEdges[Room] + AStar.start) | no Helper.ofTotalA[r]
}

/** Every prefix in the candidate path has weight <= its extension. */
pred no_pathlength_overflow {
    wellformed_ofTotals
    all r: cheapEdges[Room] | Helper.ofTotalC[r] >= Helper.ofTotalC[r.~cheapEdges]
    all r: usedEdges[Room]  | Helper.ofTotalA[r] >= Helper.ofTotalA[r.~usedEdges]
}

/** Sum up all edges in the candidate cheaper path. */
fun sumCheaper: one Int {
    sum r: cheapEdges.Room | (Helper.cheaper[r])[Room]
}

REQ_optimal_CE: assert {
    undirectedGraph
    allEdgesGTZero
    astarTrace
    AStar.goal in AStar.start.^(doors.Int) // will succeed
    eventually {
        halt
        cheaper_wellformed_fixed
        // Total of edge weights in cheaper is lower than what the A* model found.
        // NOTE: I'm a little bit worried here about overflow... And I was right to be.
        // But when I originally checked this, I used the `cheaper_wellformed_orig` version.
        sumCheaper < AStar.realCost[AStar.goal]

        no_pathlength_overflow
    }
} is unsat for 6 Room

/* Because I'm worried about overflow, I want to poke at the above check a little bit. 
   The main scenario I worry about is: an alternative path ending up negative because
   of overflow, when the "real" best path is positive. Wouldn't that be satisfiable?    

   Even more basically, we really should check that the wellformedness predicate isn't 
   unsatisfiable! Let's try looking for alternative paths that aren't one-hop.
*/

/** Regression test: wellformed predicate should allow paths of length > 1*/
wellformed_non_immediate: assert {
    cheaper_wellformed_fixed
    wellformed_ofTotals
    // Actual reachability in >1 step
    AStar.goal not in AStar.start.(doors.Int) 
    AStar.goal in AStar.start.^(doors.Int)
    #Helper.cheaper > 1
} is sat for exactly 4 Room


/**
   Now let's be concrete. 4 rooms. Start: A. Goal: D. 

   A -1- B
   |     |
   2     1
   |     |
   C -3- D 

   The optimal path is A->B->D for cost 2. 
   Bitwidth default (3) gives us the interval [-4, 3] inclusive. 
   A->C->D is a candidate, and has cost 5, which overflows to -3. 

   Can this specific example be instantiated? For efficiency, we'll use 
   partial-instance example syntax.
*/

example_4rooms_overflow: assert {
    undirectedGraph
    gridworld
    allConnected
    allEdgesGTZero -- technically given in bounds below, but just in case
    astarTrace
    cheaper_wellformed_fixed

    eventually {
        // Confirm overflow is as expected
        halt
        some d: Room | AStar.realCost[d] = 2 // expected path length
        sumCheaper < 2

    }
} is sat for { 
    #Int = 3 // [-4, 3], hence overflow
    Room = `A + `B + `C + `D
    AStar = `AStar0
    `A.doors = `B -> 1 + `C -> 2
    `B.doors = `A -> 1 + `D -> 1
    `C.doors = `A -> 2 + `D -> 3
    `D.doors = `C -> 3 + `B -> 1
    `AStar0.start = `A
    `AStar0.goal = `D
}
