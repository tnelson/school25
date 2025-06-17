#lang forge/temporal 
open "gridworld.frg"
open "astar.frg"
//option run_sterling off

option max_tracelength 8

/*
At end, realCost[goal] is "optimal". Because the trace gives us a means of 
    referring to the A*-produced cost, we can ask Forge for a counterexample 
    without needing higher-order universal quantification. But this is easier
    to do in a separate module. */

sig Helper {
    cheaper: set Room -> Room -> Int
}

fun cheapEdges: set Room -> Room { Helper.cheaper.Int }

/** We want to set up `cheaper` as a possible alternative to the path that A* found. 
    It may be possible to express this more cleanly... */
pred cheaper_wellformed {
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

REQ_optimal_CE: assert {
    undirectedGraph
    allEdgesGTZero
    astarTrace
    AStar.goal in AStar.start.^(doors.Int) // will succeed
    eventually {
        halt
        cheaper_wellformed
        // Total of edge weights in cheaper is lower than what the A* model found.
        // NOTE: I'm a little bit worried here about overflow...
        (sum r: cheapEdges.Room | (Helper.cheaper[r])[Room]) < AStar.realCost[AStar.goal]
    }
} is unsat for 6 Room

/* Because I'm worried about overflow, I want to poke at the above check a little bit. 
   The main scenario I worry about is: an alternative path ending up negative because
   of overflow, when the "real" best path is positive. Wouldn't that be satisfiable?    

   Even more basically, we really should check that the wellformedness predicate isn't 
   unsatisfiable! Let's try looking for alternative paths that aren't one-hop.
*/

wellformed_non_immediate: assert {
    cheaper_wellformed
    AStar.goal not in AStar.start.^(doors.Int) // not immediately connected (as in example above)
} is sat for exactly 4 Room
// This fails!! Uh oh...


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
   // astarTrace
    cheaper_wellformed -- adding this: unsat :/ 

    /* eventually {
        // Confirm overflow is as expected
        halt
        some d: Room | AStar.realCost[d] = 2 // expected path length

    }*/
} is unsat for { // DEBUG: set to unsat to get instance
    Room = `A + `B + `C + `D
    AStar = `AStar0
    `A.doors = `B -> 1 + `C -> 2
    `B.doors = `A -> 1 + `D -> 1
    `C.doors = `A -> 2 + `D -> 3
    `D.doors = `C -> 3 + `B -> 1
    `AStar0.start = `A
    `AStar0.goal = `D
}
