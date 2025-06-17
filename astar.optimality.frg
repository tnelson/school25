#lang forge/temporal 
open "gridworld.frg"
open "astar.frg"
option run_sterling off

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
