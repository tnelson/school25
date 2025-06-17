#lang forge/temporal

/*
  Modeling gridworlds as undirected graphs where each node has a location.
  Since we anticipate using this domain model in a temporal context, we start with forge/temporal.

  ASSUME: The distance metric is taxicab, not Euclidian. This metric should never over-estimate
          real path length if there are no non-vertical/horizontal moves and real costs are 
          integers greater than zero. 
  CHOICE: We need to have weights on edges between rooms, but we also need locations for each.
          The two obvious choices are "Int->Int->RoomType" and "Room" with location fields. 
          The first option leads to a lot of the Int^4 kind of helper functions, which complicates
          a few things. So we'll go with a Room sig.
         
          Consequence: likely we'll have a lot of "blocked" room locations, since we wont actually 
          instantiate (2^Bitwidth)^2 rooms.

    VISUALIZATION: Use the CnD specification in `gridworld.cnd`. This should auto-load.
*/

// This will auto-load the CnD visualizer.
// Click the "Layout" tab to switch from the default to CnD.
option run_sterling "gridworld.cnd"

// Because this model uses integers for both row/column indexes and for 
// edge weights, and thus for cost arithmetic, we want to disallow overflow
// to protect ourselves from, e.g., the extension of a path cost becoming less 
// than the original path cost. However, the built-in overflow prevention logic
// causes some issues later, when we add a transition system. Thus,
// DO NOT DO THIS:
// option no_overflow true

---------------------------------------------------------------------
-- Data Definitions
---------------------------------------------------------------------

sig Room {
  doors: pfunc Room -> Int,
  xloc: one Int,
  yloc: one Int
}

/** Taxicab or Manhattan distance. */
fun distance[r1, r2: Room]: one Int {
  add[abs[subtract[r1.xloc, r2.xloc]], abs[subtract[r1.yloc, r2.yloc]]]
}

---------------------------------------------------------------------
-- Domain Predicates
---------------------------------------------------------------------

/** Really, the inverse of allEdgesGTZero. */
pred someNegativeCostEdge {
  some i: Room.doors[Room] | i < 0
}

/** The gridworld is connected; there are no isolated rooms. */
pred allConnected {
  all r: Room | {
    // Don't include r1 itself, since it may be the only room.
    (Room-r) in r.^(doors.Int)
  }
}

/** The grid contains no cyclic path. Keep in mind that we are modeling undirected 
    edges using symmetric edges. So we can't just naively use transitive closure. */
pred noUndirectedCycle {
  // For every adjacent pair of rooms...
  all disj r1: Room, r2: r1.doors.Int | {
    // If we remove this (symmetric) edge, the pair becomes disconnected.
    r2 not in r1.^(doors.Int - (r1->r2 + r2->r1))
  }
}

/** Are these rooms horizonal or vertical neighbors? 
     (The name `nsew` is for north-south-east-west.) */
pred nsewNeighbor[r1, r2: Room] {
  // Don't use e.g., `abs[subtract[r1.yloc, r2.yloc]] = 1` here. This is simpler.
  // `next` is reserved in Forge, thus `succ`essor intead. 
  (r1.xloc = r2.xloc and (r1.yloc = r2.yloc.succ or r2.yloc = r1.yloc.succ))
    or
  (r1.yloc = r2.yloc and (r1.xloc = r2.xloc.succ or r2.xloc = r1.xloc.succ))
}

/** Undirected graph, modeled as a symmetric edge set with no self loops */
pred undirectedGraph {
    // This isn't strong enough; it allows for different costs
    // all r1, r2: Room | some r1.doors[r2] iff some r2.doors[r1]
    all r1, r2: Room | r1.doors[r2] = r2.doors[r1]

    all r: Room | no r.doors[r]
}

pred allEdgesGTZero {
  all i: Room.doors[Room] | i > 0
}

pred gridworld {
    undirectedGraph
    allEdgesGTZero
    
    // All doors lead to a distance-1 neighbor: no "skipping" cells in space. 
    // If a distance-1 neighbor is present, there is a corresponding door. 
    // (No diagonal doors.)
    all disj r1, r2: Room | {
      some r1.doors[r2] iff nsewNeighbor[r1,r2]
    }

    // All rooms have a different location. 
    all disj r1, r2: Room | r1.xloc != r2.xloc or r1.yloc != r2.yloc 
}

/** We ought to try to do some manual overflow protection. We can't safely
    speak of #Int, since we will never have enough bits to express that. 
    But we can use max[Int]. However, this seems best done in a different module,
    when sums actually matter. */

---------------------------------------------------------------------
-- Show an example gridworld
---------------------------------------------------------------------

/** 2^3 = 8 rows and columns, so 64 possible locations. */
grid6Rooms: run {
  gridworld
} for 3 Int, exactly 6 Room 