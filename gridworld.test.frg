#lang forge/temporal

/*
  Validation for gridworld.frg. 

  Potential spoilers for SPECS 2025! 
  Read this model only at the appropriate time. :-)
*/

open "gridworld.frg"
option run_sterling off

/*
  Forge has more testing syntax than Alloy does. Forge also provides the `assert`
  keyword, but it is used differently than it is in Alloy. Don't try to write 
  non-reusable predicates using the `assert` keyword. Instead:
    - assert {...} is consistent with <predname>
    - assert {...} is inconsistent with <predname>
    - assert {...} is sat
    - assert {...} is unsat
    - assert {...} is necessary for <predname>
    - assert {...} is sufficient for <predname>

  Tests should be named when possible. Use <name>: assert ...

  If using forms other than `is sat` or `is unsat`, you can add universal
  quantifiers that have both sides in scope. Say all x: A ... | assert ...
*/

---------------------------------------------------------------------
-- Validation: nsewNeighbor
-- These are more like unit tests. The "optional predicates" are very 
-- specifically describing locations of rooms in the gridworld.
---------------------------------------------------------------------

neighbor_samex: assert all r1, r2: Room | 
  { r1.xloc = 0 and r2.xloc = 0
    r1.yloc = 1 and r2.yloc = 0} 
is sufficient for nsewNeighbor[r1,r2] 
for exactly 2 Room

neighbor_samey: assert all r1, r2: Room | 
  {r1.yloc = 0 and r2.yloc = 0
  r1.xloc = 1 and r2.xloc = 0}
is sufficient for nsewNeighbor[r1,r2] 
for exactly 2 Room

not_neighbor_samex: assert { some r1, r2: Room | {
  r1.xloc = 0 and r2.xloc = 0
  r1.yloc = 2 and r2.yloc = 0
  nsewNeighbor[r1,r2]}
} is unsat for exactly 2 Room

not_neighbor_samey: assert { some r1, r2: Room | {
  r1.yloc = 0 and r2.yloc = 0
  r1.xloc = 2 and r2.xloc = 0
  nsewNeighbor[r1,r2]}
} is unsat for exactly 2 Room

nsewNeighbor_consistent: assert {
  gridworld
  some r1, r2: Room | nsewNeighbor[r1,r2]
} is sat for exactly 2 Room

---------------------------------------------------------------------
-- Validation: gridworld
-- My first worry is about whether gridworld is overconstrained. E.g., 
-- When I was making this model, I accidentally forbade connected rooms.
-- We'll start with more focused consistency checks. 
---------------------------------------------------------------------

/** The grid contains a sub-pattern like a knight's move in chess. */
pred subgrid_knight { 
    some disj r1, r2, r3, r4: Room | {
        r2.xloc = r1.xloc
        r2.yloc = add[1, r1.yloc]
        r3.xloc = r2.xloc
        r3.yloc = add[1, r2.yloc]
        r4.xloc = add[r2.xloc, 1]
        r4.yloc = r3.yloc
        some r1.doors[r2]
        some r2.doors[r3]
        some r3.doors[r4]
    }
}

/** The grid contains a pattern like a (one-square) bishop's move in chess. 
    I.e., there can be a diagonal edge. */
pred subgrid_bishop {
    some disj r1, r2: Room | {
        r2.xloc = add[r1.xloc, 1]
        r2.yloc = add[r1.yloc, 1]
        some r1.doors[r2]
    }
}

gw_knight: assert subgrid_knight is consistent with gridworld
gw_bishop: assert subgrid_bishop is inconsistent with gridworld

/** When we search the gridworld, there is a distinction between "goal not found"
    And "goal unreachable". Make sure the latter is possible. */
gw_disconnected: assert allConnected is consistent with gridworld
gw_connected: assert {not allConnected} is consistent with gridworld

/** Testing the combination of 2 domain predicates: I want to be sure that 
    one of these patterns doesn't somehow force connectivity. At 4 rooms, 
    we need all 4 for the knight's move and thus all must be be connected. */
gw_knight_disconnected_unsat4: assert {
    subgrid_knight 
    not allConnected
} is inconsistent with gridworld for exactly 4 Room
gw_knight_disconnected_sat5: assert {
    subgrid_knight 
    not allConnected
} is consistent with gridworld for exactly 5 Room


/** Double-check that we can either have cycles or no cycles. */
gw_noCycle: assert noUndirectedCycle is consistent with gridworld 
gw_cycle: assert {not noUndirectedCycle} is consistent with gridworld 

/** If the knight's move is the only set of rooms, it's possible to have 
    a cycle unless diagonal edges are allowed. */
gw_knight_cycle_4_impossible: assert {
    gridworld
    subgrid_knight 
    not noUndirectedCycle
} is unsat for 4 Room 

/** We can find a connected gridworld with all non-zero weight edges. 
    This is actually a regression test, from a real specification bug! 
    "for 3 Room" was satisfiable under that bug, because it allowed 
    0, 1, and 2-Room solutions. */
connected_nontrivial_size3: assert {
    allConnected
    allEdgesGTZero
} is consistent with gridworld for exactly 3 Room
