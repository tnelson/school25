#lang forge/temporal
open "gridworld.frg"
open "astar.frg"

// Note: I like running test files from the command line, to avoid any delay in feedback.

// Our tests will be on smaller graphs than 11 or 12 nodes. So we can reduce this from the
// number we used in the main model. 
option max_tracelength 8

/***************************************************
/** COMMENT THIS OUT AND RE-RUN IF ANY TESTS FAIL. */
// option run_sterling off


---------------------------------------------------------------------
-- Optional predicates about the _domain_ for validation.
--  (Minor bad-modeling problem: I've put the start and goal in _AStar_,
--   while these are controlled by the domain. At least they are in the "interface".)
---------------------------------------------------------------------

pred goalReachable {
    AStar.goal in AStar.start.^(doors.Int)
}

pred goalNotImmediate {
    let links = doors.Int | {
        AStar.goal not in AStar.start.links 
    }
}

---------------------------------------------------------------------
-- Optional predicates about the _system_ for validation.
---------------------------------------------------------------------

pred successStateEventually {
    eventually AStar.goal in AStar.finalized
}
pred failureStateEventually {
    eventually {
        AStar.goal not in AStar.finalized
        no AStar.frontier } }



////////////////////////////////////////
// ? What else would you like to add? //
////////////////////////////////////////



---------------------------------------------------------------------
-- Validation of single steps, prefixes, subtraces, etc.
-- These are finer-grained tests than looking at full traces. I like 
-- to confirm that specific transitions are possible, no 2 transitions
-- can be enabled at once, etc. etc. 
-- It's also useful to make prefix-satisfiability tests, especially 
-- when debugging unsatisfiablity.
---------------------------------------------------------------------

/** Describe a 3-step run prefix on a gridworld. Anything shown after 3 steps is 
    unconstrained! This is a useful debugging technique if an overconstraint is 
    discovered: gradually telescope out until reaching unsat. */
pred three_steps_prefix_gw {
  // We want to see this on a gridworld.
  gridworld
  // Start at an initial state
  init
  // These lines say that A* finalizes at least 3 rooms.
  step 
  next_state step
  next_state next_state step
  // Adding this line says that A* finishes running after those 3 rooms are finalized.
  // BEWARE: don't try to use negation, because without the scaffolding of the trace pred, 
  //   "not halt" might mean "do anything, so long as it isn't a halt transition".
  next_state next_state next_state halt 
}

/** We should be able to find a 3-step run prefix on a gridworld with non-zero weights. */
gw_len3_prefix_costs: assert {
    three_steps_prefix_gw
    allEdgesGTZero
} is sat

/** These aren't "invariants" exactly. They refer to 2 states at once. We just 
    want to check that certain monotonicity properties are observed by `step`. */
check_realCost_monotonic: assert {
    undirectedGraph and step and not (realCost.Int in realCost'.Int)
} is unsat
check_estimatedCost_monotonic: assert {
    undirectedGraph and step and not (estimatedCost.Int in estimatedCost'.Int)
} is unsat
check_treeDomain_monotonic: assert {
    undirectedGraph and step and not (tree.Room in tree'.Room)
} is unsat
/** the real cost is always <= the estimated cost, unless overflow occurs.
    Technically an "invariant", but the "unless overflow occurs" part is annoying. */
/*check_real_vs_estimated_monotonic: assert {
    undirectedGraph
    step
    not {
        // precondition: need estimatedCost not to overflow, and defined pre-transition
        (all r: Room | { 
            invariants // assuming these are verified
            
            some AStar.estimatedCost[r]
            some AStar.realCost[r]
            AStar.estimatedCost[r] >= 0
            AStar.estimatedCost'[r] >= 0
            AStar.realCost[r] <= AStar.estimatedCost[r] 
        }) implies
        (all r: Room | { 
            AStar.realCost'[r] <= AStar.estimatedCost'[r] 
        })
    }
} is unsat*/

/** Various state invariants. 
    - The shortest-path `tree` is indeed always a tree. 

    That first invariant isn't inductive alone, so we need to enrich it.
    (It's not trivial, because there are so many state relations.)
    
    - Enrichments:
      - frontier+finalized always includes the start room
      - frontier is disjoint from finalized
      - tree's codomain (reached from) is never outside finalized
      - tree's domain (reached) is never outside finalized+frontier
      - frontier and finalized are all reachable from the start
    
    - Every edge in the shortest-path tree is an edge in the graph.
    - real and estimated costs are only populated for rooms in the frontier/finalized sets. */
pred invariants {
     all r: Room | r not in r.^(AStar.tree)
     
     AStar.start in AStar.frontier + AStar.finalized 
     init or AStar.start in AStar.finalized
     no (AStar.frontier & AStar.finalized)
     AStar.tree[Room] in AStar.finalized
     AStar.tree.Room in  AStar.frontier + AStar.finalized
     AStar.frontier + AStar.finalized in (AStar.start.^(doors.Int) + AStar.start)

     AStar.tree in doors.Int

     AStar.realCost.Int in AStar.frontier + AStar.finalized
     AStar.estimatedCost.Int in AStar.frontier + AStar.finalized

     // Frontier-consistency: everything finalized or in the frontier is 
     // reachable using only doors between start/frontier/finalized.
     // TODO

     
}
sat_invariants: assert { invariants } is sat
init_invariants: assert { init } is sufficient for invariants 
check_invariants: assert {
    // Structural preconditions/assumptions
    AStar.start != AStar.goal
    undirectedGraph
    // Precondition: invariant holds of prestate, take a step
    invariants
    step
    // Invariant violated after step
    next_state not invariants 
} is unsat

---------------------------------------------------------------------
-- Validation of full trace behavior (astarTrace)
-- If I haven't been building validation tests constantly, I like to 
-- start with a small number of these, since they often find broad 
-- errors in the model.
---------------------------------------------------------------------

-- The search can run on inputs with reachable, unreachable goals that are next to start, or not.
trace_reach_close: assert {gridworld and goalReachable and not goalNotImmediate} 
  is consistent with astarTrace for 6 Room
trace_reach_3plus: assert {gridworld and goalReachable and goalNotImmediate}
  is consistent with astarTrace for 6 Room
trace_unreach_3plus: assert {gridworld and not goalReachable and goalNotImmediate} 
  is consistent with astarTrace for 6 Room

-- If the goal is reachable and next-door, we can't fail to find it. 
-- (No need to assert `gridworld`.)
trace_unreach_close: assert {not goalReachable and not goalNotImmediate} 
  is inconsistent with astarTrace for 6 Room

-- If the goal is reachable, A* will find it eventually (No need to assert `gridworld`)
trace_successNecessary: assert {astarTrace and goalReachable} 
  is sufficient for successStateEventually for 6 Room

-- If start=goal, even if there are no edges to take, A* will end in a success state.
-- No need to assert `gridworld`. 
trace_failureNecessary: assert {AStar.goal != AStar.start and astarTrace and not goalReachable} 
  is sufficient for failureStateEventually for 6 Room


/** I expect that if `halt` isn't runnable, that we must run a `step`. 
    Note that this is _not_ the same as "if `halt` isn't runnable, `step` is runnable." 
    Tests like this will discover situations where a transition appears "enabled" but 
    there is some deep conflict in its action or frame conditions. */
trace_cant_halt_implies_step_taken: assert {
    astarTrace
    not haltEnabled
} is sufficient for step for 6 Room

/** Invariant: the shortest-path tree always involves only nodes with a cost. */
trace_tree_invariant: assert {
    undirectedGraph => {
        always {AStar.tree[Room] + AStar.tree.Room in AStar.realCost.Int}}
} is necessary for astarTrace for 6 Room

/* It is possible for realCost != estimatedCost in a real trace */
realCost_diff_estimatedCost: assert {
    eventually {some r: Room | AStar.realCost[r] != AStar.estimatedCost[r]}
} is consistent with astarTrace for 6 Room

/* Distinguish vs. greedy-shortest-path-first: it is possible to take a transition
   "uphill". I'm testing this in the context of a full trace, rather than using 
   a single transition, because I want to guard myself against being lulled into 
   a false sense of soundness because "sat" but under the hood those are all using 
   unreachable prestates. */
disagree_with_greedy_possible: assert {
    eventually { 
        some greedy: AStar.frontier | {
            greedy not in AStar.finalized'
            heuristic[greedy, AStar.goal] < 
            heuristic[AStar.finalized'-AStar.finalized, AStar.goal]
        }
    }
} is consistent with astarTrace for 6 Room

/** In principle we could do this without a complete trace, but there's a lot of 
    unreachable-prestate annoyance. So we'll just make it a trace property. */
check_only_one_expanded: assert {
    always {
        step =>
        one (AStar.finalized' - AStar.finalized)
    }
} is necessary for astarTrace for 6 Room

---------------------------------------------------------------------
-- REQUIREMENTS: what do we expect from A*'s end-to-end behavior?
---------------------------------------------------------------------

/** If we can't reach the goal, we won't ever assert there's a path to it */
REQ_unreachable_no_tree: assert {
    AStar.goal not in AStar.start.^(doors.Int) implies 
        always { AStar.start not in AStar.goal.^(AStar.tree) }
} is necessary for astarTrace for 6 Room

/** If we can reach the goal, we will eventually find a path to it.
    We need the start != end condition, otherwise the tree won't be used. */
REQ_reachable_tree: assert {
    (AStar.start != AStar.goal) implies {
        AStar.goal in AStar.start.^(doors.Int) implies 
            eventually { AStar.start in AStar.goal.^(AStar.tree) }}
} is necessary for astarTrace for 6 Room

/** Total of edge weights leading to goal in shortest-path tree equals realCost[goal].*/

/*
  That's really slow! We could reduce the bound, or move AStar.start and AStar.end into one sigs. 
  It turns out neither of these help much on their own. 

  Let's try a different kind of optimization: an explicit partial instance. Identifiers preceded
  by a back-tick name _atoms_.

  We don't want to constrain locations or connectivity. But we could limit edge weights to be 
  >0 *here*, rather than leaving it to the solver via constraint. This affects the lower and 
  upper bounds sent to the engine directly.
*/

inst optimizer_5rooms {
  // There are 5 possible rooms.  (6 takes longer than I want for this lecture. :-))
  Room in `Room0 + `Room1 + `Room2 + `Room3 + `Room4 
  AStar = `AStar0
  // We must use at least 2 of them.
  start = AStar -> `Room0
  goal = AStar -> `Room1
  // Edge weights are non-negative 
  doors in (`Room0 + `Room1 + `Room2 + `Room3 + `Room4) -> 
           (`Room0 + `Room1 + `Room2 + `Room3 + `Room4) -> (0+1+2+3)
}

/** Summing up all edges in the path agrees with the realCost table entry. */
REQ_path_cost_agrees: assert {
    {(AStar.start != AStar.goal)
     undirectedGraph 
     AStar.goal in AStar.start.^(doors.Int) 
    } implies 
      eventually {
        // Use the fact that `tree` is in fact a tree. Follow the edges from goal to start. 
        (sum r: usedEdges.Room | (r.doors)[r.(AStar.tree)]) = AStar.realCost[AStar.goal]
    }
} is necessary for astarTrace for optimizer_5rooms


/* OPTIMALITY IS IN A SEPARATE FILE! */