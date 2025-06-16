# Tim Nelson's Materials for SPECS Summer School 2025

## Flowlog

* [Machine-generated Alloy spec for a Flowlog program](./flowlog_nib.als). Concretely, this is a "Network Information Base": it maintains knowledge of reachability, etc. in the network. 

The Flowlog spec is Alloy, not Forge, because Forge didn't exist then! Other materials will use Forge.

## Forge installation

You can follow along (and run your own specs!) by downloading Forge. To install [Forge](https://forge-fm.org), we strongly suggest just pulling the Git repository, rather than working with the Racket package server. Concretely:

You'll need to install:
* Java (version 11 or later);
* the Racket language; and
* a web browser.

Then:
* Clone the Git repository (`git clone https://github.com/tnelson/forge`).
* `cd` into the repository (`cd Forge`).
* Install the Racket package (`raco pkg install ./forge `). (Make sure you include the prefix `./` or Racket will refer to the package server, not your newly cloned repo.)

## Gridworld Model

A domain model of grid-worlds, where the cost of traveling between rooms isn't necessarily `1`. 

* [gridworld.frg](Forge domain model of Gridworlds). 
<!-- * [gridworld.test.frg](Partial Forge validation for Gridworlds). -->
* [gridworld.cnd](Cope-and-drag specification for visualizing Gridworlds).

## A* Search Model 

(These will be provided on Tuesday.)

<!-- * [astar.frg](Forge system model of A* Search); uses the grid-world model. 
* [astar.test.frg](Partial Forge validation for A*).
* [astar.cnd](Cope-and-drag specification for visualizing A* runs).
* [astar.js](Forge custom visualization for A* runs). -->
