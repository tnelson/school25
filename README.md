# Tim Nelson's Materials for SPECS Summer School 2025

## Flowlog

* [Slides](./flowlog.pptx). **These slides are subject to change!**
* [Flowlog Network Information Base (NIB) program](./NIB.flg). This program maintains knowledge of reachability, etc. in the network. 
* [Machine-generated Alloy spec for the NIB program](./flowlog_nib.als). 

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

**Note well:** The test file will spoil some of our discussion if you read it right away. I'm hoping that, by discussing together _first_, we might uncover some tests I didn't think to write! This often happens.

* [Forge domain model of Gridworlds](./gridworld.frg). 
* [Partial Forge validation for Gridworlds](./gridworld.test.frg).
* [Cope-and-drag specification for visualizing Gridworlds](./gridworld.cnd).

## A* Search Model 

A model of the A* search algorithm.

(These will be provided on Tuesday.)

* [Forge system model of A* Search](./astar.frg); uses the grid-world model. 
* [Partial Forge validation for A*](./astar.test.frg).
* [Separate module validating optimality for A*](./astar.optimality.frg). Note that this, and some properties in the prior module, are _requirements_: properties we hope for about the system, not validation of the model. We still consider this validation, however: we're working only with a specification. There's no implementation to verify. 
* [Cope-and-drag specification for visualizing A* runs](./astar.cnd).

<!-- * [astar.js](Forge custom visualization for A* runs). -->
