# Tim Nelson's Materials for SPECS Summer School 2025

## Flowlog

* [Slides](./flowlog.pptx). (As of June 16; I may clean up some of them afterward.)
* [Flowlog Network Information Base (NIB) program](./NIB.flg). This program maintains knowledge of reachability, etc. in the network. 
* [Machine-generated Alloy spec for the NIB program](./flowlog_nib.als). 

The Flowlog spec is Alloy, not Forge, because Forge didn't exist then! Other materials will use Forge.

## Validation Slides 

These are adapted from [the module I co-taught with Pamela Zave in 2023](https://fm.csl.sri.com/SSFT23/). These slides were from Pamela's part of the module. I'm using them with permission.

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

For our context today, I suggest running via the command line, not the VSCode extension. You just run `racket <filename.frg>`. If you want to use [CnD](https://www.siddharthaprasad.com/copeanddrag/), you'll need to install it separately:

```
npm install cope-and-drag -g
npx cope-and-drag
```

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

## Thoughts on Hackathon Topics 

I'll try to scope these to the 2-day hackathon, not a full research project. 

### "Which instance?" in Alloy/Forge

Honestly, Eunsuk's list was great for those interested in modifying or doing empirical studies with Alloy. If you're interested in the "which instance should be shown next?" problem, [I've done some work there](https://cs.brown.edu/~tbn/publications/nsdfk-icse13-aluminum.pdf) with collaborators at Brown. But so have a few others. In particular, I'm a big fan of [this work](https://link.springer.com/chapter/10.1007/978-3-642-54804-8_2) by Alcino Cunha and others, which is built into the Pardinus/Kodkod engine that both Forge and Alloy use. 

If you want to experiment with different instance-iterator priorities, I suggest working with Pardinus directly, _not_ Alloy, which doesn't give the full interface that Pardinus does. Forge gives a bit more (e.g., exposing maximization and minimization!) but it's still a very limited set of features compared to the full target-oriented engine.

I'm curious whether Hamming-distance metrics are always good. Don't they give a lot of weight to higher-arity predicates? What other metrics could we imagine?

### Visualization in Alloy/Forge 

We've seen a few improvements on Alloy's default visualizer. Forge uses both Sterling and CnD. Penlloy uses Penrose. There are some other academic works that explore the question, which you can find links to in our [paper forthcoming at ECOOP](https://www.siddharthaprasad.com/unpublished/pgnk-lightweight-diagramming.pdf). 

I'm personally interested in what it would take to integrate Alloy and CnD. The latest version of Alloy has a command-line interface; if there's a way to print the instance XML there then we could perhaps imagine piping that data to CnD. 

### What would you like to model? 

Do you have a research domain you'd like to model? This is a good time to get advice and perhaps build a prototype. Some of us have been writing specifications for a long time, and so we may be able to help you avoid various pitfalls. 

## Extending Forge 

Skyler and I sat down on Thursday and built a demo of how you can extend Forge, if you know Racket. 

Concretely, we built a new operator that repeats the `next_state` operator a given number of times.

* [Racket file with `nexts` defined](./nexts.rkt)
* [Forge model using the new operator](./extension_demo.frg)
