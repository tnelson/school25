#lang forge/temporal

/* 
  Demo of adding a Forge extension via Racket. The `nexts.rkt` module contains 
  the definition of a new, custom operator that repeats the `next_state` operator
  a specified number of times. Note that there aren't many guard rails here; passing
  the wrong kind of argument, etc. may cause unexpected behavior. 
*/

open "nexts.rkt" 

one sig World {
    var value: one Int
}

pred init {World.value = 0}
pred increment {World.value' = add[World.value, 1]}
pred double {World.value' = multiply[World.value, 2]}

run {
    init 
    always {increment or double}
    // After 3 transitions of some sort, the value is >0 but after that we see overflow.
    nexts[3, World.value > 0 and World.value' < 0]

    // Note error handling (uncomment to see)   
    // nexts[univ, World.value > 0 and World.value' < 0]
    // nexts[3, init]
} 
// Default Int set = [-8, 7]
// 0 -> 1 -> 2 -> 4 -> -8