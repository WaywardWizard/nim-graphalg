# Package
version       = "0.1.0"
author        = "Ben Tomlin"
description   = "Iterative (vs. recursive) Graph Algorithms & Structures"
license       = "MIT"
srcDir        = "src"


# Dependencies
requires "nim >= 1.4.0"
requires "combinatronics >= 1.0.0" # brute forcing vertex order/edgeset
requires "fusion >= 1.2" # DSL pattern matching

# Tasks
include "tasks.nims"