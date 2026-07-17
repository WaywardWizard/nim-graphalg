# Package
version       = "1.2.0"
author        = "Ben Tomlin"
description   = "Iterative (vs. recursive) Graph Algorithms & Structures"
license       = "MIT"

# Tasks
when fileExists("tasks.nims"):
  include "tasks.nims" # distribute th{is,ese} files or the nimble file breaks

# Dependencies
requires "nim >= 1.4.0"
requires "combinatronics >= 1.2.0" # brute forcing vertex order/edgeset
requires "fusion >= 1.2" # DSL pattern matching
requires "datastructures >= 1.2.0"