# Package

version       = "0.1.0"
author        = "Ben Tomlin"
description   = "Iterative (vs. recursive) Graph Algorithms & Structures"
license       = "MIT"
srcDir        = "src"


# Dependencies

requires "nim >= 2.2.6"

requires "fusion >= 1.2"

import std/[pegs,strbasics,strformat, json]

var docfolder = "docs" # must be this for ghpages
task docs, "Generate HTML documentation":

  exec(&"fd -g *.md | xargs -r echo md2html --index:only --outdir:{docfolder}")
  exec(&"fd -g *.md | xargs -r nim md2html --index:on --outdir:{docfolder}")

  exec(&"nim doc --outdir:{docfolder} --index:only --project src/*.nim")
  exec(&"nim doc --outdir:{docfolder} --index:on --project src/*.nim")

task nimversion, "Test against other nim versions":
  # set requires to the earliest version you want to test back to
  var versions: seq[string]
  var found = false
  for line in gorgeEx("choosenim --nocolor versions").output.splitLines:
    if line.match(peg"^\s*Installed\:"):
      found = true
      continue
    if found:
      for m in line.findAll(peg"\s{\d+\.\d+\.\d+}(\s/$)"):
        versions.add m.strip

  var bestVersion: string
  for v in versions:
    echo "Testing ", v
    var (output,exit) = gorgeEx &"choosenim {v}; nimble test"
    if exit==0:
      bestVersion = v
    else:
      echo "Failed ", v
      echo output
      break

  echo "Best version ", bestVersion

task ghpage, "Setup documentation on github pages":
  exec &"gh api repos/{{owner}}/{{repo}}/pages -f build_type=legacy -f 'source[branch]=master' -f 'source[path]=/{docfolder}'"
task rmghpage, "Remove github page":
  exec "gh api --method DELETE repos/{owner}/{repo}/pages"
task qghpage, "Remove github page":
  exec "gh api repos/{owner}/{repo}/pages"


requires "combinatronics >= 1.0.0"
