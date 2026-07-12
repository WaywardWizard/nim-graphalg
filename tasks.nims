## General tasks for nim projects
## - mkdocs: Generate documentation from markdown and source (fd)
## - chkcompat: Find earliest compatible nim version (requires choosenim)
## - upGhPage: Setup github pages from generated documentation. Documentation to
##     go into $reporoot/docs and include an index.html file
## - rmGhPage: Remove github pages page
## - ghPage: Query github page status
import std/[pegs,strbasics,strformat, json,tables]

var docfolder = "docs" # must be this for ghpages
type Shellcmd = distinct string
var nimdocShArgs: seq[tuple[argname,value: string, validator:Peg]] = @[
  ("git.url", "git remote get-url origin",peg"^https\:\/\/github\.com"), # git url
  ("git.commit", "git describe --tags --abbrev=0", peg"v?\d+(\.\d+)*"), # extract tag matching docs
]
var nimdocArgs: seq[tuple[argname,value: string, validator:Peg]] = @[
  ("outdir",docfolder,peg"^!\/"),
]

task mkdocs, "Generate HTML documentation":
  var docarg: string
  for (k,s,p) in nimdocShArgs:
    let val = (gorgeEx s).output
    assert val.find(p) > -1, &"Argument --{k}:{val} not resolvable with cmd {s} and validator {p}"
    docarg &= &" --{k}:{val}"
  for (k,v,p) in nimdocArgs:
    assert v.find(p) > -1, &"Value --{k}:{v} does not match validator {p}"
    docarg &= &" --{k}:{v}"

  exec &"rm -rf {docfolder}"
  exec(&"fd -g *.md | xargs -r echo md2html {docarg} --index:only")
  exec(&"fd -g *.md | xargs -r nim md2html {docarg} --index:off")
  exec(&"nim doc {docarg} --index:only --project src/*.nim")
  exec(&"nim doc {docarg} --index:on --project src/*.nim")
  exec &"mv {docfolder}/{{the,}}index.html"

task chkcompat, "Test against other nim versions":
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

task upghpage, "Setup github pages":
  exec &"gh api repos/{{owner}}/{{repo}}/pages -f build_type=legacy -f 'source[branch]=master' -f 'source[path]=/{docfolder}'"
task rmghpage, "Remove github page":
  exec "gh api --method DELETE repos/{owner}/{repo}/pages"
task ghpage, "Query status of github pages page for repo":
  exec "gh api repos/{owner}/{repo}/pages"
