2.0.0 (October 4, 2026)

* Project home moved from facebookincubator/retrie to xich/retrie. Report
  issues and send PRs to https://github.com/xich/retrie
* Support for GHC 9.14 (#13, @simonhorlick)
* Support for GHC 9.12 (#9, @pe200012)
* Dropped support for GHC < 9.6 (supported: 9.6, 9.8, 9.12, 9.14) (#3, @xich)
* Added -j/--jobs flag to bound the number of files rewritten concurrently.
  Defaults to the number of RTS capabilities, so peak memory use no longer
  grows with the number of target files. Fixes #10 (#18, @xich)
* Build the executables with the threaded RTS, so -j (or +RTS -N) actually
  rewrites files concurrently (#18, @xich)
* Require ghc-exactprint >= 1.12.1 (GHC 9.12) and >= 1.14.2 (GHC 9.14), which
  fix a space leak that caused high memory use on large files (#20, @xich)
* Split long grep/VCS invocations into chunks under the system argument limit,
  fixing failures with tens of thousands of target files
  (facebookincubator/retrie#63, @watashi)
* Fix missing parentheses in rewritten expressions and redundant parentheses
  in rewritten types (facebookincubator/retrie#69, @watashi)
* Don't strip the parentheses around sections, which produced malformed
  output (facebookincubator/retrie#70, @watashi)
* Add parentheses where needed when substituting into sections, record
  updates, record-dot projections and negation (#23, @simonhorlick)
* Backtick (infix) rewrites now work for functions of arity greater than two;
  previously these produced code that didn't compile (#14, @simonhorlick)
* Fix many exact-printing bugs in rewritten code: duplicated or misplaced
  trailing commas (e.g. "[succ 4,, ...]" or "(succ 1,)"), lost comments and
  syntax errors when a template has comments before a hole, stray spaces like
  "( Just x)", and lost annotations when reassociating infix operators and
  constructor patterns (#21, #26, @simonhorlick)
* Fix rewrites of expressions and patterns that were reassociated by fixity,
  which could replace the wrong source span (#21, @simonhorlick)
* Fix broken layout in CPP modules when a multi-line replacement lands
  somewhere other than column 1: continuation lines are now indented relative
  to where the replacement starts. Fixes #24 (#29, @xich)
* Preserve comments and layout when unfolding definitions with where clauses
  (#19, @simonhorlick)
* Unfolding works for constructor patterns with type applications
  (type arguments are ignored) (#13, @simonhorlick)
* Report unsupported type-variable binder syntax with the usual "missing
  syntax" error instead of crashing (#9, @pe200012)

1.2.3 (January 15, 2024)

* Support for GHC 9.8 (facebookincubator/retrie#61, @pranaysashank)
* Allow mtl 2.3 and transformers 0.6, as shipped with GHC 9.6
  (facebookincubator/retrie#56, @wz1000)

1.2.2 (March 24, 2023)

* Support for GHC 9.6 (facebookincubator/retrie#54, @wz1000)
* Allow optparse-applicative 0.17 (facebookincubator/retrie#53, @pepeiborra)

1.2.1.1 (November 17, 2022)

* Simplified build-depends: single ghc and ghc-exactprint bounds instead of
  per-GHC conditionals (facebookincubator/retrie#52, @pepeiborra)

1.2.1 (November 13, 2022)

* Support for GHC 9.4 (facebookincubator/retrie#49, @9999years)
* Escape single quotes in patterns passed to grep
  (facebookincubator/retrie#43, @nrnrnr)
* Support text 2.0 (facebookincubator/retrie#44, facebookincubator/retrie#45,
  @pepeiborra)
* Allow ghc-exactprint 1.5 (facebookincubator/retrie#47, @pepeiborra)

1.2.0.1 (January 3, 2022)

* Upgrade to ghc-exactprint 1.4 (facebookincubator/retrie#40, @pepeiborra)

1.2.0.0 (December 14, 2021)

* Early support for GHC 9.2.1 (thanks to Alan Zimmerman)
* Dropped support for GHC <9.2 (might readd it later)

1.1.0.0 (November 13, 2021)
* Remove dependency on xargs (facebookincubator/retrie#31)
* Allow rewrite elaboration

1.0.0.0 (April 9, 2021)

* Added --adhoc-type flag (facebookincubator/retrie#13)
* Added --adhoc-pattern, --pattern-forward, --pattern-backward
  (facebookincubator/retrie#15)
* Speed up file search when large number of files match.
* Removed support for GHC 8.4 and 8.8
* Added support for GHC 9.0.1

0.1.1.1 (June 1, 2020)

* Remove dependency on haskell-src-exts from library
  (facebookincubator/retrie#9)
* Support additional pattern syntax when generating fold/unfold rewrites
  (facebookincubator/retrie#8)
* Limit partial-application rewrite variants to irrefutible patterns
  (facebookincubator/retrie#7)
* Fix handling of qualified names during substitution
  (facebookincubator/retrie#5)
* Fix self-recursion check for do-syntax binds (facebookincubator/retrie#5)
* Fix bug in grep invocation for relative target paths
  (facebookincubator/retrie#5)

0.1.1.0 (May 8, 2020)

* Support GHC 8.10.1

0.1.0.1 (March 31, 2020)

* Don't fail if 'git' or 'hg' commands cannot be found.
* Better error message when syntax support needs to be extended.
* Add support for following type syntax: lists, tuples, constraints,
  unboxed sums, and forall.

0.1.0.0 (March 16, 2020)

Initial release
