/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joscha Mennicken
-/

import VersoManual
import Manual.Meta
import Manual.Meta.Markdown

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Lean 4.37.0-rc1 (2026-11-18)" =>
%%%
tag := "release-v4.37.0"
file := "v4.37.0"
%%%

:::warn
These release notes describe a _release candidate_, not the final release.
They may be incomplete and are subject to change.
:::

For this release, 370 changes landed.
In addition to the 71 feature additions
and 159 fixes listed below,
there were 7 refactoring changes,
1 documentation improvement,
108 performance improvements,
4 improvements to the test suite,
and 20 other changes.

# Language

````markdown

- [#16533](https://github.com/leanprover/lean4/pull/16533)
  changes `registerReservedNamePredicate` to take two functions: a test on the last component of the name, and the predicate itself. A name is a candidate for being reserved only if its last component passes the test.

- [#16531](https://github.com/leanprover/lean4/pull/16531)
  fixes an "environment already contains" import error when two modules realize the same `match` congruence equation.

- [#16512](https://github.com/leanprover/lean4/pull/16512)
  fixes a bug wherein loose bvars where not always checked for in inductive declarations. This issue looks benign, and does not lead to an apparent proof of false.

- [#16519](https://github.com/leanprover/lean4/pull/16519)
  makes the generation of `match` equations faster for a `match` with many alternatives and a catch-all. The `big_match_string` benchmark with 128 alternatives is about 14% faster (#16313).

- [#16505](https://github.com/leanprover/lean4/pull/16505)
  makes each congruence equation `f.match_1.congr_eq_i` of a `match` be generated on demand, independently of the other ones. It fixes a performance regression from #16502 for a `match` with many alternatives where only a few match equations are not proved by `rfl`, for example literals or constructors followed by a catch-all: `big_match_nat_split` and `big_match_partial` are 18% and 7% faster. Referring to `f.match_1.congr_eq_i` by name also generates only that theorem.

- [#16503](https://github.com/leanprover/lean4/pull/16503)
  makes the kernel type check a constant created by a nested realization only once. For example, the equation theorems of a function request the equations of its `match`, and the kernel checked each of those theorems twice, or three times when they requested further theorems themselves. Generating the equations of a `String → Nat` function with 128 literal alternatives is about 25% faster. It also fixes repeated error messages: a kernel error in such a constant was reported once per nesting level, and is now reported once.

- [#16501](https://github.com/leanprover/lean4/pull/16501)
  adds the option `shiftLeft.threshold` (default: 65536). `whnf`, `simp`, and `grind` no longer evaluate a left shift of literals when the shift amount is above this threshold, and report a warning instead, as they already do for exponents above `exponentiation.threshold`. Previously, a shift amount of 2^32 or more aborted the Lean process with `INTERNAL PANIC: Nat.shiftl exponent is too big`, e.g., in `example : (1 <<< 4294967296 : Nat) = 0 := by simp`. `cbv` and the compiler use the same bound as a constant.

- [#16404](https://github.com/leanprover/lean4/pull/16404)
  makes the `do` elaborator reject a `finally` block that reassigns a `mut` variable in scope at the `try`. The error names the reassigned variables:

  ```
  A `finally` block cannot reassign the `mut` variable `s`.
  ```

- [#16482](https://github.com/leanprover/lean4/pull/16482)
  turns the `csimpCore` test, which checks that declarations replaced by `csimp` are `noncomputable`, into a linter.

- [#16480](https://github.com/leanprover/lean4/pull/16480)
  makes equation theorems of nonrecursive definitions faster to type check when the definition is a `match` on literals. For a `String → Nat` function with 128 `String` literal alternatives, generating its equation theorems, which `simp [f]` and `cbv` need, takes 15.5s instead of 25.7s.

- [#15856](https://github.com/leanprover/lean4/pull/15856)
  adds an optional starting position to `Lean.Parser.parseHeader`, allowing tools such as Verso to parse module headers inside a larger source file while preserving source locations.

- [#16477](https://github.com/leanprover/lean4/pull/16477)
  makes generating the equations of a `match` faster when a discriminant is annotated with `h :` and the patterns are values. For `match h : s with` and 64 `String` literal alternatives, it takes 0.40s instead of 1.50s.

- [#16476](https://github.com/leanprover/lean4/pull/16476)
  makes the proofs that two `String` literals are different cheaper to check, improving on #16474. For two literals that share a prefix of 512 characters, the kernel checks the proof in 3.5ms instead of 4.4ms.

- [#16474](https://github.com/leanprover/lean4/pull/16474)
  makes the proofs that two `String` literals are different faster to build and to check. These proofs are used by `simp`, `cbv`, and the equations of `match` expressions with `String` patterns. For two literals that share a prefix of 64 characters, the kernel checks the proof in 0.60ms instead of 1.85ms.

- [#16465](https://github.com/leanprover/lean4/pull/16465)
  makes generating the equations of a `match` with many value patterns faster. For a `match` with two discriminants and 64 alternatives such as `| "name", 0 => ..` followed by a catch-all, it takes 0.38s instead of 1.16s.

- [#16460](https://github.com/leanprover/lean4/pull/16460)
  makes generating the equations of a `match` with many alternatives faster when the patterns contain literals nested in constructors, e.g., `| some "a" => ..`. For 32 alternatives of this form, generating the `match` equations takes 0.53s instead of 1.45s.

- [#16354](https://github.com/leanprover/lean4/pull/16354)
  speeds up the generation of equation lemmas for definitions that `match` on `String` literals. With 64 literal patterns, generation used to hit the heartbeat limit.

- [#16408](https://github.com/leanprover/lean4/pull/16408)
  makes elaborating large `mutual` blocks defined by well-founded recursion faster. Cleaning up the termination proof goals no longer takes time proportional to the number of functions in the block, which used to make elaborating the whole block quadratic. As a side effect, the functional induction principle of a function with a nested recursive call, such as `f (f x)`, no longer contains a duplicate induction hypothesis for the inner call; proofs that name the hypotheses of such a case positionally need to drop one name.

- [#16422](https://github.com/leanprover/lean4/pull/16422)
  simplifies the result type of the function that packs a `mutual` block defined by well-founded recursion: where both branches of a case split on the packed argument have the same non-dependent result type, the case split is omitted. If all functions have the same result type, the packed function now has that type, as the docstring of `ArgsPacker.Mutual.uncurryType` already promised. Previously this type was a case split over all functions of the block, which appeared in the motive of every case split in the definition and its unfolding lemma and made type checking large blocks slow.

- [#16409](https://github.com/leanprover/lean4/pull/16409)
  packs the arguments of a `mutual` block defined by well-founded recursion into a balanced tree of `PSum` types instead of a right-nested chain. The nesting depth of packed arguments and of the case splits that take them apart becomes logarithmic in the number of functions, which makes elaborating and type checking large blocks much cheaper. Blocks of up to three functions are packed as before.

- [#16320](https://github.com/leanprover/lean4/pull/16320)
  fixes a segfault when `withImportModules` is called a second time in one process and the imported module imports another package root, a regression from #15291.

- [#16279](https://github.com/leanprover/lean4/pull/16279)
  fixes `Expr.hasLooseBVar`, `Expr.liftLooseBVars`, `Expr.lowerLooseBVars`, task priorities and the kernel's handling of the number of parameters of an inductive declaration, which silently truncated values of `2^32` and above to 32 bits. For example, the kernel accepted an inductive declaration with `numParams := 2^32` and recorded `numParams = 0`, and a task with priority `2^32 - 1` ran synchronously in the caller rather than on a dedicated thread.

- [#15889](https://github.com/leanprover/lean4/pull/15889)
  makes type class resolution reuse cached results much more often. A result is shared by all local contexts that agree on the local instances of the classes its search consulted, and declaring or erasing an instance only invalidates the results whose search consulted the instance's class. Building all of Mathlib takes about 2.7% less wall-clock time, and about 6.7% less time in type class resolution.

- [#16273](https://github.com/leanprover/lean4/pull/16273)
  makes `set_option maxRecDepth 0` mean "no limit" in the compiler and in macro expansion, and makes huge `maxRecDepth` values act as unlimited in the kernel instead of wrapping around to a small limit. Previously, `maxRecDepth 0` was stricter than e.g. `maxRecDepth 10000`, and values such as `2^60` could reject shallow declarations.

- [#16235](https://github.com/leanprover/lean4/pull/16235)
  makes the equation lemmas `f.eq_<i>` keep the `have`s and `let`s of the right-hand side when they split a `match` below them, instead of inlining their values into each equation. Inlining duplicated the values, exponentially for nested `have`s, and lost the sharing of the join points that `do` notation introduces, which `vcgen +jp [f]` needs (#16122). The generated equations are otherwise the same: inlining the `have`s gives back the previous equations.

- [#16252](https://github.com/leanprover/lean4/pull/16252)
  fixes a kernel error `unknown constant 'f.match_1.eq_1'` when generating equation lemmas whose statements contain cast proofs, as happens when a `match` on a literal is reduced under a dependent argument. Definitions whose body eliminates an empty type now get one equation lemma stating the unfolded definition, instead of none.

- [#16219](https://github.com/leanprover/lean4/pull/16219)
  fixes timeouts when comparing distinct `Float`/`Float32` literals, for example while generating the equation lemmas of a `match` on float literals. Unifying such literals used to unfold the float model on both sides in lockstep.

- [#16215](https://github.com/leanprover/lean4/pull/16215)
  fixes `match` on `Float` and `Float32` literal patterns treating literals that denote the same value (such as `5` and `5.0`, or `16777216` and `16777217` as `Float32`) as different patterns, which could cause a matching alternative to be skipped. Such overlapping alternatives are now also reported as redundant.

- [#16208](https://github.com/leanprover/lean4/pull/16208)
  makes the equation lemmas `f.eq_<i>` keep the `have`s and `let`s at the root of the right-hand side, unless they must be zeta-reduced to split a `match`. For a definition without a `match`, `f.eq_1` is now the same as `f.eq_def`.

- [#16138](https://github.com/leanprover/lean4/pull/16138)
  makes `Kernel.Environment.replay` add the constants used in the types of all members of a mutual inductive block before adding the block. Previously only the dependencies of the member through which replay reached the block, and those of the constructors, were added, so a valid export could be rejected with `unknown constant`, depending on hash order.

- [#16132](https://github.com/leanprover/lean4/pull/16132)
  speeds up type class resolution for classes with many instances.

- [#16105](https://github.com/leanprover/lean4/pull/16105)
  ports the macro used for long list to a term elaborator instead. The term elaborator mimicks the logic of the previous macro but executes it noticeably faster than before.

- [#16091](https://github.com/leanprover/lean4/pull/16091)
  avoids using an mvar for the type of a numlit when the type is known.

- [#16078](https://github.com/leanprover/lean4/pull/16078)
  improves the performance of elaborating long list literals.

- [#16047](https://github.com/leanprover/lean4/pull/16047)
  fixes equation lemmas of structurally recursive functions whose `rfl` proof was very expensive for the kernel to check. For example, generating `f.eq_2` for the following definition failed with kernel deep recursion, and `cbv`, `rw [f.eq_2]`, and `simp [f]` failed with it:
  ```lean
  def f : Nat → Nat → Nat
    | 0, x => x
    | n+1, x => f n ((x * 1103515245) % 5)
  ```

- [#16046](https://github.com/leanprover/lean4/pull/16046)
  fixes quadratic elaboration behavior for large string-literal equalities such as `theorem t : s = String.ofList l := rfl`.

- [#15959](https://github.com/leanprover/lean4/pull/15959)
  changes the parser of `return` to allow the term after `return` to start on a later line.

- [#15968](https://github.com/leanprover/lean4/pull/15968)
  speeds up `Environment.hasUnsafe`, which `mkAuxTheorem` runs on the type and value of every auxiliary theorem, such as each proof produced by `grind`. Imported constants are now read from the imported constant map, which is computed once per traversal. Before, `findAsync?` wrapped each of them in an `AsyncConstantInfo`, allocating the wrapper, two `Task`s and a `ConstantVal`.

- [#15955](https://github.com/leanprover/lean4/pull/15955)
  adds the `@[vcgen_simp]` attribute, which collects `Sym.simp` theorems for the `vcgen` tactic.

- [#15951](https://github.com/leanprover/lean4/pull/15951)
  makes normalization for the TC cache fail if a local instance is not a free variable.

- [#15855](https://github.com/leanprover/lean4/pull/15855)
  adds a `mkInstanceNameOfType` for determining the fully qualified name of an instance and makes delta deriving use it.

- [#15898](https://github.com/leanprover/lean4/pull/15898)
  makes `@[deprecated]` on `syntax`, `macro`, `elab`, `notation` and the mixfix commands deprecate the declared syntax, like `deprecated_syntax`.

- [#15942](https://github.com/leanprover/lean4/pull/15942)
  speeds up lookups of attribute and environment-extension data for imported declarations, such as reducibility status, tag attributes, parametric attributes and `MapDeclarationExtension.find?`. These lookups run very frequently during elaboration, and their results are unchanged.

- [#15921](https://github.com/leanprover/lean4/pull/15921)
  speeds up `Expr.consumeTypeAnnotations`, which the elaborator calls on the expected type of each application argument.

- [#15920](https://github.com/leanprover/lean4/pull/15920)
  speeds up `Expr.cleanupAnnotations`, which `match_expr` and `let_expr` call on the discriminant and after every argument they peel.

- [#15897](https://github.com/leanprover/lean4/pull/15897)
  ensures that the rules for macros which are deprecated are themselves not linted for deprecated declarations.

- [#15806](https://github.com/leanprover/lean4/pull/15806)
  allows users of the `deprecated_syntax` command to optionally specify a syntax transformation to produce a suggested replacement that will then be available as a code action.

- [#15879](https://github.com/leanprover/lean4/pull/15879)
  makes notations, macros and other checked quotations (``` ``(…) ```) report deprecated constants where they are defined, in addition to every place they are used.

- [#15858](https://github.com/leanprover/lean4/pull/15858)
  changes many places that erase free variables from the local instances to use the same functions, `LocalInstance.erase` and `LocalInstance.eraseAll` (a new function), and makes them not rely on the fact that `fvar` is a free variable. Local instances which are not free variables are useful e.g. for the new deriving framework (#15320) but should not be used in code that may revert or clear free variables.

- [#15863](https://github.com/leanprover/lean4/pull/15863)
  makes the elaboration of terms with many postponed type class problems, such as long arithmetic expressions over numerals, take linear instead of quadratic time. For example, `def bla : Nat := 2 ^ 3 * 8 + 2 ^ 3 * 8 + ...` with 80 summands now spends 65 ms in type class inference instead of 2.95 s.

- [#15824](https://github.com/leanprover/lean4/pull/15824)
  fixes `dsimp` and `simp` unfolding a function defined by mutual structural recursion when a `match` around a recursive call to another function of the group does not reduce. The resulting proof was accepted by the elaborator but rejected by the kernel.

- [#15737](https://github.com/leanprover/lean4/pull/15737)
  fixes `fun_cases` and `fun_induction` for a `match` whose discriminant appears in the type of another variable in the goal.

- [#15813](https://github.com/leanprover/lean4/pull/15813)
  makes the "deprecated syntax" linter report in places it previously missed.

- [#15371](https://github.com/leanprover/lean4/pull/15371)
  expands the condition for which the major of a recursor can be eta-expanded. Namely, subsingleton structures such as `And` should be eta-expanded in this situation.

- [#15103](https://github.com/leanprover/lean4/pull/15103)
  ensures `is_def_eq_proof_irrel` runs before reducing any potential proofs in `is_def_eq_core` rather than after. This is already the order in which things run in the elaborator, so no need for any changes there.

- [#15373](https://github.com/leanprover/lean4/pull/15373)
  eta-expands partial constructor applications.

- [#15682](https://github.com/leanprover/lean4/pull/15682)
  fixes `mkBindUnlessPure` to only run the continuation once, making sure that using `pure ()` doesn't elaborate everything afterwards twice.

- [#15740](https://github.com/leanprover/lean4/pull/15740)
  makes name resolution treat auxiliary local declarations (recursive references to the definition being elaborated, `let rec` and `where`) like the global declarations they represent, for both more consistent semantics and faster lookups.

- [#15738](https://github.com/leanprover/lean4/pull/15738)
  fixes a `(kernel) unknown constant` error for structurally recursive definitions where a recursive call appears as a `match` discriminant and an alternative of that `match` also recurses. Such definitions are now compiled using structural recursion.

- [#15318](https://github.com/leanprover/lean4/pull/15318)
  adds a `getEntriesWithKeys` function to `DiscrTree` that can be used to get all entries inside of a `DiscrTree` that have a specific key sequence.

- [#15710](https://github.com/leanprover/lean4/pull/15710)
  fixes the functional induction and cases principles for functions that match with a named pattern on a literal or a constructor without arguments (e.g. `n@5` or `b@true`), which were previously rejected by the kernel.

````

# Library

````markdown

- [#16487](https://github.com/leanprover/lean4/pull/16487)
  bakes monotonicity into `Lean.Order.PredTrans`. `PredTrans.mk f h` builds a transformer from a function `f` and a proof `h` that `f` is monotone, `PredTrans.apply` applies it, and `PredTrans.apply_mono` states its monotonicity. The `WP` class now carries only `trans` since monotonicity is baked in.

- [#16497](https://github.com/leanprover/lean4/pull/16497)
  fixes the bad performance on `Std.Http.Header.Name.ofString?` and `Header.Value.ofString?`.

- [#16417](https://github.com/leanprover/lean4/pull/16417)
  fixes twelve cases where the HTTP/1.1 client, the server or the URI printer did not follow RFC 9110, RFC 9112 or RFC 3986.

- [#16418](https://github.com/leanprover/lean4/pull/16418)
  reimplements `IO.Process.spawn` and the operations on `IO.Process.Child`. This fixes a number of bugs on all platforms, makes spawning much faster in processes that use a lot of memory, and makes `spawn` throw an error if the command cannot be started.

- [#16441](https://github.com/leanprover/lean4/pull/16441)
  makes all functions that later receive a `csimp` lemma `noncomputable`, to ensure that the slow versions are never used.

- [#16429](https://github.com/leanprover/lean4/pull/16429)
  makes the `Std.Http` server keep reading a client's upload before closing the connection when it rejects the request from its head alone, such as a `413` for a declared body over `maxBodySize` or a `400` for conflicting `Content-Length` fields. Previously the client could get a connection reset while still sending its body, and lose the response.

- [#16426](https://github.com/leanprover/lean4/pull/16426)
  makes closing a TCP socket on Windows cancel all pending writes, whichever thread issued them, as it already does on other platforms. Before this, a write to a peer that does not read could keep the socket open indefinitely if a different thread had issued it.

- [#16400](https://github.com/leanprover/lean4/pull/16400)
  fixes several `Std.Http` bugs:

  * A 2xx response to `CONNECT` has no framing fields or content and closes the connection.
  * `close` in `Connection` wins over `keep-alive` for every HTTP version, and empty list elements are accepted.
  * HTTP/1.0 requests are sent with `Content-Length`, and an HTTP/1.0 response with a transfer coding becomes a 500.
  * Request-target limits derive from `maxUriLength`, an overlong request line gets 414, and trailing CRLF at EOF is not a second request.
  * Chunk extensions with obs-text are ignored instead of failing the request, and leading zeros don't count toward the chunk-size limit.
  * `URI.Config` defaults are raised, and padded ports and 253-character hosts with a trailing dot parse.
  * `:` in a username is encoded, and a `RequestTarget` drops userinfo and the fragment.
  * `Status.isServerError` covers 600–999.
  * `waitShutdown` wakes every waiter, and reads stop at `maximumRecvSize` while a response streams.
  * The server lingers after an early response, a failing `onFailure` no longer skips cleanup, and late response bodies are closed.
  * `Body.Stream.close` keeps accepted bytes, and a cancelled `readAll` throws.
  AI Assisted (Claude)

- [#16366](https://github.com/leanprover/lean4/pull/16366)
  adds `Std.Async.Watchdog`, which enforces deadlines on a sequence of waits with a single background timer and cancels a `CancellationContext` with `.deadline` when a wait outlives its deadline.

- [#16380](https://github.com/leanprover/lean4/pull/16380)
  makes the HTTP/1.1 server report truncated request bodies to handlers and end connections whose peer stops reading. It adds `Config.writeTimeout` (default 30 seconds) and `close` on TCP sockets.

- [#16373](https://github.com/leanprover/lean4/pull/16373)
  fixes the HTTP/1.1 server closing a keep-alive connection right after a slow response write finishes.

- [#16372](https://github.com/leanprover/lean4/pull/16372)
  fixes the `Substring.Raw.splitOn` function which did not properly backtrack.

- [#16371](https://github.com/leanprover/lean4/pull/16371)
  fixes a number of typos and factual errors in the docstrings for `String` functions.

- [#16362](https://github.com/leanprover/lean4/pull/16362)
  makes an HTTP/1.0 request gets an HTTP/1.1 status line, a 205 response carries no content, the error responses the server writes itself carry a `Date` field and a short `text/plain` explanation, and a request with an unrecognized method or with a transfer coding other than `chunked` gets 501 instead of 400 or reaching the handler still coded.

- [#16360](https://github.com/leanprover/lean4/pull/16360)
  revamps input and output handling for processes as seen in `Process.output` and `Process.run`.

- [#16328](https://github.com/leanprover/lean4/pull/16328)
  fixes how `Std.Http` parses and prints URIs, request targets and `Host` values, and how `decideRedirect` resolves and follows redirects. Query values may contain `=`, a `Location: /` redirect goes to the root, and a printed URI reads back as the same URI. `decideRedirect` no longer takes the `onlySafeRedirects` and `responseVersion` parameters.

- [#16322](https://github.com/leanprover/lean4/pull/16322)
  makes the HTTP/1.1 server continue with the next request while a response is still being written, instead of waiting for each socket write, which makes pipelined and keep-alive requests about 15–30% faster.

- [#16358](https://github.com/leanprover/lean4/pull/16358)
  makes `Process.Child.kill` send `SIGTERM` or `SIGKILL` depending on a new parameter `force` defaulting to `true` (i.e. `SIGKILL`).

- [#15532](https://github.com/leanprover/lean4/pull/15532)
  marks `Dyadic.toRat` as a coercion, and tags various lemmas with `norm_cast`.

- [#16282](https://github.com/leanprover/lean4/pull/16282)
  fixes HTTP/1.1 message parsing, framing and connection handling in the client and server, and a few small `Std.Http` API issues.

- [#16080](https://github.com/leanprover/lean4/pull/16080)
  makes `Std.Http`'s HTTP/1.1 server answer a request whose request-target exceeds `maxUriLength` with `414 URI Too Long` however the request line is split into reads. A read that ended between byte `maxStartLineLength` and the parser's `maxUriLength` check gave `400 Bad Request`.

- [#15841](https://github.com/leanprover/lean4/pull/15841)
  makes `Std.Http`'s HTTP/1.1 parser wait for more input, instead of failing the message, when a read ends inside a chunk extension or a trailer field.

- [#16258](https://github.com/leanprover/lean4/pull/16258)
  fixes many cases where `Std.Time` could not parse the text it formatted with the same pattern, including `aaaa` (#16247) and `B` at night (#16248). It also makes `PlainDate.format` and `PlainDateTime.format` use their `locale` argument, keeps non-zero seconds in zone offsets, and corrects `Month.Ordinal.toDays` and `PlainDate.ofWallTime` before 1970.

- [#16266](https://github.com/leanprover/lean4/pull/16266)
  makes building and editing `Std.Http.Headers` several times faster by keeping header entries in an array that lookups scan.

- [#16079](https://github.com/leanprover/lean4/pull/16079)
  makes `Std.Http`'s URI and Host parsers read a host name that begins with an IPv4 address, such as `1.2.3.4-x.example`, as a name, instead of rejecting it.

- [#16265](https://github.com/leanprover/lean4/pull/16265)
  changes the encoding of HTTP structures to raw ByteArrays.

- [#15892](https://github.com/leanprover/lean4/pull/15892)
  makes the `String`-keyed `URI.Query` operations (`get`, `getD`, `find?`, `findAll`, `contains`, `erase` and `set`) find a query parameter by its decoded name, so a parameter is found whichever valid percent-encoding it arrived in. Previously, a name a browser percent-encoded, such as `a%3Ab` for a form field named `a:b`, could not be looked up as `"a:b"`, and `set` added a duplicate parameter instead of replacing it.

- [#15254](https://github.com/leanprover/lean4/pull/15254)
  preserves literal `+` characters in HTTP query keys and values by encoding them as `%2B`, so they remain distinct from spaces. For a query received as `a+b=1`, `get "a+b"` now returns `none`; use `get "a b"` for that space-containing name, or send `a%2Bb` to represent a literal plus.

- [#15323](https://github.com/leanprover/lean4/pull/15323)
  adds `withIsExclusive a k h`, which runs `k` on whether `a` is exclusive at runtime and is logically `k false`; the proof `h : k true = k false` keeps it sound. It lets safe code take different paths depending on sharing, for example to skip caching values that are referenced from at most one (owning) location.

- [#16225](https://github.com/leanprover/lean4/pull/16225)
  makes `Core.transform` preserve sharing of unchanged application nodes. Other expressions already remained shared before.

- [#16217](https://github.com/leanprover/lean4/pull/16217)
  adds `wf_preprocess` lemmas for the various higher-order `Option` functions.

- [#15269](https://github.com/leanprover/lean4/pull/15269)
  speeds up leading- and trailing-zero counting on bitvectors, including kernel reduction, while preserving support in `bv_decide`. Proofs that unfold these operations should instead use `BitVec.clz_eq_clzAuxRec` or `BitVec.ctz_eq_reverse_clz` to recover their previous definitions.

- [#15265](https://github.com/leanprover/lean4/pull/15265)
  adds `Nat.trailingZeros` and makes trailing-zero counting for `Nat` and `Int` efficient for arbitrary-precision values, speeding up dyadic normalization. Both operations return zero on zero, and `Int.trailingZeros` agrees with the natural-number operation on `natAbs`.

- [#16116](https://github.com/leanprover/lean4/pull/16116)
  adds `Vector.modify` to update an element with a function, returning the vector unchanged when the index is out of bounds.

- [#16119](https://github.com/leanprover/lean4/pull/16119)
  fixes `GenericFormat.parse` for patterns that rejected or misread what `GenericFormat.format` writes with the same pattern, and adds `*` and `/` by `Nat` and `Int` scalars to the `Std.Time` unit offsets and `Duration`. `O` and `OOOO` now accept a bare `GMT`, `xxxxx` accepts offsets without seconds, and `Z`, `ZZ` and `ZZZ` accept offsets with seconds. `PlainTime.toTime12Hour` no longer writes an hour that is off by one, such as `04:00:00 PM` for 15:00.`k`, `K` and `y` with a BC era now parse to the correct hour or year instead of silently returning a wrong value.

- [#15997](https://github.com/leanprover/lean4/pull/15997)
  makes `JsonNumber.toString` write a zero mantissa as `0` whatever the exponent.  With an exponent above 10 it wrote `0.e-k`, which is not JSON, so `Json.compress` output for such a number did not read back with `Json.parse`.

- [#15996](https://github.com/leanprover/lean4/pull/15996)
  makes `Json.parse` fail with a parse error on arrays and objects nested more than 10,000 levels deep, instead of overflowing the stack and aborting the process.

- [#16113](https://github.com/leanprover/lean4/pull/16113)
  makes kernel reduction of `String.toList` on a string literal take time linear in its length. Previously, `decide +kernel` on `s.toList.length = 400` took about 8 s, and literals of a few thousand characters hit the kernel's recursion limit.

- [#15160](https://github.com/leanprover/lean4/pull/15160)
  adds `Nat.extendedGcd`, returning a gcd and signed Bézout coefficients together with correctness and simplification lemmas.

- [#15077](https://github.com/leanprover/lean4/pull/15077)
  adds `UInt64.mulMod`, `UInt64.powMod`, and `UInt64.invMod?` for fixed-width modular arithmetic without overflowing intermediate products. `powMod` accepts an arbitrary `Nat` exponent, and `invMod?` returns `none` for a zero modulus or noncoprime inputs.

- [#15885](https://github.com/leanprover/lean4/pull/15885)
  adds `IO.FS.renameIfNew` which performs an atomic rename and errors if the destination already exists.

- [#16099](https://github.com/leanprover/lean4/pull/16099)
  removes the instances `instInhabitedForall` and `instInhabitedForallOfMonad`.

- [#16095](https://github.com/leanprover/lean4/pull/16095)
  introduces `Lean.UnionFind` as a compiler internal union find data structure. It features rank-based merging, path splitting, and efficient tracking of equivalence class members via cyclic pointers.

- [#16053](https://github.com/leanprover/lean4/pull/16053)
  adds benchmarks for many parts of Std.HTTP, from encoding, body streams, handlers, and the H1 machine to server and client behavior over TCP.

- [#16022](https://github.com/leanprover/lean4/pull/16022)
  speeds up `Json.compress`, `Json.pretty` and `Json.escape` on strings that contain non-ASCII characters, with unchanged output.

- [#15952](https://github.com/leanprover/lean4/pull/15952)
  adds the missing order instances for `Char`, namely `Min`/`Max` and the associated lawfulness properties.

- [#15936](https://github.com/leanprover/lean4/pull/15936)
  ensures that CXXFLAGS is passed to CaDiCaL's kitten component. This is necessary since the CaDiCaL 3.0 upgrade as it now includes kitten, a subsolver written in C.

- [#15653](https://github.com/leanprover/lean4/pull/15653)
  fixes several libuv-backed system and network functions:

  * `osGetPriority`, `osSetPriority`, `osGetGroup` and `getGroup` throw `IO.Error.invalidArgument` for a process or group id that does not fit the operating system's id type, instead of truncating it and acting on a different process or group. `osGetGroup` now takes a `Nat` instead of a `UInt64`.
  * `osGetGroup` throws `IO.Error.unsupportedOperation` on Windows for every id.
  * `osGetPasswd` decides whether the group id is missing from the group id itself rather than from the user id.
  * IPv6 addresses are converted correctly on big-endian hosts.
  * `IPv6Addr.ofString` rejects a `%` zone suffix instead of silently dropping it.
  * `getProcessTitle` returns titles of 512 bytes or more, and fails with `ENOBUFS` instead of exhausting memory when the process arguments were never set up, as in the `lean` binary.
  * `osGetenv` returns `none` for a name with an `=` after its first character instead of the value of the variable named by its prefix. Windows variables such as `=C:` are still found.
  * `IO.Process.Child.pid` no longer leaks the `Child` object.
  * The libuv runtime sources no longer use `using namespace std` in headers, give their file-local helpers internal linkage, and declare the timer functions on all builds.

- [#15294](https://github.com/leanprover/lean4/pull/15294)
  adds union/intersection emptiness distributivity lemmas:

  ```lean
  -- isEmpty_union_inter / isEmpty_inter_union
  ((m₁ ∪ m₂) ∩ m₃).isEmpty = ((m₁ ∩ m₃).isEmpty && (m₂ ∩ m₃).isEmpty)
  (m₁ ∩ (m₂ ∪ m₃)).isEmpty = ((m₁ ∩ m₂).isEmpty && (m₁ ∩ m₃).isEmpty)

  -- union_inter_equiv_empty_iff / inter_union_equiv_empty_iff
  ((m₁ ∪ m₂) ∩ m₃) ~m ∅ ↔ (m₁ ∩ m₃) ~m ∅ ∧ (m₂ ∩ m₃) ~m ∅
  (m₁ ∩ (m₂ ∪ m₃)) ~m ∅ ↔ (m₁ ∩ m₂) ~m ∅ ∧ (m₁ ∩ m₃) ~m ∅

  -- union_inter_eq_empty_iff / inter_union_eq_empty_iff (extensional variants)
  (m₁ ∪ m₂) ∩ m₃ = ∅ ↔ m₁ ∩ m₃ = ∅ ∧ m₂ ∩ m₃ = ∅
  m₁ ∩ (m₂ ∪ m₃) = ∅ ↔ m₁ ∩ m₂ = ∅ ∧ m₁ ∩ m₃ = ∅
  ```

- [#15562](https://github.com/leanprover/lean4/pull/15562)
  makes `grind` terminate on goals that take the `min` of two identical `List.findIdx` terms by giving `List.min_findIdx_findIdx` an explicit `grind_pattern`. It is instantiated only for distinct predicates and only on terms of low generation.

- [#14753](https://github.com/leanprover/lean4/pull/14753)
  makes `vcgen … with finish` prove that a loop measure decreases when the measure lands in a pair or a nested pair of well-founded types. For example, a `while` loop that counts `i` down and resets `j` closes with `.ofMeasure fun (i, j) => (i, j)` and `with finish`.

- [#15317](https://github.com/leanprover/lean4/pull/15317)
  adds `Bool.dand`, the dependent version of `Bool.and`, and `Ordering.dthen`, the dependent version of `Ordering.then`, along with new lemmas both for the non-dependent and for the dependent versions. Additionally, it adds a `Decidable` instance that's useful for case distinction in proofs about functions like `Ordering.dthen`. These primitives will be useful for implementing the new `BEq` / `Ord` / `DecidableEq` deriving handlers in #14929.

- [#15603](https://github.com/leanprover/lean4/pull/15603)
  adds `owned_ref` a helper that owns lean objects and helps avoiding hundreds of `lean_inc` and `lean_dec` inside the LibUV codebase

- [#15711](https://github.com/leanprover/lean4/pull/15711)
  adds order instances on `String.Slice`.

- [#14892](https://github.com/leanprover/lean4/pull/14892)
  redefines `WellFounded.fix`, `WellFounded.fixF` and `WellFounded.recursion` so that they no longer eliminate an accessibility proof into data, and adds `Acc.rec'`, `Acc.recOn'`, `Acc.ndrec'` and `Acc.ndrecOn'` for code that needs to do so itself. Fixpoint equations and compiled code are unchanged, and `Acc.rec` is untouched. The one visible change is that well-founded definitions now depend on `Classical.choice`, which `#print axioms` reports.

- [#15598](https://github.com/leanprover/lean4/pull/15598)
  introduces the `uv_buf_t` array for TCP and UDP sends on the stack, and makes send and recv fail with an invalid-argument error for a buffer size of 4 GiB or more, instead of letting the length wrap to 32 bits.

- [#15680](https://github.com/leanprover/lean4/pull/15680)
  makes `WPMonad.withFrameClosure` universe polymorphic. It now accepts a monad `m : Type v → Type w` and a resource `R : Type t` in any universe, for example `StateT (ULift.{1} Nat) Id`.

````

# Tactics

````markdown

- [#16532](https://github.com/leanprover/lean4/pull/16532)
  makes `simp` faster on terms with long projection chains, such as the ones in the proof of the unfold theorem (`f.eq_def`) of a function defined by structural recursion over a large nested inductive type.

- [#16507](https://github.com/leanprover/lean4/pull/16507)
  makes `vcgen [f]` linear in the number of join points of `f`. Making the spec for the unfold equation of `f` zeta-reduced its right-hand side, the whole program, which copied each join point into all its jumps. For a chain of 16 `if`s that reassign a mutable variable, `vcgen +jp [chain]` now takes 28 ms instead of 3.2 s.

- [#16525](https://github.com/leanprover/lean4/pull/16525)
  changes how the `grind` commutative ring solver picks the basis equation used to simplify a monomial. It now uses the equation with the fewest terms among those whose leading monomial divides the monomial. This keeps intermediate polynomials smaller on some problems. On the ring tests and benchmarks the output is unchanged and the total instruction count drops by 0.5%, with `grind_ring_5` 9.3% faster.

- [#16504](https://github.com/leanprover/lean4/pull/16504)
  fixes process aborts with `INTERNAL PANIC: Nat.pow exponent is too big` in `simp`, `grind`, `cbv`, `bv_decide` and `bv_normalize`. They happened on goals containing a `BitVec` literal of width `2^32` or more, such as `example (x : BitVec 5000000000) : 1#5000000000 = x := by simp`, and on powers with an exponent of `2^32` or more when `exponentiation.threshold` was raised above `2^32`. These terms are now left unevaluated. The examples from #15786 now pass.

- [#16499](https://github.com/leanprover/lean4/pull/16499)
  improves `grind`'s ring solver on commutative rings that do not implement `NoNatZeroDivisors`, where it can now derive equalities it could not derive before. Example:

  ```lean
  example [CommRing α] (x y : α) (h₁ : 2*x = y) (h₂ : 3*x = y + 1) : x = 1 := by
    grobner
  ```

- [#16468](https://github.com/leanprover/lean4/pull/16468)
  adds a new tactic called `epr` for solving EPR problems using a BitVec encoding combined with `bv_decide`. This tactic will be particularly useful for applications in protocol verifiers such as [Veil](https://github.com/verse-lab/veil).

- [#16456](https://github.com/leanprover/lean4/pull/16456)
  implements Z3-style instantiation sets for MBQI based model-checking.

- [#16455](https://github.com/leanprover/lean4/pull/16455)
  introduces a Paradox-style union-find based subsort analysis to `bv_decide`'s EPR support. It operates in two steps:
  1. Infer subsorts using a normal union-find algorithm and at the same time detect (non)-monotone sorts using the syntactic positive equality criterion.
  2. For all monotone sorts that have more than one syntactic subsort do split them up into actual subsorts in the EPR problem.

- [#16453](https://github.com/leanprover/lean4/pull/16453)
  implements some symmetry breaking for the EPR encoding used in `bv_decide`, we provide 3 different modes:
  - `off`, no symmetry breaking, provide the minimum sound encoding. That is, every sort element gets assigned a  `BitVec` variable that is unconstrained besides the maximum sort cardinality.
  - `simple`, the default. Instead of leaving them unconstrained we say that the bitvec encoding of element `a_i` must be `<= i`. This is similar to one of Paradox's symmetry breakers introduced in "New Techniques that Improve MACE-style Finite Model Finding"
  - `full`. This introduces as much symmetry breaking as possible, in addition to `simple` this introduces the fact that if `a_i != i` then all `a_j` with `j > i` will also have `a_j != i`.

- [#16452](https://github.com/leanprover/lean4/pull/16452)
  introduces a basic EPR solver to `bv_decide`. It detects type parameters that act like EPR sorts, encodes them into a BitVec representation and finally solves the problem using a naive MBQI loop. Follow up work will provide a convenient top level tactic for this.

- [#16484](https://github.com/leanprover/lean4/pull/16484)
  makes `vcgen +jp` state the equation of a join-point parameter once, above the disjunction over the jumps, if every jump passes the same term for it. For a join point that many jumps reach in the same state `t`, the join hypothesis is now `s = t ∧ (d₁ ∨ … ∨ dₙ)`, so each disjunct `dᵢ` has one equation fewer.

- [#16414](https://github.com/leanprover/lean4/pull/16414)
  fixes a stack overflow in `sym =>` when `apply` unifies a metavariable with a term that contains it. For example, `apply Eq.refl` on the goal `?n = ?n * ?n` used to assign `?n := ?n * ?n`, and now fails with "rule is not applicable".

- [#16346](https://github.com/leanprover/lean4/pull/16346)
  adds the config options `simpMaxSteps` and `simpMaxDischargeDepth` to `vcgen`. They set `maxSteps` and `maxDischargeDepth` of every `Sym.simp` run of the simp step, as the fields of a `register_sym_simp` variant do. The defaults are those of `Sym.Simp.Config`.

- [#16316](https://github.com/leanprover/lean4/pull/16316)
  improves `cbv` handling of match equations. Previously `cbv`, when encountering match expressions would try first to use matcher equations using `Sym` machinery for theorem rewrite, with no discharger enabled, before falling back to `whnf`. Now, we try a discharger that can deal with overlap hypotheses, by applying `cbv` to each of the arguments of the overlaph hypothesis. Literals nested inside constructor pattterns, still fall back to `whnf`, since `Sym.simp` has no simproc  for constructor injectivity yet.

- [#16341](https://github.com/leanprover/lean4/pull/16341)
  fixes the `grind` internal error "linarith term has not been internalized" on negative numerals such as `-1 : T`, where `T` unfolds to `Int` and has an ordered `IntModule` instance but no `CommRing` instance.

- [#16319](https://github.com/leanprover/lean4/pull/16319)
  changes the proofs produced by `lia`, `grind`, and the `Nat` offset simprocs so that the kernel no longer has to evaluate their arithmetic atoms. Before, for goals containing terms such as `(x + 4294967295) % 4294967296`, the kernel ran in unary `Nat` arithmetic and failed to check the proofs in practice. Closes #16311.

- [#16310](https://github.com/leanprover/lean4/pull/16310)
  makes `vcgen` keep its goals maximally shared, and runs the `vcgen` and `mvcgen` tests with `sym.debug` set, so the test suite catches a change that breaks a `SymM` invariant.

- [#16291](https://github.com/leanprover/lean4/pull/16291)
  adds the attribute `@[vcgen_rintro]`, which tells `vcgen` how to destructure a binder while it introduces the binders of a goal, like a fixed `rintro` pattern. For example, with

- [#16303](https://github.com/leanprover/lean4/pull/16303)
  makes `vcgen` keep the value of a `let` or `have` in the program as written, as before #16292, so that `vcgen +jp` is as fast as before. For example, `have x := 0 + k; pure (x + x)` leaves `x : Nat := 0 + k` in the VC under `vcgen simp [Nat.zero_add]`.

- [#16292](https://github.com/leanprover/lean4/pull/16292)
  makes `vcgen` step past a `let` or `have` at the head of the right-hand side of an entailment `pre ⊑ rhs`. A spec such as

- [#16298](https://github.com/leanprover/lean4/pull/16298)
  fixes `grind linarith` failing with the internal error "structure is not a preorder" on `≤` and `<` facts over types with an order but no `OrderedAdd` instance, such as `Fin n` and `BitVec w`. For example, `(x : Fin 3) (h : x < x) : False` is now proved by `grind_linarith`, and the satisfiable `(x y : Fin 3) (h₁ : x < y) (h₂ : y + 1 < x + 1) : False` now fails with a regular `grind` failure message.

- [#16297](https://github.com/leanprover/lean4/pull/16297)
  fixes a kernel type mismatch on `eq_of_dvd_ediv` in proofs produced by `lia` and `grind`, for goals such as `x % 3 ≤ 2 * x % 3 → 4 * x % 3 ≤ 2 * x % 3`.

- [#16294](https://github.com/leanprover/lean4/pull/16294)
  fixes the internal error `mkNoConfusion: No manifest constructors` in `contradiction` on hypotheses such as `h : 0 + 0 = 1`.

- [#16261](https://github.com/leanprover/lean4/pull/16261)
  makes `vcgen` report an error when the goal is a `Std.Do` triple or entailment, and when `Std.WP` is not imported. The error message comes with a hint what to do. The `Std.Do` error asks the user to restate the goal with the definitions from `Std.WP`, and to add `import Std.WP` when it is missing.

- [#16280](https://github.com/leanprover/lean4/pull/16280)
  makes `vcgen` rewrite a `match` on a string literal discriminant in its verification conditions, e.g. `match "done" with | "start" => False | "done" => True | _ => False` reduces to `True`.

- [#16264](https://github.com/leanprover/lean4/pull/16264)
  fixes a kernel error in the `Sym.simp`-based arithmetic normalizer on types of characteristic `1`, such as `Fin 1`. The normalizer now leaves these types as written.

- [#16263](https://github.com/leanprover/lean4/pull/16263)
  fixes a `grind.debug` panic in `checkEqc` on goals such as `x = 1 → -x = -1` for `Int8`, `Int16`, `Int32`, and `Int64`.

- [#16226](https://github.com/leanprover/lean4/pull/16226)
  changes `bv_normalize` to explicitly eliminate `BitVec.cast` via equational rewriting with `BitVec.cast_eq` as opposed to `rfl`. Michael Tautschnig noticed that eliminating via `rfl` forces the kernel to evaluate the term being cast which is potentially expensive.

- [#16181](https://github.com/leanprover/lean4/pull/16181)
  changes `vcgen` so that `reduceHead?` substitutes an assigned metavariable at the head of a term and beta-reduces, and `instantiateGoal?` reduces the head of the entailment with it, so a goal whose right-hand side holds unassigned metavariables below the head is no longer instantiated in full at every step.
  Another consequence is that a `match` postcondition applied to a constructor yields one verification condition per conjunct, which renumbers the `case vcN` tags of such goals.

- [#16241](https://github.com/leanprover/lean4/pull/16241)
  fixes `sym =>` tactics that failed or made no progress on goals mentioning metavariables assigned after the goal was created, e.g., by `apply` or by solving a sibling goal. This affected `intro`, `apply`, `simp`, `dsimp`, `let_to_have`, `lift_lets`, and local instance registration.

- [#16222](https://github.com/leanprover/lean4/pull/16222)
  uses a CaDiCaL terminator based on a Lean `BaseIO Bool` callback for incremental solves instead of spawning a second thread that kills the solving process if it takes too long.

- [#16069](https://github.com/leanprover/lean4/pull/16069)
  introduces a generic incremental bitvector solver into bv_decide. For now this is only used to feed the BitVec component of the CEGAR loop but it will have additional applications in the future.

- [#16212](https://github.com/leanprover/lean4/pull/16212)
  fixes `vcgen +jp` for a join point nested in a branch of another join point. Before, such a program failed with "vcgen +jp: unexpected binder" or "vcgen +jp: missing witness".

- [#16221](https://github.com/leanprover/lean4/pull/16221)
  disables CaDiCaL's lucky pass in incremental mode. At the beginning of each incremental solve it visits the whole problem trying an all true/all false assignment. This is quadratic if we sequence many incremental solves.

- [#16102](https://github.com/leanprover/lean4/pull/16102)
  adds the lattice simplifications of `simp` and `grind norm` to the `@[vcgen_simp]` set, so `vcgen` states verification conditions at carrier `Prop` with `∧`, `∨`, `∃`, `∀` and `→` in place of `⊓`, `⊔`, `⨆`, `⨅` and `⊑`. The set also eliminates the index of a supremum when an equation determines it. For example, from the precondition `fun s => s = 3`, the postcondition `fun _ s => ⨆ n : Nat, ⌜s = n⌝ ⊓ ⌜n < 5⌝` leaves no verification condition, and the postcondition `fun _ _ => ⨆ n : Nat, ⌜n < 5⌝` leaves `∃ n, n < 5`.

- [#16216](https://github.com/leanprover/lean4/pull/16216)
  makes the join point hypotheses of `vcgen +jp` smaller. For two sequential `if`s that modify the state, the hypothesis of the second join point is now `b 0 = true ∧ s = s₀ + 1 ∨ ¬b 0 = true ∧ s = s₀ + 2`. Before, it also contained the equation `x = (PUnit.unit, s₀ + 1).fst` for the result of the first `if`.

- [#16192](https://github.com/leanprover/lean4/pull/16192)
  makes `vcgen` instantiate assigned metavariables in hypothesis types before introducing them to the local context. This results in more Sym term sharing and more reliable `vcgen` operation in general.

- [#16207](https://github.com/leanprover/lean4/pull/16207)
  fixes a panic and a kernel error in `grind` with the new normalizer (`backward.grind.normalizer false`) when the local context contains a `let`-variable, as in `(h : a * b = c) : let x := a * b; x = c` after `intro x`.

- [#16204](https://github.com/leanprover/lean4/pull/16204)
  fixes `grind` failing on goals that mix a cast from `Nat` and a cast from `Int` into the same ring, such as `(m : Int) (k : Nat) (h : m = k) : (m : R) = (k : R)`. With the new normalizer (`backward.grind.normalizer false`) this also affected goals written as `(m : R) = ((k : Int) : R)`, because the normalizer rewrites `((k : Int) : R)` to `(k : R)`.

- [#16203](https://github.com/leanprover/lean4/pull/16203)
  makes `Sym` handle `let` and `have` declarations. Backward rules (`sym => apply`, `vcgen` specs and unfold rules) now keep the `have`s of their hypotheses in the new goals instead of copying the values into every use. Matching and unification now unfold `let`s and `have`s in the goal instead of failing or reporting "unexpected let-declaration term". As a result, `vcgen +jp [f.eq_def]` shares the join points of `f`: with `n` sequential `if`s it produces 2 goals instead of 2ⁿ⁺¹ (part of #16122). A `have` in the program can now appear in a verification condition as a let-variable.

- [#16199](https://github.com/leanprover/lean4/pull/16199)
  introduces a cache for bitblasting of boolean substructure in bv_decide. Note that at the bit/AIG level this was already being cached but we never the less repeatedly traversed the expressions before. This has so far not been an issue as our problems mostly consisted of BitVec expressions which is not necessarily the case anymore.

- [#16193](https://github.com/leanprover/lean4/pull/16193)
  fixes a kernel error in `grind` on `match` expressions with overlapping patterns where a literal in the discriminant meets a pattern variable, e.g. `p (3, false)` with `p` defined by `match s with | (_, true) => 0 | _ => 1`.

- [#16167](https://github.com/leanprover/lean4/pull/16167)
  fixes `grind` failing to prove `(m : R) = (k : R)` for a ring `R` such as `ZMod n` when the facts force `m = k` but `lia` does not derive it, e.g., from `m ≤ k`, `k ≤ m + 1` and `2 ∣ k - m`. This fixes a Mathlib regression introduced by #16161.

- [#16165](https://github.com/leanprover/lean4/pull/16165)
  makes the `Sym.Arith` normalizer push `Nat` and `Int` casts through `+`, `*` and powers with a literal exponent, and for `Int` also through `-`, negation and casts from `Nat`. As a result, `(m + n) • x = m • x + n • x` and `((m * n : Nat) : R) = ((n * m : Nat) : R)` are now proved by `Sym.simp` with `arith`, and by the `grind` normalizer. Truncated `Nat` subtraction, division and remainder are still treated as atoms.

- [#16164](https://github.com/leanprover/lean4/pull/16164)
  fixes `sym => dsimp` timing out on large, deeply nested terms that `sym => simp` handles quickly.

- [#16163](https://github.com/leanprover/lean4/pull/16163)
  makes `Sym.simp` reduce a `match` whose discriminant is a value such as a `String`, `Nat` or `Char` literal, e.g. `match "b" with | "a" => 1 | "b" => 2 | _ => 3`. This affects `sym => simp` and the `Sym.simp`-based `grind` normalizer, which previously left such terms unchanged.

- [#16162](https://github.com/leanprover/lean4/pull/16162)
  fixes `Sym` pattern matching (used by `Sym.simp`, `Sym.dsimp` and `apply` in `sym` mode) for theorems whose universe variables first occur inside a `max` level, such as rewriting `@id (α × β) p` with `id_prod {α : Type u} {β : Type v} (p : α × β) : @id (α × β) p = p` when `β : Type (max v w)`. Previously, the matcher guessed the universe variables by splitting the `max` argument by argument, and failed when a later occurrence such as `Prod.{u, v}` required different values.

- [#16161](https://github.com/leanprover/lean4/pull/16161)
  fixes `grind` model-based theory combination making useless case splits on `x = y` for `Nat` terms such as `3 * x`, `x / 3` and `x % 3`, which it treated as nonlinear because only `Int` numerals were recognized.

- [#16159](https://github.com/leanprover/lean4/pull/16159)
  makes the `Sym.simp`-based `grind` normalizer handle integer powers with a literal exponent in a field. For example, `2 ^ (-1 : Int)` becomes `2⁻¹` and `a ^ (2 : Int)` becomes `a ^ 2`, so they take part in the polynomial normal form. The legacy normalizer only evaluates a numeral power inside `⁻¹` or `/`.

- [#16158](https://github.com/leanprover/lean4/pull/16158)
  fixes universe level unification in `Sym`, which could assign a universe level metavariable to a level containing itself (causing a stack overflow) or overwrite an existing assignment (leaving universe metavariables in the proof).

- [#16157](https://github.com/leanprover/lean4/pull/16157)
  fixes `grind` with the `Sym.simp` normalizer on goals that use `/` in a field of nonzero characteristic. For example, `a / c = b → b = a * c⁻¹` over `[Field α] [IsCharP α 7]` now closes, as it does with the legacy normalizer.

- [#16156](https://github.com/leanprover/lean4/pull/16156)
  makes the `Sym.simp` arithmetic normalizer, used by `sym => simp` and the `Sym.simp`-based `grind` normalizer, prove ground `Nat`, `Int` and `Rat` subterms such as `2 ^ 64` or the `2 + 3` in `a + (2 + 3)` by `rfl` instead of a ring-reflection certificate, which reduces kernel checking time.

- [#16152](https://github.com/leanprover/lean4/pull/16152)
  reduces the fixed cost of every `grind` and `lia` call by about 25 µs.

- [#16147](https://github.com/leanprover/lean4/pull/16147)
  replaces the `grind` option `splits` with `branches`, which limits the total number of branches that case splitting may create during a proof search (default 1024). Previously, `grind`, `lia`, and the related tactics allowed at most 9 case splits along each branch of the search, so a goal with a long chain of cheap case splits failed even when its proof was tiny. For example, a hypothesis `x ≤ 0 ∨ 100 ≤ x ∨ x = 2 ∨ x = 4 ∨ … ∨ x = 36` whose disjuncts are each refuted immediately needed 17 case splits in a row and exceeded the limit. Such goals are now proved with the default configuration, while the total amount of case splitting stays bounded.

- [#16143](https://github.com/leanprover/lean4/pull/16143)
  makes `lia` (and `grind`) assert the linear bounds that hold in every disjunct of a disjunction, instead of finding them by case splitting. For example, `(b = true ∧ y = x + 1) ∨ (b = false ∧ y = x + 2)` implies `x + 1 ≤ y` and `y ≤ x + 2`. Goals produced by `vcgen +jp` (#16122) carry one such disjunction per join point. On them, `lia` explored all 2ⁿ cases and failed for `n ≥ 10` at the `splits` threshold. It now solves them in time linear in `n`.

- [#16141](https://github.com/leanprover/lean4/pull/16141)
  fixes an exponential slowdown in `grind` on terms whose types are equal only modulo the E-graph, such as `Fin (a.set! i v).size` and `Fin a.size`, or the bounds proofs `j < (a.set! i v).size` and `j < a.size` in array accesses.

- [#16131](https://github.com/leanprover/lean4/pull/16131)
  makes `rw` and other tactics based on `kabstract` faster on goals with shared subterms.

- [#16130](https://github.com/leanprover/lean4/pull/16130)
  makes `rw` faster on large goals by type checking only the parts of the motive that depend on the rewritten occurrences.

- [#16129](https://github.com/leanprover/lean4/pull/16129)
  speeds up `grind` on goals with many nested case splits. Building the proof of a case split no longer traverses the proofs of the case splits below it.

- [#16124](https://github.com/leanprover/lean4/pull/16124)
  fixes a kernel "loose bound variables" error in `sym =>` when two `have` or `let` expressions differ only in their type.

- [#16118](https://github.com/leanprover/lean4/pull/16118)
  adds support for propositional variables in bv_decide even when they are not wrapped in `decide p = true`.

- [#16106](https://github.com/leanprover/lean4/pull/16106)
  makes `vcgen` discharge the hypotheses of conditional theorems in its simp set. The simp set (`@[vcgen_simp]` and `vcgen simp [...]`) now rewrites with the discharger `Sym.Simp.dischargeSimpSelf`.
  Example: `Mem.loadInt_storeInt (hw : n ≤ 2 ^ w) : (m.storeInt a n v).loadInt a n = some (Int.ofBytes (Int.toBytes n v))`. At a call site `n` and `w` are literals, and ground evaluation proves `8 ≤ 2 ^ 64`.

- [#16114](https://github.com/leanprover/lean4/pull/16114)
  fixes an `unknown free variable` error when `lia` closes a subgoal of `cases_next` in `grind` interactive mode, e.g., `grind => cases_next; all_goals finish`.

- [#16112](https://github.com/leanprover/lean4/pull/16112)
  fixes an internal `grind` error ("term has not been internalized") caused by structure eta.

- [#16094](https://github.com/leanprover/lean4/pull/16094)
  makes `vcgen` leave out a lifted equation `x = t` after it substitutes `t` for `x`, when no other hypothesis mentions `x`. The equation then carries no information, and the verification conditions no longer show it. For example, the verification condition of a program that throws `"x"` against the postcondition `fun e => e = "x" ∨ e = "y"` was

- [#16093](https://github.com/leanprover/lean4/pull/16093)
  lets a `@[frameproc]` name a theorem `framesThm?` that proves `WP.Frames op x F P` for every program `x`, frame `F` and guard `P`. `vcgen` discharges the frame condition of each framed call with that theorem, so the frame condition no longer becomes a verification condition.

- [#16092](https://github.com/leanprover/lean4/pull/16092)
  makes `try?` treat a candidate tactic that exceeds the maximum recursion depth as having failed, as it already did for the heartbeat limit, instead of aborting with that error. For example, `impossible by decide` on a goal quantifying over `UInt64` hits the recursion limit and previously made the whole `try?` call fail.

- [#16085](https://github.com/leanprover/lean4/pull/16085)
  reduces the time `grind` spends in its order solver when many terms are related by fixed offsets, such as numerals in an ordered ring. Adding `n` numerals used to take time cubic in `n` and now takes quadratic time. For example, a goal with 300 hypotheses `yₖ = k` over `Int` now takes 0.44 s instead of 1.86 s.

- [#16075](https://github.com/leanprover/lean4/pull/16075)
  makes the `grind` failure message reported without `+verbose` list the thresholds that were reached, as configuration items the user can raise. For example, `lia` now fails with `` `lia` has failed after reaching the threshold `(splits := 9)`, use `+verbose` to obtain diagnostic information ``. This applies to `instances`, `ematch`, `splits`, `gen`, `ringSteps`, and `liaSteps`, and to all tactics built on `grind`, such as `lia`, `grind_order`, `grind_linarith`, and `grobner`.

- [#16073](https://github.com/leanprover/lean4/pull/16073)
  shortens the error message reported when `grind` fails without `+verbose`. Instead of printing the failing goal, the message is now `` `<tactic>` has failed, use `+verbose` to obtain diagnostic information ``, where `<tactic>` is the tactic the user invoked (e.g., `lia`, `grind_order`, `grind_linarith`, `grobner`, `sym`) rather than always `grind`. With `+verbose`, the goal and diagnostics are still reported, and the header also names the invoked tactic.

- [#16072](https://github.com/leanprover/lean4/pull/16072)
  fixes a `grind` panic in `mkCongrDefaultProof` when using `Function.Injective` hypotheses together with case splits (#16059).

- [#16056](https://github.com/leanprover/lean4/pull/16056)
  fixes `grind?` and `finish?` dropping case-splits from their generated scripts when the proof does not use the case-split, but the rest of the script does. For example, a case-split may introduce a term that E-matching uses later. The scripts then failed to replay, and `grind?` dropped theorems from its `grind only` suggestions.

- [#16050](https://github.com/leanprover/lean4/pull/16050)
  fixes `grind?` generating a `· done` step for a case-split alternative that `grind` closes while introducing its hypotheses. The step failed when the script was replayed, which also made `grind?` drop theorems from its `grind only` suggestions.

- [#16057](https://github.com/leanprover/lean4/pull/16057)
  makes `grind?` check each suggested tactic before showing it. Previously, only the generated `grind =>` script was checked, and it was suggested even when the check failed. Suggestions that do not close the goal are now reported in a warning instead of being suggested, and if none of them works, `grind?` suggests `grind` with the original configuration and parameters. `try?` uses the same check for the `grind only` suggestions it shows.

- [#16054](https://github.com/leanprover/lean4/pull/16054)
  fixes `grind?` suggesting `grind only [...]` calls that fail because they need more E-matching rounds than the `ematch` limit allows. The search that found the proof may have performed more rounds because case-splits reset the round counter, even when those case-splits were not needed by the proof and were removed from the generated script. The suggestions now set the `ematch` limit, e.g., `grind (ematch := 6) only [...]`, when the generated script performs more rounds between case-splits than the limit.

- [#16052](https://github.com/leanprover/lean4/pull/16052)
  fixes `instantiate only [!thm]` ignoring the `!` modifier when `thm` is already registered as a `grind` theorem, and using its registered patterns instead of the minimal indexable ones. Generated scripts using `!thm` then failed to replay, and `grind?` dropped `thm` from its `grind only` suggestions.

- [#16051](https://github.com/leanprover/lean4/pull/16051)
  fixes `grind?` and `finish?` dropping solver steps such as `ring` and `lia` that make progress without closing the goal or propagating facts. Later steps may depend on that progress, so the generated script failed to replay, and `grind?` also dropped theorems from its `grind only` suggestions.

- [#16048](https://github.com/leanprover/lean4/pull/16048)
  fixes `grind?` producing scripts that pick the wrong case-split when local variables are shadowed, which also made it drop theorems from its `grind only` suggestions.

- [#16042](https://github.com/leanprover/lean4/pull/16042)
  fixes `grind?` dropping `[grind inj]` theorems from its `grind only` suggestions, which then failed when pasted.

- [#16041](https://github.com/leanprover/lean4/pull/16041)
  fixes anchors such as `#c0c6` in `grind only [...]` being parsed as terms when a `#` prefix notation is in scope, which made `grind?` suggestions fail. A `#` notation applied to a hexadecimal identifier can still be written with parentheses, e.g. `grind only [(#ab)]`.

- [#16040](https://github.com/leanprover/lean4/pull/16040)
  fixes `instantiate only [...]` never firing instances of theorems registered with `grind_pattern ... where guard ...`, which made `grind?` drop such theorems from its suggestions.

- [#15961](https://github.com/leanprover/lean4/pull/15961)
  makes `vcgen` simplify the verification conditions it produces, together with the hypotheses and program states along the way. By default, it uses the theorems tagged `@[vcgen_simp]` and evaluates ground terms such as `41 + 1`, so that `(a, b).snd = 7` becomes `b = 7` and a branch whose condition evaluates to `False` closes at once. `vcgen simp [thm, h, *]` adds theorems for one call and replaces `simplifying_assumptions [...]`. `vcgen -simp` turns simplification off.

- [#15999](https://github.com/leanprover/lean4/pull/15999)
  makes kernel checking of `Sym.simp`'s arithmetic normalization and of `grind`'s ring solver proofs much cheaper over few variables. Polynomial identities are checked by evaluating both sides at one point, instead of normalizing them in the kernel.

- [#15995](https://github.com/leanprover/lean4/pull/15995)
  makes kernel checking of `Sym.simp`'s arithmetic normal forms and identities, and of `grind`'s Gröbner chains, cheaper. It uses polynomials whose monomials are packed into natural numbers (`Grind.CommRing.PPoly`, in the new file `Init/Grind/Ring/Packed.lean`).

- [#15990](https://github.com/leanprover/lean4/pull/15990)
  makes kernel checking of `Sym.simp` arithmetic normalization much cheaper for terms with large products, such as `(a + b + c + d + e) ^ 7 = (a + b + c + d + e) ^ 3 * (a + b + c + d + e) ^ 4`.

- [#15988](https://github.com/leanprover/lean4/pull/15988)
  makes kernel checking of `Sym.simp` arithmetic relations and identities cheaper.

- [#15986](https://github.com/leanprover/lean4/pull/15986)
  makes kernel checking of `Sym.simp` arithmetic normalization much cheaper for long sums and large polynomials.

- [#15984](https://github.com/leanprover/lean4/pull/15984)
  speeds up kernel checking of the certificates produced by the `arith` simproc of `Sym.simp`, and adds benchmarks for the simproc.

- [#15983](https://github.com/leanprover/lean4/pull/15983)
  makes kernel checking of `cutsat` proofs and of the `simp +arith` steps that `grind` uses to normalize hypotheses cheaper. On the `lia` benchmarks, kernel checking becomes 38–46% cheaper.

- [#15981](https://github.com/leanprover/lean4/pull/15981)
  makes kernel checking of `grind`'s semiring, field and `linarith` proofs cheaper. It replaces definitions that the kernel reduces through `brecOn`, structural recursion or derived `BEq` instances with recursor-based ones.

- [#15967](https://github.com/leanprover/lean4/pull/15967)
  makes `lia`, `grind` and `Sym.simp`'s `arith` simproc cheaper by answering the algebraic structure queries of `Sym.Arith` classification for `Int` and `Nat` from a table, without type class resolution. Each `grind` goal classified these types again, issuing about 20 queries that the instance cache did not carry over between goals.

- [#15970](https://github.com/leanprover/lean4/pull/15970)
  makes kernel checking of `grind ring` proofs much cheaper, especially for long Gröbner basis derivations.

- [#15969](https://github.com/leanprover/lean4/pull/15969)
  makes `grind` ring proofs smaller by building the expression of each distinct monomial and coefficient once.

- [#15944](https://github.com/leanprover/lean4/pull/15944)
  speeds up kernel checking of ring and field certificates produced by `grind` and `Sym.simp`.

- [#15943](https://github.com/leanprover/lean4/pull/15943)
  makes the kernel check the certificates of the `grind` ring solver and of the `Sym.simp` arithmetic normalizer about twice as fast. It also adds benchmarks for them under `tests/ring_perf`.

- [#15934](https://github.com/leanprover/lean4/pull/15934)
  optimizes literal recognition and improves `grind` support for rational and signed fixed-width integer literals.

- [#15926](https://github.com/leanprover/lean4/pull/15926)
  makes `grind` and its variants such as `lia` invoke only the solvers that the configuration enables. Each solver extension declares when it is enabled, and `grind` computes the active solvers once per run, instead of calling every solver and letting each one check its own flag.

- [#15924](https://github.com/leanprover/lean4/pull/15924)
  speeds up `lia` on goals that contain `a / k` or `a % k` for a numeral `k`.

- [#15922](https://github.com/leanprover/lean4/pull/15922)
  makes `grind` and `lia` use the core instances for `OfNat Int n`, `OfNat Nat n`, and `Decidable` of `≤`, `<`, and `=` over `Int` and `Nat` without running type class resolution when canonicalizing terms.

- [#15917](https://github.com/leanprover/lean4/pull/15917)
  makes the kernel check the remaining `lia` certificates faster, including those for divisibility constraints, Cooper resolution, and constant folding. They now evaluate recursor-based versions of the operations they still unfolded through `match`, `decide`, or fuel. Theorems that take user hypotheses now state them with `Expr.denote_k`, so matching a hypothesis no longer unfolds `Expr.denote`. `Init.Data.Int.Kernel` gains versions of `-`, `/`, `%`, `^`, `natAbs`, `toNat`, `gcd`, `lcm`, and `bmod`.

- [#15914](https://github.com/leanprover/lean4/pull/15914)
  makes `lia` add the linear facts it derives for `a / k` and `a % k` without running them through the `simp`-based preprocessor. These facts are linear combinations that `lia` normalizes itself.

- [#15912](https://github.com/leanprover/lean4/pull/15912)
  makes `grind`'s `markNestedSubsingletons` preprocessing step reuse the core cache for instantiated constant types instead of instantiating the type of every application head again.

- [#15913](https://github.com/leanprover/lean4/pull/15913)
  fixes `grind` ignoring hypotheses such as `∀ n, v = f n → False`, where `f n` is not a pattern. The equivalent `∀ n, ¬ v = f n` worked.

- [#15911](https://github.com/leanprover/lean4/pull/15911)
  makes the kernel check `lia` certificates faster. Certificates now evaluate versions of polynomial normalization and `Int` arithmetic written with recursors, so the kernel no longer unfolds `match` and structural recursion. The `Int` versions live in the new module `Init.Data.Int.Kernel` for reuse.

- [#15910](https://github.com/leanprover/lean4/pull/15910)
  makes the `Nat` and `Int` linear-constraint parsers used by `simp_arith`, `grind`, and `lia` check that a comparison is over `Nat` (resp. `Int`) before testing its instance. Before, `Simp.Arith.Nat.ToLinear.toLinearCnstr?` matched `LE.le _ i a b` and called `DefEq.isInstLENat i` on every comparison, so each `Int` comparison paid a failing `isDefEqI` against `instLENat`; `Simp.Arith.Int.ToLinear.leCnstr?` and `dvdCnstr?` had the same problem with `Nat` comparisons.

- [#15909](https://github.com/leanprover/lean4/pull/15909)
  fixes `grind` missing a `match`-expression condition when a constructor for a nested subterm arrives after the outer merge. For example, given `h : ∀ n, v = .lit (.nat n) → False`, `grind` closed the goal from `l = .nat m` and `v = .lit l` only when the facts arrived in that order. The same issue prevented conditions of `match` equations from becoming true, e.g., `f v = 2` for `f` with the alternatives `.lit (.nat _) => 1 | _ => 2`, given `v = .lit l` and `l = .str s` from a case split.

- [#15906](https://github.com/leanprover/lean4/pull/15906)
  changes the default of the `grind` option `verbose` to `false`, which also applies to `lia`, `cutsat`, `grind_linarith`, `grind_order`, and `grobner`. Failures now show only the remaining goal and the hint `use `+verbose` to obtain diagnostic information`. Collecting and printing diagnostics took about 38% of the time spent on easy failing `lia` goals.

- [#15905](https://github.com/leanprover/lean4/pull/15905)
  makes `lia` (cutsat) prove a constraint once, in the goal where it was stored, instead of once in every branch below it. On goals with many `grind` case splits, `lia` is up to 2.8x faster in elaboration and up to 200x faster in the kernel.

- [#15891](https://github.com/leanprover/lean4/pull/15891)
  fixes a panic in `vcgen` under `set_option sym.debug true`. The panic occurred whenever `vcgen` substituted a precondition `x = t`.

- [#15884](https://github.com/leanprover/lean4/pull/15884)
  makes the `Sym.simp`-based `grind` normalizer (`backward.grind.normalizer := false`) cancel the common part of both sides of a `Nat` subtraction, as the legacy normalizer does with `Nat.reduceSubDiff`: `n + 1 - 1` becomes `n`, `n + 2 - 1` becomes `n + 1`, and `3 - (n + 1)` becomes `2 - n`. Common monomials are cancelled too, so `n + k - k` becomes `n` and `x * y + 3 - (x * y + z + 1)` becomes `2 - z`.

- [#15874](https://github.com/leanprover/lean4/pull/15874)
  fixes a `grind.debug` invariant violation in `checkEqc` on goals such as `(p && p && q) = (p && q)`.

- [#15873](https://github.com/leanprover/lean4/pull/15873)
  fixes a `grind.debug` internal error on ground `Rat` arithmetic such as `(3 : Rat) * 2 = 6`.

- [#15872](https://github.com/leanprover/lean4/pull/15872)
  fixes `grind` producing a proof the kernel rejects (`decide (1 = 1) = false`) when the same literal occurs at definitionally equal but syntactically different types, such as `(1 : BitVec w)` and `(1 : BitVec 32)` for `@[implicit_reducible] def w : Nat := 32`.

- [#15862](https://github.com/leanprover/lean4/pull/15862)
  fixes the internal `grind` error "term has not been internalized" on an `HEq` fact whose sides are proofs of `BitVec`, `UInt8`, or `Fin` equations, e.g., `p ≍ True.intro` with `p : a = 1`. Such facts are also created by `grind` when it splits a `match` with a proof discriminant.

- [#15860](https://github.com/leanprover/lean4/pull/15860)
  fixes a kernel error in `grind` when a `BitVec` width or `Fin` bound is a definition, e.g., `x : BitVec W` with `def W : Nat := 4`.

- [#15854](https://github.com/leanprover/lean4/pull/15854)
  fixes `grind?` suggesting a `grind only [...]` call that drops a premise used in the proof, together with a generated tactic script that fails to close the goal. This happened when the goal contains several case-split candidates that differ only in hidden variables, such as the `w✝`s introduced by function extensionality.

- [#15852](https://github.com/leanprover/lean4/pull/15852)
  fixes a kernel type error in proofs produced by `grind` when goals contain heterogeneous arithmetic applications such as `c * xs` with `c : Nat` and `xs : Vector Nat n`.

- [#15851](https://github.com/leanprover/lean4/pull/15851)
  fixes a stack overflow in `grind` when a `match`-expression condition refers to a term in a cyclic equivalence class, such as `as = a :: as`.

- [#15850](https://github.com/leanprover/lean4/pull/15850)
  fixes a `grind` proof that the kernel rejected when the goal involves a ring of characteristic `1`, such as `Fin 1`. Disequalities in such rings now close the goal directly.

- [#15847](https://github.com/leanprover/lean4/pull/15847)
  fixes the `grind.debug` internal error "`internalize` reached an application whose arguments are still being internalized" on casts such as `((n - m : Nat) : Int)`.

- [#7942](https://github.com/leanprover/lean4/pull/7942)
  updates to Cadical 3.0.1. While mixed on our checked in benchmarks, on SMT-LIB this was measured to be a general net-positive:
  ```
   config                 status  total  solved    sat  unsat   best  timeout  memout  error  uniq  dis   time_cpu      memory
   no_kernel_new_cadical  ee      46191   45195  17882  27313  17892      595     395      6     0    0  1077161.8  17933756.1
   kernel_new_cadical     ee      46191   45159  17890  27269   5220      642     380     10     7    0  1245494.4  27242333.1
   no_kernel_old_cadical  ee      46191   45141  17827  27314  18892      664     381      5    11    0  1187605.0  18032921.3
   kernel_old_cadical     ee      46191   45097  17833  27264   3950      715     367     12     3    0  1366219.3  27300968.9

  ```

- [#15838](https://github.com/leanprover/lean4/pull/15838)
  makes `lia` eliminate equations whose coefficients are all non-unit as in the Omega test, instead of a solved form scaled by the smallest coefficient. Chains of such equations, as produced by `/` and `%` definitions, no longer yield bounds with coefficients in the thousands and Cooper splits with as many cases.

- [#15837](https://github.com/leanprover/lean4/pull/15837)
  fixes a panic in the `lia` model search when a bound mentions a variable created after the first case split: the bound tightening indexed the divisibility constraints of the level-0 snapshot with that variable.

- [#15836](https://github.com/leanprover/lean4/pull/15836)
  fixes an internal `grind` error (`mkEqProof` invoked with terms of different types) and missed solver equalities in equivalence classes merged via `HEq` (e.g., `Fin n` and `Fin m` terms related by `cast`).

- [#15835](https://github.com/leanprover/lean4/pull/15835)
  makes `lia` reorder its variables instead of enumerating a Cooper case split with many cases, which fixes goals such as a three-limb counter increment that previously needed a `2^32`-way split.

- [#15833](https://github.com/leanprover/lean4/pull/15833)
  fixes a regression from #15827 where `lia` enumerated all cases of a Cooper split although the untightened bounds refuted every case at once.

- [#15832](https://github.com/leanprover/lean4/pull/15832)
  makes `liaSteps` also bound the cases enumerated by Cooper and disequality splits in `lia`, so that a long enumeration stops at the threshold instead of producing a proof the kernel rejects.

- [#15831](https://github.com/leanprover/lean4/pull/15831)
  fixes a panic and infinite loop in `grind`'s `lia` model search.

- [#15830](https://github.com/leanprover/lean4/pull/15830)
  fixes a kernel error and missed proofs in `lia` when an integer term or inequality occurs in a dependent position, where the `grind` preprocessor cannot normalize it.

- [#15829](https://github.com/leanprover/lean4/pull/15829)
  fixes `grind` kernel errors and internal errors when proving equalities between terms that contain binders, such as the preconditions of a function unfolded with `grind [f]`.

- [#15827](https://github.com/leanprover/lean4/pull/15827)
  makes `lia` solve goals with large-modulus divisibility constraints, such as `65536 ∣ 10 * x ⊢ 32768 ∣ x`, without a Cooper case split per residue.

- [#15826](https://github.com/leanprover/lean4/pull/15826)
  fixes `lia` exhausting `liaSteps` on goals where its rational model search looped on a divisibility constraint.

- [#15825](https://github.com/leanprover/lean4/pull/15825)
  fixes `grind` producing a proof the kernel rejects (`decide (4 = 4) = false`) when a numeral is written as `OfNat.ofNat 4`.

- [#15823](https://github.com/leanprover/lean4/pull/15823)
  fixes `grind` producing proofs that the kernel rejects when the same `Float` or `Float32` value is written in different ways, such as `2` and `2.0`.

- [#14398](https://github.com/leanprover/lean4/pull/14398)
  implements `vcgen +jp`, which verifies the code after an `if` or a `match` once instead of once per branch. Without `+jp`, `vcgen` copies that code into every branch, so `k` consecutive splits give `2ᵏ` copies of it and its VCs. With `+jp`, VC generation grows linearly in `k`. The VCs of the shared code receive a hypothesis that states what each branch knows at its end, for example `(n > 0 ∧ x = 1) ∨ (¬n > 0 ∧ x = 2)`.

- [#15819](https://github.com/leanprover/lean4/pull/15819)
  fixes a kernel error in `grind` when it combines equations between constant functions and an equivalence class contains more than one lambda.

- [#15812](https://github.com/leanprover/lean4/pull/15812)
  fixes `lia` failures on goals that mix `/` and `%` by the same power of two, such as `t % 64 ≤ (64 * t + y) % 4096 / 64`, where `omega` succeeds and `lia` exceeded `liaSteps`.

- [#15804](https://github.com/leanprover/lean4/pull/15804)
  adds the `grind` option `maxChar` (default `0`). The `Sym.simp`-based normalizer now puts arithmetic terms in normal form only over types whose characteristic is unknown or at most `maxChar`, so terms over `BitVec`, `Fin n`, `UIntN`, and `IntN` are left as written by default, as the legacy normalizer does. Before, `x - y` over `BitVec 64` became `x + 18446744073709551615 * y`, which hid the subtraction from `[grind =]` rules keyed on `x - y` and from the translation of `BitVec`/`UIntN` terms into `Nat`.

- [#15803](https://github.com/leanprover/lean4/pull/15803)
  fixes a `grind` incompleteness where a lambda that occurs as an argument of two different functions never gets a function extensionality case split for the second one. For example, `f (fun x => k x a) = f (fun x => k x b)` with `a = b` now closes even when `fun x => k x a` also occurs in a hypothesis `g (fun x => k x a)`.

- [#15802](https://github.com/leanprover/lean4/pull/15802)
  makes `grind` learn `p v` from a term `⟨v, h⟩ : {x // p x}`, so facts about subtypes are usable even when the type of the stored proof `h` is only definitionally equal to `p v`. For example, after `Subtype.forall` normalizes `∀ x : {b // R a b}, q x` to `∀ b (h : R a b), q ⟨b, h⟩`, the instance for `⟨b, hab⟩` with `hab : diag R a b` is now discharged.

- [#15796](https://github.com/leanprover/lean4/pull/15796)
  makes `vcgen` substitute a pure precondition `x = t` on a local variable `x` into the rest of the goal. The hypothesis `x = t` stays in the local context. For example, if the postcondition of a call `let r ← g` says `r = 41`, then a spec for `f 41` applies to the next call `f r`. Verification conditions now show `t` where they showed `x` before. This feature is important to support for Iris' HeapLang example.

- [#15773](https://github.com/leanprover/lean4/pull/15773)
  fixes a `maxRecDepth` failure of `grind` with the `Sym.simp` normalizer on hypotheses such as `decide (rc ≤ Int32.minValue + c) = false`, and makes the normalizer produce the standard instance after rewriting under `decide`.

- [#15772](https://github.com/leanprover/lean4/pull/15772)
  makes `grind` with the `Sym.simp` normalizer evaluate `USize.toNat n` for a numeral `n < 2^32`, so goals such as `0 < (0x10000 : USize).toNat` are closed as they are with the legacy normalizer.

- [#15770](https://github.com/leanprover/lean4/pull/15770)
  fixes `grind` failures with the `Sym.simp` normalizer on hypotheses such as `(let j := k; fun s => s.2 = j) (a, b)`, a shape produced by `mvcgen` frames.

- [#15767](https://github.com/leanprover/lean4/pull/15767)
  fixes a kernel error of `grind` with the `Sym.simp` normalizer on goals such as `i ≠ 0` for `i : BitVec (id 32)`.

- [#15766](https://github.com/leanprover/lean4/pull/15766)
  fixes a kernel error of `grind` with the `Sym.simp` normalizer on hypotheses such as `a ≠ 1/2` over a field of characteristic zero.

- [#15765](https://github.com/leanprover/lean4/pull/15765)
  fixes a kernel error of `grind` with the `Sym.simp` normalizer on goals such as `z / (-0) = 0` over a field.

- [#15764](https://github.com/leanprover/lean4/pull/15764)
  makes `simp +arith` report no change on an `Int` term that is already in normal form, and makes both `grind` normalizers keep an equation between a numeral and an atom in the orientation it was written, also when the numeral side is an expression such as `2 * 3 - 7` or `(3 : Fin 5) + 4`.

- [#15763](https://github.com/leanprover/lean4/pull/15763)
  makes `simp +arith` and both `grind` normalizers write the equations `x + -1 * y = 0` and `x + k = 0` as `x = y` and `x = -k`. These were the documented normal forms, but inputs already of the shape `p = 0` were left alone, so `x + 5 = 0` and `x + -1 * y = 0` stayed as they were while `2 * x = 2 * y` became `x = y`.

- [#15760](https://github.com/leanprover/lean4/pull/15760)
  fixes a `simp` loop on a dependent `∀ (h : p), q h` with `p : Prop` when simplifying `p` returns a proof but leaves the term unchanged. This happens, for example, with `simp +arith` when `p` contains `Int` arithmetic that is already in normal form, and it made `grind` and `lia` hit `maxRecDepth` on hypotheses such as `∀ (k : ℕ) (x : X k), …` after `Subtype.forall` became a `grind` normalization rule.

- [#15753](https://github.com/leanprover/lean4/pull/15753)
  makes the `Sym.simp`-based `grind` normalizer (`backward.grind.normalizer := false`) eta-reduce the lambda arguments of an application before their bodies are simplified, so `id (fun x => Nat.succ x) = id Nat.succ` closes: the lambda becomes `Nat.succ` instead of `fun x => x + 1`, which nothing could relate to the unapplied `Nat.succ`. The legacy normalizer closed such goals through `eq_self` up to definitional equality, which `Sym.simp` does not use.

- [#15725](https://github.com/leanprover/lean4/pull/15725)
  removes the rebuild of the `Sym.simp` normalization theorem set on every pattern normalization in `grind`. With `backward.grind.normalizer := false`, every `[grind]` attribute application and every theorem referenced by `instantiate`/`finish` paid a full conversion of the `[grind norm]` set (`grind_ite_trace` timed out).

- [#15748](https://github.com/leanprover/lean4/pull/15748)
  adds `Subtype.forall` and `Subtype.exists` to the `grind` normalization rules, so a hypothesis `∀ α : {a // p a}, q α` becomes `∀ a, p a → q ⟨a, _⟩`. Since `grind` splits subtype binders eagerly, the goal never contains `Subtype.val` terms, and the original E-matching pattern `Subtype.val ?α` of such a hypothesis could not be instantiated.

- [#15745](https://github.com/leanprover/lean4/pull/15745)
  fixes `grind` not introducing the hypotheses of an implication or universal quantifier when the goal type is wrapped in `Expr.mdata`, as it is after a `have` (`noImplicitLambda`). The goal was negated as a whole instead, so a hypothesis `¬(p → q)` reached the normalizer and the solvers.

- [#15703](https://github.com/leanprover/lean4/pull/15703)
  fixes a `grind` failure with the `Sym.simp` normalizer (`backward.grind.normalizer false`) on goals such as the one in `grind_9216`: a negated existential `¬∃ a, (p a ∨ q a) ∧ ∃ b, r a b` must become two universally quantified facts, one per disjunct, so that each gets its own E-matching pattern. `Sym.simp` left it as a single `∀ a b, …` with a disjunction in the body.

- [#15701](https://github.com/leanprover/lean4/pull/15701)
  fixes a `grind` failure, "error while initializing arithmetic operators", triggered by the `Sym.simp` normalizer (`backward.grind.normalizer false`) on a semiring whose synthesized `NatCast` instance is not reducibly defeq to the `natCast` field of its `Grind.Semiring` instance, even when the goal contains no casts.

````

# Compiler

```markdown

- [#16520](https://github.com/leanprover/lean4/pull/16520)
  fixes various file descriptor leaks and makes `io.cpp` more resistant against `errno` being changed by `close`.

- [#14954](https://github.com/leanprover/lean4/pull/14954)
  speeds up `Nat.shiftLeft` on small values by computing the result directly on machine words instead of always going through GMP, which removes three heap allocations per shift and makes `7 <<< 4` roughly as cheap as the other native `Nat` operations.

- [#16515](https://github.com/leanprover/lean4/pull/16515)
  fixes a segfault when throwing `IO.Error.unexpectedEof` in `main`.

- [#16510](https://github.com/leanprover/lean4/pull/16510)
  implements special support in the compiler for emitting Nat literals between 2^32 and 2^64 (support for up to 2^32 is pre-existing).

- [#16357](https://github.com/leanprover/lean4/pull/16357)
  bumps the libuv version to 1.53.0 across all platforms.

- [#16376](https://github.com/leanprover/lean4/pull/16376)
  makes `LEAN_STACK_SIZE_KB` also apply to the libuv event loop thread.

- [#16363](https://github.com/leanprover/lean4/pull/16363)
  updates OpenSSL to the latest available version on every platform.

- [#15586](https://github.com/leanprover/lean4/pull/15586)
  adds a `Runtime.deepCopy` operation. It traverses an object graph, copying everything along the way.

- [#16276](https://github.com/leanprover/lean4/pull/16276)
  fixes a memory leak in compiled code when a string or large `Nat` literal that is not extracted as a closed term, for example under `set_option compiler.extract_closed false`, is passed to a join point whose parameter is only read.

- [#15779](https://github.com/leanprover/lean4/pull/15779)
  makes `IO.appPath` work in PID namespaces that share their parent's `/proc` mount, such as sandboxes and rootless containers.

- [#16251](https://github.com/leanprover/lean4/pull/16251)
  makes violations of linearity markers optionally print backtraces.

- [#16213](https://github.com/leanprover/lean4/pull/16213)
  checks allocation failures inside of the olean compactor. In doing so it also allocates the buffer with Lean's allocator as opposed to fixing it to `malloc`.

- [#16195](https://github.com/leanprover/lean4/pull/16195)
  makes the default thread stack size 8MB on all 32-bit targets, not only on Emscripten, fixing a regression from #12971. A 32-bit process does not have the address space for 1GB per thread, so spawning tasks aborts with `failed to create thread: Resource temporarily unavailable`.

- [#16211](https://github.com/leanprover/lean4/pull/16211)
  fixes compilation of pattern matching on USize.

- [#16137](https://github.com/leanprover/lean4/pull/16137)
  fixes the exit code of `lean` on 32-bit targets such as WebAssembly (wasm32) and i386 after options like `--version`, `--help` and `--deps`, after an unknown option or an invalid argument, when called without a file name, and after `--run`. In these cases `lean` exited with a code derived from a heap address instead of 0, 1 or the exit code of the program's `main`; a run that processes a file without `--run` was not affected, because it ends with `IO.Process.exit`.

- [#16090](https://github.com/leanprover/lean4/pull/16090)
  fixes eight FFI functions whose definitions took one parameter more, or one fewer, than the generated C passes. On WebAssembly, unless both Lean's C++ code and the generated C were compiled with LTO, wasm-ld reported a `function signature mismatch` for each, and calls to them trapped. Every Lean program contains calls to two of them, `lean_io_create_tempfile` and `lean_io_create_tempdir`, behind `IO.FS.createTempFile` and `IO.FS.createTempDir`; the `Lean` library calls the other six.

- [#16153](https://github.com/leanprover/lean4/pull/16153)
  makes the IR interpreter evaluate `USize`, `UInt64` and `Array.uget`/`uset` primitives in place instead of calling their boxed native wrappers. A full Mathlib build executes 3.7% fewer instructions.

- [#16148](https://github.com/leanprover/lean4/pull/16148)
  speeds up the IR interpreter's callee lookup. Mathlib: -1.8% instructions in total, up to -8.5% on individual files.

- [#16049](https://github.com/leanprover/lean4/pull/16049)
  fixes quadratic compilation behavior for large list literals.

- [#16023](https://github.com/leanprover/lean4/pull/16023)
  makes `isExclusiveUnsafe` safe to call with scalars and marks both `isExclusiveUnsafe` and `ptrAddrUnsafe` as `never_extract`. We say that scalars are unique as they, by definition, cannot be shared.

- [#15950](https://github.com/leanprover/lean4/pull/15950)
  fixes a small number of issues in the non-GMP mpz implementation.

- [#15816](https://github.com/leanprover/lean4/pull/15816)
  fixes the scalar fields of static objects, such as the hashes of name literals, on 32-bit targets such as wasm32-wasip1 and i686, by choosing the form of `LEAN_SCALAR_PTR_LITERAL` by pointer size instead of by `LEAN_EMSCRIPTEN`.

- [#15890](https://github.com/leanprover/lean4/pull/15890)
  makes evaluating a thunk that is shared between threads, or reachable from the imported environment, no longer count toward the heartbeats of the thread that forces it. Which thread first forces such a thunk depends on scheduling, so counting its evaluation made heartbeat counts, and thus `maxHeartbeats` errors, nondeterministic. Evaluating a thread-local thunk still counts as before.

- [#15774](https://github.com/leanprover/lean4/pull/15774)
  upgrades LLVM from 23.1.1 to 23.1.3. Incidentally it's also the first LLVM upgrade to use our new LLVM builds based on RHEL. This makes it compatible with older glibc releases than before.

```

# FFI

```markdown

- [#15957](https://github.com/leanprover/lean4/pull/15957)
  deletes the unused and unsafe `lean_utf8_strlen` function, which can read past a NUL-terminated buffer on truncated UTF-8 input.

- [#15980](https://github.com/leanprover/lean4/pull/15980)
  removes the obsolete `lean_string_data` declaration and its C++ wrapper from the `src` headers. The function implementation had been removed, but not the declaration.

```

# Server

```markdown

- [#16314](https://github.com/leanprover/lean4/pull/16314)
  replaces the earlier distinction between text tokens found in docstring and non-docstring Verso content with the consistent use of the `documentation` modifer for _all_ markup tokens that occur in docstrings. This makes it easier for editors to match a wider variety of themes.

- [#15550](https://github.com/leanprover/lean4/pull/15550)
  adds an `#html` command that displays HTML values in the infoview (as widget messages).

- [#13674](https://github.com/leanprover/lean4/pull/13674)
  adds semantic tokens for Markdown and Verso that correspond to those available in editor themes for Markdown. With a small update to editors, docstrings can be consistently formatted without needing to reimplement either complex parser client-side.

- [#15846](https://github.com/leanprover/lean4/pull/15846)
  adds folding range support for proofs that serve as the body of a declaration.

```

# Lake

```markdown

- [#16514](https://github.com/leanprover/lean4/pull/16514)
  passes `LEAN_NUM_THREADS` to relevant Lean based child processes of comparator.

- [#16351](https://github.com/leanprover/lean4/pull/16351)
  adds the package configuration option `downloadCacheService`. Lake uses this service as the default for a `lake cache get` of the package. Even without a `lake cache get`,  if the artifact cache is enabled, Lake will automatically download outputs and artifacts from the service on demand during a package build.

- [#16475](https://github.com/leanprover/lean4/pull/16475)
  ensures the target`ltar` file is removed before `leantar` is run. The `ltar` may be read-only if restored from the cache, in which case `leantar` will fail to overwrite it on Windows.

- [#16471](https://github.com/leanprover/lean4/pull/16471)
  prevents current fetches from overriding jobs in the build store and ensures that fetches always obtain the same job from the build store.

- [#16470](https://github.com/leanprover/lean4/pull/16470)
  fixes an issue where new build outputs could be associated with a stale trace if a build output new artifacts, failed, and then its source changes where reverted. Lake now always removes the trace before running a build action.

- [#16472](https://github.com/leanprover/lean4/pull/16472)
  fixes a few places where errors where not properly wrapped into the job associated with a facet.

- [#16461](https://github.com/leanprover/lean4/pull/16461)
  ensures downloaded artifacts are written to the cache automatically. In particular, on-demand artifacts now use a temporary file for their download before being stored as their final name (as `lake cache get` downloads already do).

- [#16457](https://github.com/leanprover/lean4/pull/16457)
  makes a module build fail if its source file changed while the build was running (i.e., between import calculation and the end of elaboration). This mitigates the chance of concurrent edits leading to a invalid builds. For example, previously, editing a file while a build was running could lead to  a trace which mapped the unedited file to the edited file's build results, producing a poisoned build store.

- [#16439](https://github.com/leanprover/lean4/pull/16439)
  fixes a bug where Lake would keep outdated `.hash` files when unpacking `.ltar` archives because it did not clear the hashes along with the artifacts before unpacking. To avoid such mistakes in the future, `clearOutputArtifacts` and `clearIROutputArtifacts` now delete the hashes along with the artifacts.

- [#16086](https://github.com/leanprover/lean4/pull/16086)
  changes Lake's build store to use a `Std.Mutex` instead of a `IO.Ref` for mutation.

- [#16302](https://github.com/leanprover/lean4/pull/16302)
  adds the ability to specify Lake cache services from within a package via a new `cache_service`  TOML table or Lean DSL declaration. These services can then be used via `lake cache get --service`. Uploading (i.e.,  `put` or `put-unstaged`) does not support package-specified services . There can only be one service per name, and a package's services take precedence over their dependencies. Services configured in the system configuration take precedence over all package-specified services.

- [#15861](https://github.com/leanprover/lean4/pull/15861)
  makes file writes to the cache atomic. Previously, a racing reader could observe a partially written artifact.

- [#16121](https://github.com/leanprover/lean4/pull/16121)
  fixes an issue with `CacheMap.writeFile` where it would truncate the file before locking it.

- [#14725](https://github.com/leanprover/lean4/pull/14725)
  makes `lake cache get` and `lake cache put` retry a transfer that fails in a transient way, such as a dropped connection or a corrupted download. Previously, one such failure made the whole command fail. Lake now attempts each transfer at most 3 times.

- [#15805](https://github.com/leanprover/lean4/pull/15805)
  computes Lake's transitive import closure first from a single snapshot of the build store, falling back to the real build store only when an artifact is missing. This decreases contention on the main build store, whose fetches otherwise must be atomic.

- [#16096](https://github.com/leanprover/lean4/pull/16096)
  adds more explicit documentation on the assumptions and guarantees provided by comparator.

- [#16083](https://github.com/leanprover/lean4/pull/16083)
  adds a new Lake benchmark that measures the performance of computing module setups. This computation walks the transitive import graph and thus scales with the size of the import closure. Experiments have shown this to be a significant bottleneck for scalability in projects with thousands of modules.

- [#15894](https://github.com/leanprover/lean4/pull/15894)
  fixes `lake update --keep-toolchain` so that a revision pinned in the root package's own `require` takes priority over one locked in another dependency's manifest, as it already does without the flag. Previously, the root's entry could be replaced by the dependency's older revision and marked as inherited.

- [#16019](https://github.com/leanprover/lean4/pull/16019)
  introduces support for a `--json` flag on `lake comparator` and `lake check`. When passed the commands will print one final JSON report to stdout instead of reporting continous progress. The JSON format is versioned and should be easily machine consumable. The format itself is specified by the `ToJson` and `FromJson` instances on the types `LakeComparatorReport` and `LakeCheckReport`.

- [#15775](https://github.com/leanprover/lean4/pull/15775)
  forces definition holes in comparator to either be a `sorry` or a lambda with a `sorry` body. This forces challenges to be in a more canonical form where a challenge can never rely on a definition hole having a particular value already.

- [#15762](https://github.com/leanprover/lean4/pull/15762)
  makes `lake check` check the project's axioms before running the kernels, as `lake comparator` already does. Previously, with `--paranoid`, a project using a non-standard axiom (e.g. via `native_decide`) was rejected only by an external checker, sometimes with an obscure failure such as a `nanoda` panic, and the report naming the unpermitted axiom was never shown.

```

# Other

````markdown

- [#16473](https://github.com/leanprover/lean4/pull/16473)
  updates bundled `lean-beam` with speculative profiling and improvements to Lean language server compatibility, cancellation, and error reporting.

- [#16349](https://github.com/leanprover/lean4/pull/16349)
  improves the error message when Lean fails to load a .olean because of e.g. the memory mapping limit on Linux.

- [#16107](https://github.com/leanprover/lean4/pull/16107)
  fixes a quadratic slowdown in the kernel when checking terms that contain long chains of the same application, such as `"ff…f" = String.ofList (List.replicate n 'f')`.

- [#14362](https://github.com/leanprover/lean4/pull/14362)
  makes importing modules substantially cheaper by replacing the imported-constants hash maps, which every import rebuilt from scratch, with per-module prefix trees that are written into the oleans and merged lazily on first access. On Mathlib, the build takes 3.0% less wall-clock time, importing all of Mathlib 3.4% less CPU time and 128 MB less memory, and the time spent importing during the build drops by 36%, at the cost of 1.1% larger olean files.

- [#15853](https://github.com/leanprover/lean4/pull/15853)
  makes `Kernel.Environment.replay` add `String.ofList` and `Char.ofNat` (if present) before any other constant. The kernel unfolds string literals to `String.ofList [Char.ofNat n, …]`, but these constants are not syntactic dependencies of a declaration that reduces a string literal. So replay, which orders declarations only by their syntactic dependencies, could check such a declaration first and wrongly reject it, for example
  ```lean
  theorem t1 : "abc" ++ "def" = "abcdef" := by decide
  ```

````
