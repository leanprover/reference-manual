/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Std.Async
import Std.Sync.Channel

import Manual.Meta

import Lean.Parser.Command

open Std.Async
open Std (CloseableChannel)

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "Asynchronous Programming" =>
%%%
file := some "Async"
%%%

The {name}`Async` monad provides tools and abstractions for constructing asynchronous programs that can safely multiplex different sources of data.
Typical use cases include network servers and other interactive applications that perform IO and must react to a variety of events, such as incoming data, timeouts, and disconnections.
Generally speaking, sequential programs that interact with the operating system can use {name}`IO` alone.
Parallel programs should use {name}`Task`s.
{name}`Async` is most appropriate when a program may spend a significant amount of time waiting on external events or I/O.

The most important feature of {name}`Async` is {deftech}_event selection_.
Given a set of potential inputs, and a computation to be carried out in response to each, event selection ensures that computations are triggered as events occur.
Each computation is triggered exactly once, as its associated event occurs, and data can never be lost.
These properties are very difficult to ensure without appropriate library support.

Behind the scenes, asynchronous tasks are represented using tasks and promises.
An asynchronous computation runs on the current thread until it must wait for a result that is not yet available, such as a timer or incoming network data.
The missing data is represented by a {name IO.Promise}`Promise`.
At that point, the asynchronous computation suspends.
Rather than blocking the thread, it yields control and arranges to resume once the awaited promise is resolved.
A single thread can therefore make progress on many waiting computations at once.
The standard library resolves these promises in response to operating system events—timers, sockets, signals, and name resolution—using the `libuv` event loop as its I/O backend.
The asynchronous model itself depends only on tasks and promises, however: any source that resolves a promise, such as a channel, can be used to reinvoke an asynchronous computation just as well.

# Asynchronous Computations

:::paragraph
There are three monads for writing asynchronous programs, each corresponding to one of the variants of {name}`IO`:

* {name}`Async` describes asynchronous computations that may throw an {name}`IO.Error`, and corresponds to {name}`IO`.
* {name}`EAsync` describes asynchronous computations that may throw a specified type of error, and corresponds to {name}`EIO`.
* {name}`BaseAsync` describes asynchronous computations that cannot throw an error, and corresponds to {name}`BaseIO`.

:::

{docstring Async}

{docstring EAsync}

{docstring BaseAsync}

Infinite loops in {name}`EAsync` and {name}`Async` use a special instance of {name}`ForIn` that ensures that they don't consume stack frames when used in {keywordOf Lean.Parser.Term.doRepeat}`repeat` and {keywordOf Lean.Parser.Term.doWhile}`while` loops.
They can therefore be used in long-running asynchronous applications such as servers without the stack overflowing.

Each of these monads has a corresponding type of asynchronous tasks that it can coordinate.
These tasks can be thought of as handles to an in-flight computation.
Calling {name}`async` on a monadic action creates a task that runs in a thread from the thread pool, and calling {name}`await` on a task results in a monadic action that waits for the task to complete.
Passing {name}`Task.Priority.dedicated` as the `prio` parameter to {name}`async` causes the task to run on a dedicated thread instead.

{docstring ETask}

{docstring AsyncTask}

{docstring MaybeTask +allowMissing}

Crucially, calling {name}`await` on a task never blocks an OS-level thread.
Threads are only blocked at the {ref "async-run"}[boundary] between the {name}`IO` and the {name}`Async` monads.
When an asynchronous task {name}`await`s a value, the code that will handle the value is attached to the task.
When the task is resolved, this code is scheduled in the thread pool like any other task.

Asynchronous tasks use the same system of {tech (key := "task priority")}[priorities] as {ref "concurrency"}[other Lean tasks], and are run by the same scheduler.

## Running Asynchronous Computations
%%%
tag := "async-run"
%%%

Asynchronous computations can be run from {name}`IO` by either waiting or blocking.
When a thread waits on an asynchronous computation, the asynchronous computation is run on the thread that is waiting until its first suspension.
After suspension, it may be scheduled in any thread in the thread pool, and the waiting thread blocks until the result is available.
When a thread blocks on an asynchronous computation, the computation is run on a worker thread in an ordinary {tech}[task] with the specified priority, and the calling thread calls {name}`Task.get` to block on the result.
Because {name}`Async` is a defined alias for {name}`EAsync`, {tech}[generalized field notation] can be used to call {name}`EAsync.wait` on a term with type {name}`Async`.

{docstring EAsync.wait}

{docstring BaseAsync.wait}

{docstring Async.block}

{docstring EAsync.block}

{docstring ETask.block}

{docstring AsyncTask.block}

Asynchronous computations can also be run as ordinary {name}`Task`s in {name}`IO`.

{docstring Async.toIO}

{docstring EAsync.toEIO}

{docstring BaseAsync.toBaseIO}

{docstring EAsync.asTask}

{docstring BaseAsync.asTask}

Compared to {name}`IO.asTask`, {name}`EAsync.asTask` schedules an _asynchronous task_.
While tasks from {name}`IO.asTask` are synchronous, occupying their worker thread until completed, tasks from {name}`EAsync.asTask` release their worker threads at suspension points and resume as tasks when the awaited value becomes available.

::::example "Running an Asynchronous Computation"
{name}`Async.block` runs an asynchronous computation and returns its result in {name}`IO`.
The following program prints a message, waits ten milliseconds, and then prints another:
:::ioExample
```ioLean
module
import Std.Async
open Std.Async

def greet : Async Unit := do
  IO.println "before sleeping"
  sleep 10
  IO.println "after sleeping"

public def main : IO Unit := greet.block
```
It prints both messages, with a brief pause between them:
```stdout
before sleeping
after sleeping
```
:::
::::

## Managing Tasks

The typical interface to asynchronous tasks is via the {name}`MonadAsync` and {name}`MonadAwait` instances for a monad.
Their respective methods {name}`MonadAsync.async` and {name}`MonadAwait.await` are {ref "exporting-names"}[exported] from {namespace}`Std.Async`.
Typically, the main thread of execution will create some number of asynchronous tasks, then await their results when needed to make progress.
The {name}`async` and {name}`await` functions are not built in to the Lean compiler, and they don't trigger a whole-program transformation.
They just create or consume tasks that are associated with underlying promises in the correct manner for the framework.

{docstring MonadAwait}

{docstring MonadAsync}

To launch an asynchronous task whose value will never be needed, use {name}`background`.

{docstring background}

In addition to instances for the {name}`Async` monads and tasks, the library includes instances that allow reader and state monad transformers to be used with {name}`async` and {name}`await`, and exception monad transformers to be used with {name}`await`.

```lean -show
-- The transformer instances for `await` and `async`.
example : MonadAwait AsyncTask (StateT Nat Async) := inferInstance
example : MonadAwait AsyncTask (ReaderT Nat Async) := inferInstance
example : MonadAwait AsyncTask (ExceptT String Async) := inferInstance
example : MonadAsync AsyncTask (StateT Nat Async) := inferInstance
example : MonadAsync AsyncTask (ReaderT Nat Async) := inferInstance
```

:::example "Spawning and Awaiting Tasks"
```imports -show
import Std.Async
```
```lean -show
open Std.Async
```
{name}`async` starts a computation as a task that runs concurrently, and {name}`await` waits for a task's result.
Here, a color and a flavor are fetched concurrently, and the two results are combined into a pair:
```lean (name := bothOut)
def fetchColor : Async String := do
  sleep 20
  return "green"

def fetchFlavor : Async String := do
  sleep 20
  return "sweet"

def fetchBoth : Async (String × String) := do
  let color ← async fetchColor
  let flavor ← async fetchFlavor
  return (← await color, ← await flavor)

#eval fetchBoth.block
```
```leanOutput bothOut
("green", "sweet")
```
:::

::::example "Background Tasks"
{name}`background` starts a computation whose result is never awaited.
Here, a logger runs in the background and prints each message sent to a channel:
:::ioExample
```ioLean
module
import Std.Async
import Std.Sync.Channel
open Std.Async
open Std (Channel)

def logger (ch : Channel String) : Async Unit := do
  while true do
    IO.println (← await (← ch.recv))

public def main : IO Unit := do
  let ch ← Channel.new (α := String)
  Async.block do
    background (logger ch)
    discard <| ch.send "hello from the background"
    sleep 20
```
The background logger prints the message it receives before the program exits:
```stdout
hello from the background
```
:::
::::

## Transforming and Inspecting Tasks

The eventual result of an asynchronous task can be transformed without first awaiting it.
{name}`AsyncTask.map` applies a function to a task's result, while {name}`AsyncTask.bindIO` and {name}`AsyncTask.mapTaskIO` sequence further {name}`IO` work onto it.
In each case, an error in the original task propagates to the transformed task.

{docstring AsyncTask.map}

{docstring AsyncTask.bindIO}

{docstring AsyncTask.mapTaskIO}

A task's progress can be inspected without blocking by retrieving its {name}`IO.TaskState`.

{docstring ETask.getState}

{docstring AsyncTask.getState}

A {name}`MaybeTask` is either an immediately-available value or a task that will produce one.
It can be converted to an ordinary {name}`Task`, have its value read by blocking, be mapped over, and have a {name}`Task` of a {name}`MaybeTask` collapsed into a single {name}`Task`.

{docstring MaybeTask.toTask}

{docstring MaybeTask.get}

{docstring MaybeTask.map}

{docstring MaybeTask.joinTask}

## Conversions

An existing {name}`Task`, {name}`IO.Promise`, or {name}`Except` value can be converted into an {name}`Async` computation.
These conversions make it possible to call code that produces a {name}`Task` or {name}`IO.Promise`, such as a wrapper around a callback-based API or a hand-written asynchronous primitive, directly from within an {name}`Async` program.
The corresponding conversions from {name}`Task` and {name}`Except` are also available for {name}`EAsync` and {name}`BaseAsync`; the conversions from {name}`IO.Promise` are specific to {name}`Async` because a dropped promise is reported as an {name}`IO.Error`.

An {name}`IO.Promise` can be dropped before it is ever resolved, for example if the code that was expected to resolve it is canceled or abandoned and the last reference to the promise goes away.
After that, the promise can never be resolved.
Because {tech}[reference counts] are deterministic, the runtime detects this the moment it happens, rather than at some unpredictable later time.
{name}`Async.ofPromise` and {name}`Async.ofPurePromise` detect a dropped promise and produce an {name}`Async` error rather than panicking; the message can be supplied via their `error` parameter, and defaults to `the promise linked to the Async was dropped`.

```lean -show
-- A promise that is dropped without ever being resolved surfaces as an `Async`
-- error rather than panicking, because these conversions use `IO.Promise.result?`.
-- Reference counts are deterministic, so the drop happens as soon as the only
-- reference to the promise goes away.
#eval show IO Unit from do
  let msg ← (do
    try
      let _ ← (Async.ofPromise (α := Nat) IO.Promise.new).block
      pure "no error"
    catch e => pure (toString e))
  unless msg == "the promise linked to the Async was dropped" do
    throw (IO.userError "ofPromise: a dropped promise should produce an error")

#eval show IO Unit from do
  let msg ← (do
    try
      let _ ← (Async.ofPurePromise (α := Nat) IO.Promise.new).block
      pure "no error"
    catch e => pure (toString e))
  unless msg == "the promise linked to the Async was dropped" do
    throw (IO.userError "ofPurePromise: a dropped promise should produce an error")
```

{docstring Async.ofTask}

{docstring EAsync.ofTask}

{docstring EAsync.ofETask}

{docstring BaseAsync.ofTask}

{docstring Async.ofIOTask}

{docstring Async.ofAsyncTask}

{docstring Async.ofPromise}

{docstring Async.ofPurePromise}

{name}`ETask.ofPromise!` converts a promise to a task directly, panicking if the promise is dropped rather than producing an error.

{docstring ETask.ofPromise!}

{docstring Async.ofExcept}

{docstring EAsync.ofExcept}

{docstring BaseAsync.ofExcept}

# Concurrent Composition

Concurrent composition runs several asynchronous computations at the same time and combines their results.
These operators are defined in terms of {name}`async` and {name}`await`, but they provide a higher-level, more structured approach to concurrent asynchronous programming.
Each operator launches {tech}[tasks] on the shared scheduler at the {tech (key := "task priority")}[priority] given by the optional `prio` parameter, and then awaits them.
There are two families of concurrent operators: those that wait for every subcomputation and return all results, and those that return the result of the first subcomputation that finishes.

{name}`Async.concurrently` runs two computations and returns their results as a pair, while {name}`Async.concurrentlyAll` runs an array of computations and returns their results in the same order.
Both wait for every subcomputation to finish, awaiting them positionally rather than chronologically, so an exception is reported in the position of the failing subcomputation rather than in the order in which failures occur (see {ref "errors-and-concurrency"}[errors and concurrency]).

{name}`Async.race` runs two computations and returns the result of whichever finishes first, while {name}`Async.raceAll` does the same for an array of computations.
The result of the call to {name}`Async.race` or {name}`Async.raceAll` is that of the first subcomputation to chronologically finish, whether it is a thrown exception or a returned value.
A computation that fails quickly takes precedence over one that succeeds slowly.

None of these operators cancel the computations whose results are not used.
In {name}`Async.race` and {name}`Async.raceAll`, the computations that do not finish first continue running to completion, and their results are discarded.
In {name}`Async.concurrently` and {name}`Async.concurrentlyAll`, a failure in one subcomputation does not stop the others.
The corresponding operators on {name}`ContextAsync`, such as {name}`ContextAsync.race`, do cancel the computations that are no longer needed.

To start a computation concurrently without awaiting its result, use {name}`background`.

```lean -show
-- `race` returns the first computation to finish.
#eval do
  let r ← (Async.race (do sleep 80; return 1) (do sleep 10; return 2)).block
  unless r == 2 do throw (IO.userError "race: first to finish")

-- No cancellation: the loser keeps running to completion after the race returns.
#eval show IO Unit from do
  let ranToEnd ← IO.mkRef false
  let r ← (Async.race
    (do sleep 10; return "fast")
    (do sleep 40; ranToEnd.set true; return "slow")).block
  unless r == "fast" do throw (IO.userError "race: winner")
  IO.sleep 80
  unless (← ranToEnd.get) do throw (IO.userError "race: loser was canceled")

-- `ContextAsync.race` cancels the loser.
def ctxRaceCancelsLoser : Async Bool := ContextAsync.run do
  let cancelledP ← IO.Promise.new (α := Bool)
  let loser : ContextAsync Nat := do
    let c ← Selector.cancelled
    discard <| Selectable.one #[.case c (fun _ => pure ())]
    cancelledP.resolve true
    return 2
  let r ← ContextAsync.race (do sleep 5; return 1) loser
  unless r == 1 do throw (IO.userError "ctxRace: winner")
  Async.race (await cancelledP) (do sleep 500; return false)
#eval do
  unless (← ctxRaceCancelsLoser.block) do throw (IO.userError "ctxRace: loser was not cancelled")

-- `concurrentlyAll` returns results in array order, not completion order.
#eval do
  let r ← (Async.concurrentlyAll #[
    (do sleep 50; return 1),
    (do sleep 10; return 2),
    (do sleep 30; return 3)]).block
  unless r == #[1, 2, 3] do throw (IO.userError "concurrentlyAll: order")
```

Each operator is available for {name}`BaseAsync`, {name}`EAsync`, and {name}`Async`.

{docstring Async.concurrently}

{docstring EAsync.concurrently}

{docstring BaseAsync.concurrently}

{docstring Async.concurrentlyAll}

{docstring EAsync.concurrentlyAll}

{docstring BaseAsync.concurrentlyAll}

{docstring Async.race}

{docstring EAsync.race}

{docstring BaseAsync.race}

{docstring Async.raceAll}

{docstring EAsync.raceAll}

{docstring BaseAsync.raceAll}

# Event Selection
%%%
tag := "async-select"
%%%

:::leanSection
```lean -show
variable (α : Type)
```
{tech}[Event selection] involves both {deftech}_selectors_, which are the source of events, and {deftech}[selectables], which pair selectors with code to be executed when the selector's event occurs.
When a selector's event occurs, the selector has {deftech}_resolved_.
A selectable's code is not executed immediately when its selector resolves; instead, it is run when invoked by event selection.
When a selectable whose selector has resolved is chosen for execution, it is {deftech}_selected_.

A {lean}`Selector α` provides a value of type {lean}`α` when its event occurs, while a {lean}`Selectable α` contains an {name}`Async` action to run when its selector has resolved.
The type of the selector in a {name}`Selectable` is a field of the _constructor_ {name}`Selectable.case`, rather than a {tech}[parameter] to the type; this means that selectables that are waiting on different types of event data can be used together.
:::

{docstring Selector}

{docstring Selectable +allowMissing}

Event selection is invoked using three operators:
 * {name}`Selectable.one` blocks until one selectable's event occurs and returns the resulting value,
 * {name}`Selectable.tryOne` checks whether any selectable is resolved and returns the associated value but does not block,
 * {name}`Selectable.combine` creates a new {name}`Selector` whose event occurs when any of the underlying {name}`Selectable`s selector's event occurs, yielding the {name}`Selectable`'s data.

{docstring Selectable.one}

{docstring Selectable.tryOne}

{docstring Selectable.combine}

:::example "Polling Without Blocking"
```imports -show
import Std.Async
import Std.Sync.Channel
```
```lean -show
open Std Async
```
{name}`Selectable.tryOne` checks whether any selector has already resolved and returns the corresponding value immediately, or {name}`none` if none has, rather than blocking.
Defining selection with `:=` rather than `←` makes `pick` the {name}`Async` computation itself rather than its result, so the same poll can be run more than once.
```lean (name := tryOneOut)
#eval show IO (Option String × Option String × Option String) from do
  let colors ← Channel.new (α := String)
  let flavors ← Channel.new (α := String)
  let pick := Selectable.tryOne #[
    .case colors.recvSelector fun color => return color,
    .case flavors.recvSelector fun flavor => return flavor
  ]
  let whenEmpty ← pick.block
  discard <| colors.send "gray"
  let afterColor ← pick.block
  discard <| flavors.send "salty"
  let afterFlavor ← pick.block
  return (whenEmpty, afterColor, afterFlavor)
```
```leanOutput tryOneOut
(none, some "gray", some "salty")
```
:::

:::example "Selection and Timeouts"
```imports -show
import Std.Async
import Std.Sync.Channel
```
```lean -show
open Std Async
```
A {name}`CloseableChannel` provides a selector via {name}`CloseableChannel.recvSelector` that resolves when the channel receives a value.
{name}`Selector.sleep` is a selector that resolves after the specified number of milliseconds have passed.
The function {name}`recv` combines these, waiting for up to 100 milliseconds to receive a value, after which it terminates without one:
```lean
def recv (ch : CloseableChannel Nat) : Async (Option Nat) := do
  Selectable.one #[
    .case ch.recvSelector fun n? => return n?,
    .case (← Selector.sleep 100) fun () => return none
  ]
```

If the channel contains a value, then the {name CloseableChannel.recvSelector}`recvSelector` wins:
```lean (name := recvWin)
#eval show IO _ from do
  let ch ← CloseableChannel.new (α := Nat)
  discard <| ch.send 42
  (recv ch).block
```
```leanOutput recvWin
some 42
```
If not, the timer wins:
```lean (name := timerWin)
#eval show IO _ from do
  let ch ← CloseableChannel.new (α := Nat)
  -- nothing sent: the timeout wins
  (recv ch).block
```
```leanOutput timerWin
none
```
:::

:::example "Selection"
```imports -show
import Std.Async
import Std.Sync.Channel
```
```lean -show
open Std Async
```
A {name}`CloseableChannel` provides a selector via {name}`CloseableChannel.recvSelector` that resolves when the channel receives a value.
The function {name}`recv2` selects the first value returned on either channel:
```lean
def recv2 (ch1 ch2 : CloseableChannel Nat) : Async (Option Nat) := do
  Selectable.one #[
    .case ch1.recvSelector fun n? => return n?,
    .case ch2.recvSelector fun n? => return n?
  ]
```

If only one channel contains a value, then it is returned:
```lean (name := chan1)
#eval show IO _ from do
  let ch1 ← CloseableChannel.new (α := Nat)
  let ch2 ← CloseableChannel.new (α := Nat)
  discard <| ch1.send 1
  (recv2 ch1 ch2).block
```
```leanOutput chan1
some 1
```

```lean (name := chan2)
#eval show IO _ from do
  let ch1 ← CloseableChannel.new (α := Nat)
  let ch2 ← CloseableChannel.new (α := Nat)
  discard <| ch2.send 2
  (recv2 ch1 ch2).block
```
```leanOutput chan2
some 2
```

If neither channel contains a value, then {name}`recv2` blocks until one does; the first one to have a value wins:
```lean (name := recv2race)
#eval show IO _ from do
  let ch1 ← CloseableChannel.new (α := Nat)
  let ch2 ← CloseableChannel.new (α := Nat)
  discard <| IO.asTask (prio := .dedicated) do
    IO.sleep 100
    ch1.send 1
  discard <| IO.asTask (prio := .dedicated) do
    IO.sleep 50
    ch2.send 2
  (recv2 ch1 ch2).block
```
```leanOutput recv2race
some 2
```
:::


Both {name}`Selectable.one` and {name}`Selectable.tryOne` throw an exception when passed an empty array of selectables, because it's impossible to get a value from nothing.

Event selection is {deftech}_fair_.
This means that there is an equal probability that any of the selectables with currently-resolved selectors win and have their associated code invoked.
This is important because a bias in event selection can lead to one of the selectables _never_ being called, which can in turn cause data to accumulate without bound in the source it would have handled.
Behind the scenes, fairness is ensured by randomizing the order of selectables each time.

```lean -show
-- Both selection operators reject an empty array.
#eval do
  let e ← try discard <| (Selectable.one (α := Nat) #[]).block; pure "" catch e => pure (toString e)
  unless e == "Selectable.one requires at least one Selectable" do throw (IO.userError s!"one: {e}")
  let e ← try discard <| (Selectable.tryOne (α := Nat) #[]).block; pure "" catch e => pure (toString e)
  unless e == "Selectable.tryOne requires at least one Selectable" do throw (IO.userError s!"tryOne: {e}")

-- Fairness: over many selections between two ready channels, each wins at least once.
def fairness : Async Unit := do
  let a ← CloseableChannel.new (α := Nat)
  let b ← CloseableChannel.new (α := Nat)
  let mut aWins := 0
  let mut bWins := 0
  for _ in [0:200] do
    discard <| a.send 0
    discard <| b.send 0
    let w ← Selectable.one #[.case a.recvSelector (fun _ => return 0), .case b.recvSelector (fun _ => return 1)]
    if w == 0 then aWins := aWins + 1 else bWins := bWins + 1
    -- drain the loser so both channels start each round with exactly one value
    discard <| (if w == 0 then b else a).recv
  unless aWins > 0 && bWins > 0 do throw (IO.userError s!"fairness: {aWins} vs {bWins}")
#eval fairness.block
```

Furthermore, event selection never results in data being lost in the losing selectables.
The implementation ensures that data is never removed from a selector without being passed to the selectable's code, and that resolving a selector calls the associated selectable's code at most once.
Data loss and double delivery are ruled out via a protocol that distinguishes checking whether a selector is resolved from actually consuming its data along with an atomic means of selecting one of the resolved selectors.

```lean -show
-- Hidden regression test for the no-data-loss claim above. Both channels are
-- empty when selection begins, so the waiting path is taken; only A is delivered
-- during selection, and B's value (sent afterward) must still be received intact.
def noDataLoss : Async (String × String) := do
  let chA ← CloseableChannel.new (α := String)
  let chB ← CloseableChannel.new (α := String)
  discard <| IO.asTask (prio := .dedicated) do
    IO.sleep 20; discard <| chA.send "from A"
  let winner ← Selectable.one #[
    .case chA.recvSelector fun s? => return ("A:" ++ s?.getD "?"),
    .case chB.recvSelector fun s? => return ("B:" ++ s?.getD "?")
  ]
  discard <| chB.send "from B"
  let next ← Selectable.one #[
    .case chB.recvSelector fun s? => return ("B:" ++ s?.getD "?")
  ]
  return (winner, next)
#eval do
  let (winner, next) ← noDataLoss.block
  unless winner == "A:from A" do throw (IO.userError "noDataLoss winner")
  unless next == "B:from B" do throw (IO.userError "noDataLoss next")
```

## Selection Protocol
%%%
tag := "selector-protocol"
%%%

:::sectionNote
This section is primarily intended for authors of new selectors.
:::

Event selection begins by randomizing the order of the selectables.
Each selector's non-blocking poll {name}`Selector.tryFn` is consulted until one of them returns {name}`some`.
This is the winning selectable; its code is invoked and no further work is needed.
On this fast path, only one selector is ever consumed, so there is no risk of data loss or double delivery.
No cleanup is needed because a {name Selector.tryFn}`tryFn` that returns {name}`none` must leave its data source unchanged.

If no selector was resolved in the first iteration (that is, each {name Selector.tryFn}`tryFn` returned {name}`none`), then it is necessary to wait until one of the selectors is resolved.
The process of waiting has three phases: {ref "selector-protocol-registration"}[registration], {ref "selector-protocol-race"}[racing], and {ref "selector-protocol-cleanup"}[cleanup].
Racing is concurrent with registration: the race begins before all selectors have been registered, and it may even terminate before all selectors have been registered.

The winning selectable's data is passed to the selectable's {name}`Selectable.cont` continuation.
This continuation asynchronously computes the result that is returned from {name}`Selectable.one`.

### Registration
%%%
tag := "selector-protocol-registration"
%%%

Prior to registration, the order of the selectables is randomized again.
During registration, a {tech}[waiter] is registered with each selector in turn using {name}`Selector.registerFn`.
Selectors must consider registration to be merely an expression of interest in the selector's data, so a {name Selector.registerFn}`registerFn` should not itself consume data.

Racing begins as soon as the first {name Selector.registerFn}`registerFn` has been called.
The first selector that has data wins the race via the waiters.
Selectors may win the race during their {name Selector.registerFn}`registerFn` calls.
If the data becomes available between the initial {name Selector.tryFn}`tryFn` loop and the registration phase, then there's no reason to wait until later to win the race.

All the waiters involved in a selection share a single atomic flag that indicates whether a winner has already been chosen, while each waiter has its own promise by which the selector can deliver its data if it wins the race.
The registration process stops early if the flag is already set, because that indicates that a selector has already won, so further registration is pointless.
Likewise, if a {name Selector.registerFn}`registerFn` throws an exception, then the process stops.
If a selector has already won, then its result is returned and the exception is discarded; otherwise, the exception becomes the result of the selection.

### Racing
%%%
tag := "selector-protocol-race"
%%%

Racing begins as soon as a single selectable is registered, and it continues until a selectable wins the race or registration fails due to an exception.
When a selectable's event is ready, it calls {name}`Waiter.race` on its waiter; the waiter determines whether it has won.

A {deftech}_waiter_ is a means of atomically selecting a single offered value.
Internally, it contains an atomic flag that indicates that a winner has been selected.
When a client has a value, it calls {name}`Waiter.race` with two callbacks: one is used when the offered value was not accepted (it did not win the race), the other is used when it is accepted.
The callback that is invoked upon winning the race should resolve the waiter's promise, which is provided to the winning callback.
The callback that is invoked upon losing the race must leave all data in place.
This two-phase protocol ensures that there is no data loss, because selectors only consume events once they've already won the race.

{docstring Waiter +allowMissing}

{docstring Waiter.race}

{docstring Waiter.withPromise}

{docstring Waiter.checkFinished}

### Cleanup
%%%
tag := "selector-protocol-cleanup"
%%%

When the {ref "selector-protocol-race"}[race] is completed, selectors are offered the opportunity to clean up.
This occurs no matter whether the race has been won or a  {name}`Selector.registerFn` threw an exception, but not when the initial {name Selector.tryFn}`tryFn` loop returned a value.
In this phase, {name}`Selector.unregisterFn` is called on every selector in the array, regardless of whether it was registered in the {ref "selector-protocol-registration"}[registration phase] or whether it threw an exception during registration.

Cleanup always occurs, regardless of whether an error occurred during registration, racing, or in prior selectors' {name Selector.unregisterFn}`unregisterFn` implementations.
Selectors must therefore be written so that {name Selector.unregisterFn}`unregisterFn` is safe to use even when their {name Selector.registerFn}`registerFn` lost the race, was never called, or threw an exception.


:::example "Natural Number Ticker"
```imports -show
import Std.Async
```
```lean -show
open Std.Async
```

A {name}`natTicker` is a selector that makes a {name}`Nat` available every 100 milliseconds, incrementing each time.
Its state is determined by two values:
1. a counter, which is an {name}`IO.Ref` that contains the next {name}`Nat` to emit
2. the time at which the process was started

The {name}`Selector.tryFn` checks whether at least 100ms have elapsed for each emitted `Nat`.
If so, the value is incremented and returned immediately:
```lean
def tickerTryFn (counter : IO.Ref Nat) (startMs : Nat) := do
  let nowMs ← IO.monoMsNow
  let n ← counter.get
  if nowMs ≥ startMs + n * 100 then
    counter.set (n + 1)
    return (some n)
  else
    return none
```

If the race was not immediately run, a waiter is registered.
A background task is launched that sleeps until the next {name}`Nat` is ready, and the waiter's {name Waiter.race}`race` is invoked; if the race is won, then the counter is incremented:
```lean
def tickerRegisterFn (counter : IO.Ref Nat) (startMs : Nat)
    (waiter : Waiter Nat) : Async Unit := do
  let n ← counter.get
  let delay := startMs + n * 100 - (← IO.monoMsNow)
  let sleep ← Sleep.mk <| .ofNat delay
  discard <| background do
    sleep.wait
    waiter.race (pure ()) fun promise => do
      counter.set (n + 1)
      promise.resolve (.ok n)
```
These components can be combined into a selector:
```lean
def natTicker : IO (Selector Nat) := do
  let current ← IO.mkRef 0
  let startMs ← IO.monoMsNow
  return {
    tryFn := tickerTryFn current startMs
    registerFn := tickerRegisterFn current startMs
    unregisterFn := pure ()
  }
```

This selector is not thread-safe.
Multiple uses in a single {name}`Selectable.one` are safe, because they do not lose data (the {name ST.Ref.set}`set` is only invoked when the race has been definitively won).
However, concurrent invocations of {name}`Selectable.one` on the same {name}`natTicker` can lead to data races.
Fixing this requires careful locking.

```lean -show
-- Backs the "multiple uses in a single `Selectable.one`" safety claim above:
-- using the same ticker in two branches of one selection emits each value once.
#eval do
  let t ← natTicker
  let a ← (Selectable.one #[.case t (fun n => return n)]).block
  let b ← (Selectable.one #[
    .case t (fun n => return n),
    .case t (fun n => return n)
  ]).block
  unless a == 0 do throw (IO.userError "natTicker: first tick")
  unless b == 1 do throw (IO.userError "natTicker: shared use in one selection")
```
:::

# Standard Selectors

The standard library includes a number of {tech}[selectors] for events such as timers, receiving values through channels, and {ref "async-network"}[network sockets].
These selectors allow {name}`Async` programs to reliably process inputs from many different sources.

When a selector is built on some data source, it is very important not to use the same data source directly.
For example, {name Std.CloseableChannel.recvSelector}`recvSelector` and {name Std.CloseableChannel.recv}`recv` should not be used on the same channel.
This can lead to violations of the {ref "selector-protocol"}[selector protocol] when the selector relies on exclusive control over the real-world state of the data source.

{docstring Sleep.selector}

{docstring Std.Channel.recvSelector}

{docstring Std.CloseableChannel.recvSelector}

{docstring Std.Broadcast.Receiver.recvSelector}

{docstring Std.Notify.selector}

{docstring Std.CancellationToken.selector}

{docstring Std.CancellationContext.doneSelector}

{docstring Selector.cancelled}

{docstring TCP.Socket.Server.acceptSelector}

{docstring TCP.Socket.Client.recvSelector}

{docstring UDP.Socket.recvSelector}

{docstring Signal.Waiter.selector}

{docstring Std.StreamMap.selector}

# Errors

:::leanSection
```lean -show
variable (α : Type) (ε : Type)
```
Error handling in {name}`Async` mirrors error handling in {name}`IO`:
 * {name}`BaseAsync`, like {name}`BaseIO`, cannot throw an error.
 * {name}`EAsync`, like {name}`EIO`, is parameterized by an error type. Behind the scenes, {lean}`EAsync ε α` is {lean}`BaseAsync (Except ε α)`, and its {name}`Monad` instance is like that of {name}`ExceptT`.
 * {lean}`Async α` is {lean}`EAsync IO.Error α`, just as {lean}`IO α` is {lean}`EIO IO.Error α`.
:::

The details of error handling in {name}`Async` are consequences of this arrangement.
When an asynchronous task (spawned via {name}`async`) throws an exception, this is not observable in the parent.
The error surfaces when the task's result is requested via {name}`await`.
If the task is never {name}`await`ed, *the error vanishes*.
In other words, errors in tasks created via {name}`background` or {name}`ContextAsync.disown` are not propagated at all.

```lean -show
-- Hidden regression tests for the error-handling claims above.

-- A spawned task's error surfaces at `await`, not at `async`:
def caughtAtAwait : Async Nat := do
  let t ← async (m := Async) do
    throw (IO.userError "boom")
  try await t catch _ => return 0
#eval do
  let r ← caughtAtAwait.block
  unless r == 0 do throw (IO.userError "caughtAtAwait")

-- An error in a `background` task is silently swallowed:
def swallowedError : Async String := do
  background (t := AsyncTask) (show Async Unit from throw (IO.userError "lost"))
  sleep 30
  return "no error observed"
#eval do
  let r ← swallowedError.block
  unless r == "no error observed" do throw (IO.userError "swallowedError")

-- An error in a `ContextAsync.disown` task is silently swallowed:
def disownSwallows : Async String := ContextAsync.run do
  ContextAsync.disown (throw (IO.userError "lost") : ContextAsync Unit)
  sleep 30
  return "no error observed"
#eval do
  let r ← disownSwallows.block
  unless r == "no error observed" do throw (IO.userError "disownSwallows")

-- `bind` short-circuits: statements after a throw don't run (like `ExceptT`):
def bindShortCircuits : Async (List Nat) := do
  let log ← IO.mkRef ([] : List Nat)
  try
    log.modify (· ++ [1])
    throw (IO.userError "stop")
    log.modify (· ++ [2])
  catch _ => pure ()
  log.get
#eval do
  let r ← bindShortCircuits.block
  unless r == [1] do throw (IO.userError "bindShortCircuits")

-- A throwing finalizer masks the original error:
def finalizerMasks : Async String := do
  try
    try
      throw (IO.userError "original")
    finally
      (throw (IO.userError "from finalizer") : Async Unit)
  catch e => return (toString e)
#eval do
  let r ← finalizerMasks.block
  unless r == "from finalizer" do throw (IO.userError "finalizerMasks")
```

## Errors and Concurrency
%%%
tag := "errors-and-concurrency"
%%%

The concurrency operators {name}`Async.concurrently` and {name}`Async.concurrentlyAll` await the results of their sub-tasks positionally rather than chronologically.
This means that errors that result from these tasks are reported in source-code order, rather than the chronological order in which the errors occurred.

:::example "Concurrency and Error Propagation"
```imports -show
import Std.Async
```
```lean -show
open Std Async
```
{name}`failFast` waits 5 milliseconds before throwing an exception, while {name}`failSlow` waits 250 milliseconds:
```lean
def failFast : Async Nat := do
  sleep 5
  throw <| .userError "Fast failure"

def failSlow : Async Nat := do
  sleep 250
  throw <| .userError "Slow failure"
```
When run via {name}`Async.concurrently`, the program fails with the error from {name}`failSlow`. Even though it was chronologically produced after the failure from {name}`failFast`, the result of {name}`failSlow` was awaited first.
```lean +error (name := failed)
#eval Async.block do
  let val ← Async.concurrently (prio := .dedicated) failSlow failFast
  pure ()
```
```leanOutput failed
Slow failure
```
:::

{name}`Async.race` and {name}`Async.raceAll` return the result of the _first_ completed task, whether it is a success or a failure.
This means that a quickly-produced error takes precedence over a slowly-produced success.

```lean -show
-- `race` resolves with the first to *finish*: a fast error beats a slow success.
def raceFailFast : Async Nat := do sleep 10; throw (IO.userError "fast failure")
def raceSlowOk : Async Nat := do sleep 100; return 42
#eval do
  let r ← (show IO String from do
    try
      discard <| (Async.race raceFailFast raceSlowOk).block
      return "no error"
    catch e => return (toString e))
  unless r == "fast failure" do throw (IO.userError "raceFailFast")
```

## Errors in Event Selection

During selection, errors might occur at any stage of {ref "async-select"}[the protocol].
Errors thrown by a selector during the initial {name Selector.tryFn}`tryFn` loop terminate the selection immediately.
An error thrown from a {name Selector.registerFn}`registerFn` becomes the selection's result unless the race is already won; in that case, the winner's result takes priority.
Errors thrown in an {name Selector.unregisterFn}`unregisterFn` are suppressed and discarded.
A selector that wins the race may resolve the promise with either {name}`Except.ok` or {name}`Except.error`; in the latter case, the result of the call to {name}`Selectable.one` is itself an error.

```lean -show
-- A tryFn error terminates the selection, even when a sibling is ready.
def tryFnThrower : Selector Nat := {
  tryFn := throw (IO.userError "poll failed")
  registerFn := fun _ => pure ()
  unregisterFn := pure ()
}
def tryFnErrorTerminates : Async Unit := do
  let mut sawError := 0
  for _ in [0:20] do
    let ch ← CloseableChannel.new (α := Nat)
    discard <| ch.send 1
    let r ← try discard <| Selectable.one #[.case ch.recvSelector (fun _ => return 0), .case tryFnThrower (fun _ => return 1)]; pure "" catch e => pure (toString e)
    if r == "poll failed" then sawError := sawError + 1
    else if r != "" then throw (IO.userError s!"tryFnErrorTerminates: {r}")
  -- with random order, the throwing selector is sometimes polled first
  unless sawError > 0 do throw (IO.userError "tryFnErrorTerminates: error never surfaced")
#eval tryFnErrorTerminates.block

-- A registerFn error is discarded when a winner already exists.
def registerErrorAfterWin : Async Unit := do
  let mut valueWon := 0
  for _ in [0:20] do
    let ch ← CloseableChannel.new (α := Nat)
    -- Makes the channel ready, then fails. If the channel was registered first, it wins and the
    -- error is discarded; otherwise registration stops and the error is the result.
    let sendThenThrow : Selector Nat := {
      tryFn := return none
      registerFn := fun _ => do discard <| ch.send 5; throw (IO.userError "ignored")
      unregisterFn := pure ()
    }
    let r ← try Selectable.one #[.case ch.recvSelector (fun n? => return n?.getD 0), .case sendThenThrow (fun n => return n)]
      catch e => if toString e == "ignored" then pure 0 else throw e
    if r == 5 then valueWon := valueWon + 1
    else if r != 0 then throw (IO.userError s!"registerErrorAfterWin: {r}")
  unless valueWon > 0 do throw (IO.userError "registerErrorAfterWin: value never won")
#eval registerErrorAfterWin.block
```

```lean -show
-- An error thrown by the winning continuation propagates out of `Selectable.one`.
def selErrorPropagates : Async String := do
  let ch ← CloseableChannel.new (α := Nat)
  discard <| ch.send 1
  try
    Selectable.one #[.case ch.recvSelector fun _ =>
      throw (IO.userError "cont failed")]
  catch e => return (toString e)
#eval do
  let r ← selErrorPropagates.block
  unless r == "cont failed" do throw (IO.userError "selErrorPropagates")
```

```lean -show
-- When a sibling's registerFn throws, the selection fails with that error, the other
-- selectors are unregistered, and a later send is received rather than consumed by a stale waiter.
def registerErrorThrower : Selector Nat := {
  tryFn := return none
  registerFn := fun _ => throw (IO.userError "boom")
  unregisterFn := pure ()
}
def registerErrorCleansUp : Async Unit := do
  let ch ← CloseableChannel.new (α := Nat)
  let unregistered ← IO.mkRef false
  let victim : Selector Nat := {
    tryFn := return none
    registerFn := fun _ => pure ()
    unregisterFn := unregistered.set true
  }
  let err ← try
      discard <| Selectable.one #[
        .case ch.recvSelector (fun _ => return 0),
        .case victim (fun _ => return 1),
        .case registerErrorThrower (fun _ => return 2)]
      pure ""
    catch e => pure (toString e)
  unless err == "boom" do throw (IO.userError s!"registerErrorCleansUp: got '{err}'")
  unless (← unregistered.get) do throw (IO.userError "registerErrorCleansUp: victim was not unregistered")
  discard <| ch.send 7
  unless (← ch.tryRecv) == some 7 do throw (IO.userError "registerErrorCleansUp: value was consumed by a stale waiter")
#eval registerErrorCleansUp.block
```

```lean -show
-- When a sibling's unregisterFn throws, every other selector is still unregistered and the
-- winning selectable's value is returned.
def unregisterErrorThrower : Selector Nat := {
  tryFn := return none
  registerFn := fun _ => pure ()
  unregisterFn := throw (IO.userError "boom")
}
def unregisterErrorCleansUp : Async Unit := do
  let cleaned ← IO.mkRef false
  let ch ← CloseableChannel.new (α := Nat)
  let victim : Selector Nat := {
    tryFn := return none
    registerFn := fun _ => pure ()
    unregisterFn := cleaned.set true
  }
  -- Sends on the channel during registration, so the channel wins the race rather than the initial poll.
  let sender : Selector Nat := {
    tryFn := return none
    registerFn := fun _ => discard <| ch.send 0
    unregisterFn := pure ()
  }
  let r ← Selectable.one #[
    .case victim (fun _ => return 0),
    .case ch.recvSelector (fun _ => return 1),
    .case unregisterErrorThrower (fun _ => return 2),
    .case sender (fun _ => return 3)]
  unless r == 1 do throw (IO.userError s!"unregisterErrorCleansUp: winner was {r}")
  unless (← cleaned.get) do throw (IO.userError "unregisterErrorCleansUp: victim was not unregistered")
#eval unregisterErrorCleansUp.block
```

# Timers

There are two varieties of timer: _sleep timers_ allow a computation to wait one time for a given duration, while _interval timers_ provide an event repeatedly, separated by the duration.
Creating a timer does not start the countdown.
Timers begin running at the first call to {name}`Sleep.wait`, call to {name}`Interval.tick`, or the first selection in which they take part.
When a sleep timer loses a {ref "selection-protocol-race"}[race], it restarts in its next selection.
Stopping a timer with {name}`Sleep.stop` or {name}`Interval.stop` leaves any task that's awaiting the timer hanging forever.

```lean -show
def timeIt (act : Async α) : Async Nat := do
  let t0 ← IO.monoMsNow
  discard act
  return (← IO.monoMsNow) - t0

-- The countdown of a `Selector.sleep` begins at its first selection, not at creation.
def sleepSelectorStartsLazily : Async Unit := do
  let s ← Selector.sleep 100
  sleep 150
  let ch ← CloseableChannel.new (α := Nat)
  let ms ← timeIt (Selectable.one #[.case ch.recvSelector (fun _ => pure ()), .case s (fun _ => pure ())])
  unless ms ≥ 80 do throw (IO.userError s!"Selector.sleep started before its first selection ({ms} ms)")
#eval sleepSelectorStartsLazily.block

-- A `Selector.sleep` that has fired resolves immediately in later selections.
def sleepSelectorIsSingleShot : Async Unit := do
  let s ← Selector.sleep 100
  let ch ← CloseableChannel.new (α := Nat)
  discard <| Selectable.one #[.case ch.recvSelector (fun _ => pure ()), .case s (fun _ => pure ())]
  let ms ← timeIt (Selectable.one #[.case ch.recvSelector (fun _ => pure ()), .case s (fun _ => pure ())])
  unless ms < 50 do throw (IO.userError s!"Selector.sleep fired again after {ms} ms")
#eval sleepSelectorIsSingleShot.block

-- A `Selector.sleep` that loses a selection restarts its countdown at the next selection.
def sleepSelectorRestartsAfterLoss : Async Unit := do
  let s ← Selector.sleep 100
  let ch ← CloseableChannel.new (α := Nat)
  discard <| background (do sleep 30; discard <| ch.send 1)
  discard <| Selectable.one #[.case ch.recvSelector (fun _ => pure ()), .case s (fun _ => pure ())]
  let ms ← timeIt (Selectable.one #[.case ch.recvSelector (fun _ => pure ()), .case s (fun _ => pure ())])
  unless ms ≥ 80 do throw (IO.userError s!"Selector.sleep kept its countdown after losing ({ms} ms)")
#eval sleepSelectorRestartsAfterLoss.block
```

{docstring sleep}

{docstring Sleep +allowMissing}

{docstring Sleep.mk}

{docstring Sleep.wait}

{docstring Sleep.reset}

{docstring Sleep.stop}

{docstring Interval +allowMissing}

{docstring Interval.mk}

{docstring Interval.tick}

{docstring Interval.reset}

{docstring Interval.stop}

{docstring Selector.sleep}



::::example "Selectors and Timers"
This program runs a loop.
At each iteration, it waits up to two seconds for a line of input.
If the input is provided, then it echoes it and loops again.
If the iteration times out, then the program exits.
Checking for the timeout is done by using {name}`Selectable.one` to race the timer against a channel that delivers the lines of input.
This channel can be selected against, and it is fed by a dedicated thread that reads `stdin`.

:::ioExample
```ioLean
module
import Std.Async
import Std.Sync.Channel
open Std.Async
open Std (CloseableChannel)

-- Blocking reader on a dedicated thread: forward each line, close on EOF.
partial def reader (stdin : IO.FS.Stream) (ch : CloseableChannel String) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then
    discard <| (ch.close).toBaseIO
  else
    discard <| ch.send line
    reader stdin ch

-- Echo each line; stop on EOF (channel closed) or 2s of silence.
partial def echo (ch : CloseableChannel String) : Async Unit := do
  let more ← Selectable.one #[
    .case ch.recvSelector fun
      | some line => do IO.print (s!"got: {line}"); return true
      | none => do IO.println "done"; return false,
    .case (← Selector.sleep 2000) fun _ => do
      IO.println "done"
      return false
  ]
  if more then echo ch

public def main : IO Unit := do
  let ch ← CloseableChannel.new (α := String)
  discard <| IO.asTask (prio := .dedicated) (reader (← IO.getStdin) ch)
  (echo ch).block
```
When run with this input:
```stdin
One line
Another
```
it produces this output:
```stdout
got: One line
got: Another
done
```
:::

::::

# Asynchronous I/O
:::leanSection
```lean -show
open Std.Async.IO
```
The type classes {name}`AsyncRead`, {name}`AsyncWrite`, and {name}`AsyncStream` provide buffered asynchronous I/O.
The main {name}`AsyncRead` instances are {inst}`AsyncRead (Channel α) α`, {inst}`AsyncRead (CloseableChannel α) (Option α)`, and {inst}`AsyncRead (Broadcast.Receiver α) (Option α)`.
Similarly, the main {name}`AsyncWrite` instances are for {inst}`AsyncWrite (Channel α) α`, {inst}`AsyncWrite (CloseableChannel α) α`, and {inst}`AsyncWrite (Broadcast α) α`.
{name}`AsyncStream` has instances for the same types as {name}`AsyncRead`, but provides {tech}[selector]-based iteration of elements so they can be combined with other data sources.
:::

{docstring Std.Async.IO.AsyncRead +allowMissing}

{docstring Std.Async.IO.AsyncWrite +allowMissing}

{docstring Std.Async.IO.AsyncStream +allowMissing}

## Network
%%%
tag := "async-network"
%%%

The standard library provides asynchronous TCP and UDP sockets along with DNS name resolution.
Operations that wait for the network, such as accepting a connection, receiving data, or resolving a name, are {name}`Async` actions.
TCP and UDP sockets additionally provide {tech}[selectors], namely {name}`TCP.Socket.Server.acceptSelector`, {name}`TCP.Socket.Client.recvSelector`, and {name}`UDP.Socket.recvSelector`, so that network events can be multiplexed with other I/O using {ref "async-select"}[event selection].
Socket addresses are represented by the types {name}`Std.Net.SocketAddress` and {name}`Std.Net.IPAddr`.
As with other selectors, a socket's selector and its corresponding blocking operation each expect exclusive control of the socket.
They must not be used at the same time on the same socket.

### TCP

TCP is connection-oriented: a client establishes a connection to a server, after which the two exchange a reliable, ordered stream of bytes.
The protocol includes measures for ensuring that the data that is sent actually arrives, including re-transmission of missing parts; these features rely on having an established connection with its associated state.
A TCP server socket accepts incoming connections, while a TCP client socket connects to a server and exchanges data.
A server is set up by creating it, binding it to an address, listening, and then accepting connections.
A client is created, connected to an address, and then used to send and receive data.

{docstring TCP.Socket.Server +allowMissing}

{docstring TCP.Socket.Server.mk}

{docstring TCP.Socket.Server.bind}

{docstring TCP.Socket.Server.listen}

{docstring TCP.Socket.Server.accept}

{docstring TCP.Socket.Server.tryAccept}

{docstring TCP.Socket.Server.getSockName}

{docstring TCP.Socket.Server.noDelay}

{docstring TCP.Socket.Server.keepAlive}

{docstring TCP.Socket.Client +allowMissing}

{docstring TCP.Socket.Client.mk}

{docstring TCP.Socket.Client.bind}

{docstring TCP.Socket.Client.connect}

{docstring TCP.Socket.Client.send}

{docstring TCP.Socket.Client.sendAll}

{docstring TCP.Socket.Client.recv?}

{docstring TCP.Socket.Client.shutdown}

{docstring TCP.Socket.Client.getPeerName}

{docstring TCP.Socket.Client.getSockName}

{docstring TCP.Socket.Client.noDelay}

{docstring TCP.Socket.Client.keepAlive}

### UDP

Unlike TCP, UDP is connectionless: rather than first establishing a connection, a single socket sends and receives independent messages, called {deftech}_datagrams_, to and from any address.
There is no provision for ensuring that the datagrams actually arrive; with UDP, this is an application-level concern.
A datagram can also be delivered to many recipients at once using broadcast or multicast.

{docstring UDP.Socket.mk}

{docstring UDP.Socket.bind}

{docstring UDP.Socket.connect}

{docstring UDP.Socket.send}

{docstring UDP.Socket.sendAll}

{docstring UDP.Socket.recv}

{docstring UDP.Socket.getSockName}

{docstring UDP.Socket.getPeerName}

{docstring UDP.Socket.setBroadcast}

{docstring UDP.Socket.setTTL}

{docstring UDP.Socket.setMulticastLoop}

{docstring UDP.Socket.setMulticastTTL}

{docstring UDP.Socket.setMulticastInterface}

{docstring UDP.Socket.setMembership}

{docstring UDP.Membership +allowMissing}

### DNS

DNS resolution converts between names and socket addresses.
{name}`DNS.getAddrInfo` performs forward resolution from a host and service to a list of addresses, while {name}`DNS.getNameInfo` performs reverse resolution from an address to a host and service.

{docstring DNS.getAddrInfo}

{docstring DNS.getNameInfo}

{docstring DNS.NameInfo +allowMissing}

## Signals

Unix-style signals are asynchronous notifications that can be received from the operating system at any time.
For example, when a user presses `Ctrl-C`, the `SIGINT` signal is sent to the process.
A {name}`Signal.Waiter` is a Lean representation of an underlying signal handler.
The signals that can be handled are enumerated in the type {name}`Signal`:

{docstring Signal}

Depending on the platform, some signals cannot be caught.
On Unix-like operating systems, `SIGKILL` and `SIGSTOP` can't be caught.
`SIGBUS`, `SIGFPE`, `SIGILL`, or `SIGSEGV` can't be handled because Lean uses `libuv` to install signal handlers, and `libuv` cannot safely catch these signals.
Finally, the Lean run-time system ignores `SIGPIPE`.
On Windows, waiters can be created for `SIGTERM` and `SIGABRT`, but they never fire. `SIGHUP` fires when the console is closed, with approximately ten seconds provided for cleanup. `SIGINT` is not delivered in terminal raw mode, and `SIGWINCH` is emulated and may be untimely.

To install a signal handler, first use {name}`Signal.Waiter.mk` to create a signal waiter.
The handler is installed when the waiter is first used.
The waiter can be used via {name}`Signal.Waiter.wait`, which allows it to be waited for using {name}`await`, but most use cases probably want to use {name}`Signal.Waiter.selector` together with {ref "async-select"}[event selection] to handle arriving signals by canceling ongoing work and cleaning up.
This pattern, and the {name}`Signal.Waiter` API, mirror those of timers; unlike timers, the arrival of a signal is unpredictable.

The `repeating` parameter to {name}`Signal.Waiter.mk` determines whether the waiter awaits a single signal or repeated signals.
If it is {name}`false`, then as soon as a matching signal arrives, the waiter moves into a finished state.
Subsequent selections or calls to {name Signal.Waiter.wait}`wait` immediately return the same data.
If `repeating` is {name}`true`, then subsequent calls to {name Signal.Waiter.wait}`wait` or subsequent selections will block until another signal arrives.
A repeating waiter keeps listening for signals until {name}`Signal.Waiter.stop` is called.

{docstring Signal.Waiter +allowMissing}

{docstring Signal.Waiter.mk}

{docstring Signal.Waiter.wait}

{docstring Signal.Waiter.stop}

{docstring Signal.Waiter.selector}

::::example "Selectors and Signals"
This program runs a loop.
At each iteration, it waits for a line of input or `Ctrl-C`, which sends `SIGINT`.
If the input is provided, then it echoes it and loops again.
If it receives `SIGINT`, then iteration stops and the program terminates.
Checking for the signal is done by using {name}`Selectable.one` to race the signal handler against a channel that delivers the lines of input.
This channel can be selected against, and it is fed by a dedicated thread that reads `stdin`.

:::ioExample
```ioLean
module
import Std.Async
import Std.Sync.Channel
open Std.Async
open Std (CloseableChannel)

-- Blocking reader on a dedicated thread: forward each line, close on EOF.
partial def reader (stdin : IO.FS.Stream) (ch : CloseableChannel String) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then
    discard <| (ch.close).toBaseIO
  else
    discard <| ch.send line
    reader stdin ch

-- Echo each line; stop on EOF (channel closed) or SIGINT (Ctrl-C).
partial def echo (sigint : Signal.Waiter) (ch : CloseableChannel String) : Async Unit := do
  let more ← Selectable.one #[
    .case ch.recvSelector fun
      | some line => do IO.print (s!"got: {line}"); return true
      | none => do IO.println "done"; return false,
    .case sigint.selector fun _ => do
      IO.println "interrupted"
      return false
  ]
  if more then echo sigint ch

public def main : IO Unit := do
  let ch ← CloseableChannel.new (α := String)
  let sigint ← Signal.Waiter.mk .sigint (repeating := true)
  discard <| IO.asTask (prio := .dedicated) (reader (← IO.getStdin) ch)
  (echo sigint ch).block
```
```stdout -show
done
```
:::
::::

# Cancellation

Typical asynchronous applications need to handle _cancellation_, where work needs to be abandoned.
For example, if a user presses `Ctrl-C` or a timeout occurs, then a download may be abandoned and temporary files cleaned up without terminating the entire application.
The {name}`ContextAsync` monad provides tools for managing hierarchical trees of tasks, where canceling a task also cancels its children.

Cancellation is _cooperative_: tasks must explicitly check whether they've been canceled and terminate themselves.
In other words, cancellation is an event that tasks may opt into observing, rather than a mechanism to forcibly terminate other tasks.

:::paragraph
There are two primary ways to cancel a tree of {name}`ContextAsync` computations:

 * {name}`ContextAsync.run` executes a cancelable tree of tasks as an ordinary {name}`Async` task.
  When the root task returns normally, the entire tree is canceled.
 * {name}`ContextAsync.cancel` cancels the current task and all of its children.

For cancellation to work as expected, concurrent tasks should be started with the helpers that are specifically designed for {name}`ContextAsync`.
When this is not possible, use {name}`ContextAsync.runIn` to associate the current cancellation context with the new computation.
:::

{docstring ContextAsync}

{docstring ContextAsync.async}

{docstring ContextAsync.cancel}

{docstring ContextAsync.run}

{docstring ContextAsync.runIn}

{docstring ContextAsync.getContext}

{docstring ContextAsync.background}

{docstring ContextAsync.disown}

{docstring ContextAsync.concurrently}

{docstring ContextAsync.concurrentlyAll}

{docstring ContextAsync.race}

{docstring ContextAsync.raceAll}

## Reacting to Cancellation

Asynchronous computations can react to cancellation via explicit polling with {name}`ContextAsync.isCancelled`.
They can also block until the current context is canceled using {name}`ContextAsync.awaitCancellation`; this is useful when there is no more work to be done until cancellation, but still allows for cleanup.
Finally, cancellation can be awaited together with other events using {tech}[event selection] with {name}`Selector.cancelled` or {name}`ContextAsync.doneSelector` (they are synonymous).

{docstring ContextAsync.isCancelled}

:::example "Observing Cancellation"
```imports -show
import Std.Async
```
```lean -show
open Std.Async
```
{name}`ContextAsync.isCancelled` reports whether the current context has been canceled.
Here, the context is canceled explicitly with {name}`ContextAsync.cancel`:
```lean (name := flagOut)
#eval Async.block <| ContextAsync.run do
  let before ← ContextAsync.isCancelled
  ContextAsync.cancel .cancel
  let after ← ContextAsync.isCancelled
  return (before, after)
```
```leanOutput flagOut
(false, true)
```
:::

:::example "Cooperating with Cancellation"
```imports -show
import Std.Async
```
```lean -show
open Std.Async
```
Because cancellation is cooperative, a long-running computation must check {name}`ContextAsync.isCancelled` itself and stop once it has been canceled.
This worker records numbers until its context is canceled.
The cancellation here comes from the worker itself after three iterations, but in practice it would come from a timeout or a parent task; the worker's reaction is the same:
```lean (name := workerOut)
def worker : ContextAsync (Array Nat) := do
  let log ← IO.mkRef (#[] : Array Nat)
  for i in [0:100] do
    if ← ContextAsync.isCancelled then break
    log.modify (·.push i)
    if i == 2 then ContextAsync.cancel .cancel
  log.get

#eval Async.block <| ContextAsync.run worker
```
```leanOutput workerOut
#[0, 1, 2]
```
:::

{docstring ContextAsync.awaitCancellation}

{docstring Selector.cancelled}

:::example "Interrupting a Wait"
```imports -show
import Std.Async
import Std.Sync.Channel
```
```lean -show
open Std.Async
open Std (CloseableChannel)
```
Cancellation can be awaited alongside other events using {tech}[event selection].
Here, a computation waits for either a value on a channel or cancellation, whichever comes first.
Because the context is canceled before the selection runs, the cancellation branch wins and the result is {name}`none`:
```lean (name := cancelSelOut)
def waitOrCancel (ch : CloseableChannel Nat) : ContextAsync (Option Nat) := do
  Selectable.one #[
    .case ch.recvSelector (fun n? => return n?),
    .case (← Selector.cancelled) (fun _ => return none)
  ]

#eval Async.block <| ContextAsync.run do
  let ch ← CloseableChannel.new (α := Nat)
  ContextAsync.cancel .cancel
  waitOrCancel ch
```
```leanOutput cancelSelOut
none
```
:::

{docstring ContextAsync.doneSelector}

{docstring ContextAsync.getCancellationReason}

## Cancellation Contexts

{name}`ContextAsync` is a {ref "reader-monad"}[reader] on top of {name}`Async` that provides access to a cancellation context.
This context contains an ID and a cancellation token along with a mutex-guarded mutable state that encodes a tree of IDs, each with a cancellation token, and a source of unique ID values.
When child tasks are created, they are assigned new IDs and associated with the current task.
When tasks are canceled, the tree in the state is used to cancel their children.

{docstring Std.CancellationContext +allowMissing}

{docstring Std.CancellationContext.State +allowMissing}

{docstring Std.CancellationContext.new}

{docstring Std.CancellationContext.fork}

{docstring Std.CancellationContext.cancel}

{docstring Std.CancellationContext.isCancelled}

{docstring Std.CancellationContext.getCancellationReason}

{docstring Std.CancellationContext.done}

{docstring Std.CancellationContext.doneSelector}

{docstring Std.CancellationReason}

## Cancellation Tokens

A cancellation token is a mutex-guarded piece of shared mutable state that tracks whether the token has been canceled along with a set of consumers that have requested notification when cancellation occurs.
Behind the scenes, {name}`ContextAsync.isCancelled` checks the current context's cancellation token, then checks whether the cancellation reason is {name}`some` or {name}`none`.

{docstring Std.CancellationToken +allowMissing}

{docstring Std.CancellationToken.State}

{docstring Std.CancellationToken.Consumer +allowMissing}
