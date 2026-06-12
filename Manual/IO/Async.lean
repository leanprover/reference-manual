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

Infinite loops in {name}`EAsync` and {name}`Async` use a special instance of {name}`ForIn` that ensures that they don't consume stack frames.
They can therefore be used in long-running asynchronous applications such as servers without the stack overflowing.

Each of these monads has a corresponding type of asynchronous tasks that it can coordinate.
These tasks can be thought of as handles to an in-flight computation.
Calling {name}`async` on a monadic action creates a task that runs in the current thread until it suspends, and calling {name}`await` on a task results in a monadic action that waits for the task to complete.

{docstring ETask}

{docstring AsyncTask}

{docstring MaybeTask +allowMissing}

Crucially, calling {name}`await` on a task never blocks an OS-level thread.
Threads are only blocked at the {ref "async-run"}[boundary] between the {name}`IO` and the {name}`Async` monads.
Under the hood, asynchronous tasks are invoked when needed by the `libuv` event loop.

Asynchronous tasks use the same system of {tech (key := "task priority")}[priorities] as {ref "concurrency"}[other Lean tasks], and are run by the same scheduler.

## Running Asynchronous Computations
%%%
tag := "async-run"
%%%

Asynchronous computations can be run from {name}`IO` by either waiting or blocking.
When a thread waits on an asynchronous computation, the asynchronous computation is run on the thread that is waiting.
When a thread blocks on an asynchronous computation or task, the computation is run on a worker thread in an ordinary {tech}[task] with the specified priority, and the calling thread calls {name}`Task.get` to block on the result.
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
While tasks from {name}`IO.asTask` are synchronous, occupying their worker thread until completed, tasks from {name}`EAsync.asTask` release their worker threads at suspension points and are reinvoked as needed by the `libuv` event loop.

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

In addition to instances for the {name}`Async` monads and tasks, the library includes instances that allow reader and state monad transformers to be used with {name}`async` and {name}`await`.

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
open Std
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
open Std
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
```lean
#eval show IO _ from do
  let ch ← CloseableChannel.new (α := Nat)
  discard <| ch.send 42
  (recv ch).block
```
If not, the timer wins:
```lean
#eval show IO _ from do
  let ch ← CloseableChannel.new (α := Nat)
  -- nothing sent: the timeout wins
  (recv ch).block
```
:::

:::example "Selection"
```imports -show
import Std.Async
import Std.Sync.Channel
```
```lean -show
open Std
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
```lean
#eval show IO _ from do
  let ch1 ← CloseableChannel.new (α := Nat)
  let ch2 ← CloseableChannel.new (α := Nat)
  discard <| ch1.send 1
  (recv2 ch1 ch2).block
```

```lean
#eval show IO _ from do
  let ch1 ← CloseableChannel.new (α := Nat)
  let ch2 ← CloseableChannel.new (α := Nat)
  discard <| ch2.send 2
  (recv2 ch1 ch2).block
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


{name}`Selectable.one` throws an exception when passed an empty array of selectables, because it's impossible to get a value from nothing.
{name}`Selectable.tryOne` always returns {name}`none` when passed an empty array.

Event selection is {deftech}_fair_.
This means that there is an equal probability that any of the selectables with currently-resolved selectors have an equal chance of winning and having their associated code invoked.
This is important because a bias in event selection can lead to one of the selectables _never_ being called, which can in turn cause data to accumulate without bound in the source it would have handled.
Behind the scenes, fairness is ensured by randomizing the order of selectables each time.

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
It consults each selector's non-blocking poll {name}`Selector.tryFn` until one of them returns {name}`some`.
This is the winning selectable; its code is invoked and no further work is needed.
On this fast path, only one selector is ever consumed, so there is no risk of data loss or double delivery.

If no selector was resolved in the first iteration (that is, each {name Selector.tryFn}`tryFn` returned {name}`none`), then it is necessary to wait until one of the selectors is resolved.
Waiting consists of first registering a waiter with each selector; the first selector that has data wins the race via the waiters.
The winning selector consumes its event, invokes code to clean up the other waiting selectors, computes the selectable's value, and resolves an overall promise that {name}`Selectable.one` is blocked on.

More specifically, this is done by creating an atomic flag (indicating that a winner has been selected) and a promise for the result of {name}`Selectable.one`.
A _registration loop_ processes each selectable in the array:
1. The system checks whether the flag is now set, indicating that a prior selector has won the race. If so, the loop terminates.
2. A {tech}[waiter] is registered with the selector using {name}`Selector.registerFn`.
  This registration process may not consume data; it merely registers interest in data should it become available. The waiter includes a reference to the atomic flag along with a promise that can be resolved with the selector's data.
  The selector must call {name Waiter.race}`race` on the waiter when the event has occurred, but it may only consume data if it wins the race.
3. A task is created that observes the waiter's promise.
  When the promise is resolved, indicating that it has won the race, this _completion callback_ is invoked with {name}`none` if the promise was dropped (e.g. due to cancellation or unregistering); in this case, it should do nothing. If it is invoked with {name}`some` around the result, then it must run an {name}`Async` computation that:
  a. propagates any error indicated by the data source's result,
  b. blocks until the entire registration loop is complete,
  c. unregisters the waiter from every selectable in the array using its {name}`Selector.unregisterFn`, and
  d. runs the winning selectable's code, resolving the result promise.

When the registration loop is complete, an internal promise is resolved that unblocks the winning waiter's callback.
This block ensures that all registration occurs before all cleanup.

Finally, {name}`Selectable.one` awaits the overall result promise, which will be resolved as soon as there is a winning callback.

### Waiters

A {deftech}_waiter_ is a means of atomically selecting a single offered value.
Internally, it contains an atomic flag that indicates that a winner has been selected.
When a client has a value, it calls {name}`Waiter.race` with two callbacks: one is used when the offered value was not accepted (it did not win the race), the other is used when it is accepted.
The callback that wins the race should resolve the waiter's promise, which is provided to the winning callback.
This two-phase protocol ensures that there is no data loss, because selectors only consume events once they've already won the race.

{docstring Waiter +allowMissing}

{docstring Waiter.race}

{docstring Waiter.withPromise}

{docstring Waiter.checkFinished}

:::example "Natural Number Ticker"

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
After sleeping until the next {name}`Nat` is ready, the waiter's {name Waiter.race}`race` is invoked; if the race is won, then the counter is incremented:
```lean
def tickerRegisterFn (counter : IO.Ref Nat) (startMs : Nat)
    (waiter : Waiter Nat) : Async Unit := do
  let n ← counter.get
  let delay := startMs + n * 100 - (← IO.monoMsNow)
  let sleep ← Sleep.mk <| .ofNat delay
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
An error thrown from a {name Selector.registerFn}`registerFn` or {name Selector.unregisterFn}`unregisterFn`, by contrast, can leave selectors that were already registered without a matching call to {name Selector.unregisterFn}`unregisterFn`.
A selector that wins the race may resolve the promise with either {name}`Except.ok` or {name}`Except.error`; in the latter case, the result of the call to {name}`Selectable.one` is itself an error.

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
-- This test ensures that the documented error handling in selectors is still the case, as we have
-- discussed changing it. If this test fails, then the text almost certainly needs updating.
def selectionErrorThrower : Selector Nat := {
  tryFn := return none
  registerFn := fun _ => throw (IO.userError "boom")
  unregisterFn := pure ()
}
def selectionLeaks : IO Bool := do
  for _ in [0:50] do
    let ch ← CloseableChannel.new (α := Nat)
    try
      discard <| (Selectable.one #[
        .case ch.recvSelector (fun _ => return 0),
        .case selectionErrorThrower (fun _ => return 1)]).block
    catch _ => pure ()
    discard <| ch.send 7
    IO.sleep 5
    match ← ch.tryRecv with
    | some _ => pure ()        -- value survived: no leak this run, retry
    | none   => return true    -- value vanished: a leaked waiter consumed it
  return false
#eval do
  unless (← selectionLeaks) do
    throw (IO.userError "a selector is no longer leaked when a sibling's registerFn throws; the selection error-safety behavior may have changed, so update this section")
```

```lean -show
-- This test ensures that the documented error handling in selectors is still the case, as we have
-- discussed changing it. If this test fails, then the text almost certainly needs updating.
def unregisterErrorThrower : Selector Nat := {
  tryFn := return none
  registerFn := fun _ => pure ()
  unregisterFn := throw (IO.userError "boom")
}
def unregisterSkipsCleanup : IO Bool := do
  for _ in [0:50] do
    let cleaned ← IO.mkRef false
    let chB ← CloseableChannel.new (α := Nat)
    let victim : Selector Nat := {
      tryFn := return none
      registerFn := fun _ => pure ()
      unregisterFn := cleaned.set true
    }
    -- send to chB after registration completes, so chB wins and the cleanup loop runs
    discard <| IO.asTask (prio := .dedicated) do
      IO.sleep 15; discard <| chB.send 0
    try
      discard <| (Selectable.one #[
        .case victim (fun _ => return 0),
        .case chB.recvSelector (fun _ => return 1),
        .case unregisterErrorThrower (fun _ => return 2)]).block
    catch _ => pure ()
    IO.sleep 50              -- the cleanup loop runs after `block` returns
    unless (← cleaned.get) do return true   -- the thrower aborted cleanup before the victim
  return false
#eval do
  unless (← unregisterSkipsCleanup) do
    throw (IO.userError "a selector's unregisterFn is no longer skipped when a sibling's unregisterFn throws; the selection error-safety behavior may have changed, so update this section")
```

# Timers

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

Sleep.stop/Interval.stop leave pending waits hanging forever, and Selector.sleep's timer only starts once it's used inside a Selectable.

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

To install a signal handler, use {name}`Signal.Waiter.mk` to register a signal itself.
The waiter can be used via {name}`Signal.Waiter.wait`, which allows it to be waited for using {name}`await`, but most use cases probably want to use {name}`Signal.Waiter.selector` together with {ref "async-select"}[event selection] to handle arriving signals by canceling ongoing work and cleaning up.
This pattern, and the {name}`Signal.Waiter` API, mirror those of timers; unlike timers, the arrival of a signal is unpredictable.

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

 * {name}`ContextAsync.run` executes a cancellable tree of tasks as an ordinary {name}`Async` task.
  When the root task is completed, the entire tree is canceled.
 * {name}`ContextAsync.cancel` cancels the current task and all of its children.

For cancellation to work as expected, concurrent tasks should be started with the helpers that are specifically designed for {name}`ContextAsync`.
When this is not possible, use {name}`ContextAsync.runIn` to associate the current cancellation context with the new computation.
:::

{docstring ContextAsync}

{docstring ContextAsync.cancel}

{docstring ContextAsync.run}

{docstring ContextAsync.runIn}

{docstring ContextAsync.background}

{docstring ContextAsync.disown}

{docstring ContextAsync.concurrently}

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
This context contains an ID along with a mutex-guarded mutable state that encodes a tree of IDs, each with a cancellation token, and a source of unique ID values.
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
Behind the scenes, {name}`ContextAsync.isCancelled` checks the current context to get the token for the current task's ID, then checks whether the cancellation reason is {name}`some` or {name}`none`.

{docstring Std.CancellationToken +allowMissing}

{docstring Std.CancellationToken.State}

{docstring Std.CancellationToken.Consumer +allowMissing}
