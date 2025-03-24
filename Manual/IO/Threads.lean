/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual
open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "Tasks and Threads" =>
%%%
tag := "concurrency"
%%%

:::leanSection
```lean (show := false)
variable {α : Type u}
```

{name}`Task` is the fundamental primitive for writing multi-threaded code.
A {lean}`Task α` represents a computation that, at some point, will {deftech}_resolve_ to a value of type `α`; it may be computed on a separate thread.
When a task has resolved, its value can be read; attempting to get the value of a task before it resolves causes the current thread to block until the task has resolved.
Tasks are similar to promises in JavaScript, `JoinHandle` in Rust, and `Future` in Scala.

Tasks may either carry out pure computations or {name}`IO` actions.
The API of pure tasks resembles that of {tech}[thunks]: {name}`Task.spawn` creates a {lean}`Task α` from a function in {lean}`Unit → α`, and {name}`Task.get` waits until the function's value has been computed and then returns it.
The value is cached, so subsequent requests do not need to recompute it.
The key difference lies in when the computation occurs: while the values of thunks are not computed until they are forced, tasks execute opportunistically in a separate thread.

Tasks in {name}`IO` are created using {name}`IO.asTask`.
Similarly, {name}`BaseIO.asTask` and {name}`EIO.asTask` create tasks in other {name}`IO` monads.
These tasks may have side effects, and can communicate with other tasks.
:::

When the last reference to a task is dropped it is {deftech key:="cancel"}_cancelled_.
Pure tasks created with {name}`Task.spawn` are terminated upon cancellation.
Tasks spawned with {name}`IO.asTask`, {name}`EIO.asTask`, or {name}`BaseIO.asTask` continue executing and must explicitly check for cancellation using {name}`IO.checkCanceled`.
Tasks may be explicitly cancelled using {name}`IO.cancel`.

The Lean runtime maintains a thread pool for running tasks.
The size of the thread pool is determined by the environment variable {envVar (def := true)}`LEAN_NUM_THREADS` if it is set, or by the number of logical processors on the current machine otherwise.
The size of the thread pool is not a hard limit; in certain situations it may be exceeded to avoid deadlocks.
By default, these threads are used to run tasks; each task has a {deftech}_priority_ ({name}`Task.Priority`), and higher-priority tasks take precedence over lower-priority tasks.
Tasks may also be assigned to dedicated threads by spawning them with a sufficiently high priority.

{docstring Task (label := "type") (hideStructureConstructor := true) (hideFields := true)}

# Creating Tasks

Pure tasks should typically be created with {name}`Task.spawn`, as {name}`Task.pure` is a task that's already been resolved with the provided value.
Impure tasks are created by one of the {name BaseIO.asTask}`asTask` actions.

## Pure Tasks

Pure tasks may be created outside the {name}`IO` family of monads.
They are terminated when the last reference to them is dropped.

{docstring Task.spawn}

{docstring Task.pure}

## Impure Tasks

When spawning a task with side effects using one of the {name IO.asTask}`asTask` functions, it's important to actually execute the resulting {name}`IO` action.
A task is spawned each time the resulting action is executed, not when {name IO.asTask}`asTask` is called.
Impure tasks continue running even when there are no references to them, though this does result in cancellation being requested.
Cancellation may also be explicitly requested using {name}`IO.cancel`.
The impure task must check for cancellation using {name}`IO.checkCanceled`.

{docstring BaseIO.asTask}

{docstring EIO.asTask}

{docstring IO.asTask}

## Priorities

Task priorities are used by the thread scheduler to assign tasks to threads.
Within the priority range {name Task.Priority.default}`default`–{name Task.Priority.max}`max`, higher-priority tasks always take precedence over lower-priority tasks.
Tasks spawned with priority {name Task.Priority.dedicated}`dedicated` are assigned their own dedicated threads and do not contend with other tasks for the threads in the thread pool.

{docstring Task.Priority}

{docstring Task.Priority.default}

{docstring Task.Priority.max}

{docstring Task.Priority.dedicated}

# Task Results

{docstring Task.get}

{docstring IO.wait}

{docstring IO.waitAny}

# Sequencing Tasks

These operators create new tasks from old ones.
When possible, it's good to use {name}`Task.map` or {name}`Task.bind` instead of manually calling {name}`Task.get` in a new task because they don't temporarily increase the size of the thread pool.

{docstring Task.map}

{docstring Task.bind}

{docstring Task.mapList}

{docstring BaseIO.mapTask}

{docstring EIO.mapTask}

{docstring IO.mapTask}

{docstring BaseIO.mapTasks}

{docstring EIO.mapTasks}

{docstring IO.mapTasks}

{docstring BaseIO.bindTask}

{docstring EIO.bindTask}

{docstring IO.bindTask}

{docstring BaseIO.chainTask}

{docstring EIO.chainTask}

{docstring IO.chainTask}

# Cancellation and Status

Impure tasks should use `IO.checkCanceled` to react to cancellation, which occurs either as a result of `IO.cancel` or when the last reference to the task is dropped.
Pure tasks are terminated automatically upon cancellation.

{docstring IO.cancel}

{docstring IO.checkCanceled}

{docstring IO.hasFinished}

{docstring IO.getTaskState}

{docstring IO.TaskState}

{docstring IO.getTID}

# Promises

Promises represent a value that will be supplied in the future.
Supplying the value is called {deftech key:="resolve"}_resolving_ the promise.
Once created, a promise can be stored in a data structure or passed around like any other value, and attempts to read from it will block until it is resolved.


{docstring IO.Promise}

{docstring IO.Promise.new}

{docstring IO.Promise.isResolved}

{docstring IO.Promise.result?}

{docstring IO.Promise.result!}

{docstring IO.Promise.resultD}

{docstring IO.Promise.resolve}

# Communication Between Tasks

In addition to the types and operations described in this section, {name}`IO.Ref` can be used as a lock.
Taking the reference (using {name ST.Ref.take}`take`) causes other threads to block when reading until the reference is {name ST.Ref.set}`set` again.
This pattern is described in {ref "ref-locks"}[the section on reference cells].

## Channels

The types and functions in this section are available after importing {module}`Std.Sync.Channel`.

{docstring Std.Channel}

{docstring Std.Channel.new}

{docstring Std.Channel.send}

{docstring Std.Channel.recv?}

{docstring Std.Channel.close}

{docstring Std.Channel.forAsync}

{docstring Std.Channel.recvAllCurrent}

{docstring Std.Channel.sync}

{docstring Std.Channel.Sync}

{docstring Std.Channel.Sync.recv?}

:::leanSection
```lean (show := false)
variable {m : Type → Type v} {α : Type} [MonadLiftT BaseIO m]
```
Synchronous channels can also be read using {keywordOf Lean.Parser.Term.doFor}`for` loops.
In particular, there is an instance of type {inst}`ForIn m (Std.Channel.Sync α) α` for every monad {lean}`m` with a {inst}`MonadLiftT BaseIO m` instance.
:::
## Mutexes

The types and functions in this section are available after importing {module}`Std.Sync.Mutex`.

{docstring Std.Mutex (allowMissing := true) (label := "type") (hideFields := true)}

{docstring Std.Mutex.new}

{docstring Std.Mutex.atomically}

{docstring Std.Mutex.atomicallyOnce}

{docstring Std.AtomicT}


## Condition Variables

The types and functions in this section are available after importing {module}`Std.Sync.Mutex`.

{docstring Std.Condvar}

{docstring Std.Condvar.new}

{docstring Std.Condvar.wait}

{docstring Std.Condvar.notifyOne}

{docstring Std.Condvar.notifyAll}

{docstring Std.Condvar.waitUntil}
