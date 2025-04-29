/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Meta.ElanCheck
import Manual.Meta.ElanCmd
import Manual.Meta.ElanOpt

open Manual
open Verso.Genre Manual InlineLean


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "Managing Toolchains with Elan" =>
%%%
tag := "elan"
%%%

Elan is the Lean toolchain manager.
It is responsible both for installing {tech}[toolchains] and for running their constituent programs.
Elan makes it possible to seamlessly work on a variety of projects, each of which is designed to be built with a particular version of Lean, without having to manually install and select toolchain versions.
Each project is typically configured to use a particular version, which is transparently installed as needed, and changes to the Lean version are tracked automatically.

# Selecting Toolchains
%%%
tag := "elan-toolchain-versions"
%%%

When using Elan, the version of each tool on the {envVar}`PATH` is a proxy that invokes the correct version.
The proxy determines the appropriate toolchain version for the current context, ensures that it is installed, and then invokes the underlying tool in the appropriate toolchain installation.
These proxies can be instructed to use a specific version by passing it as an argument prefixed with `+`, so `lake +4.0.0` invokes `lake` version `4.0.0`, after installing it if necessary.


## Toolchain Identifiers
%%%
tag := "elan-channels"
%%%

Toolchains are specified by providing a toolchain identifier that is either a {deftech}_channel_, which identifies a particular type of Lean release, and optionally an origin, or a {deftech}_custom toolchain name_ established by {elan}`toolchain link`.
Channels may be:

 : `stable`

  The latest stable Lean release. Elan automatically tracks stable releases and offers to upgrade when a new one is released.

 : `nightly`

   The latest nightly build. Nightly builds are useful for experimenting with new Lean features to provide feedback to the developers.

 : A version number or specific nightly release

    Each Lean version number identifies a channel that contains only that release.
    The version number may optionally be preceded with a `v`, so `v4.17.0` and `4.17.0` are equivalent.
    Similarly, `nightly-YYYY-MM-DD` specifies the nightly release from the specified date.
    A project's {tech}[toolchain file] should typically contain a specific version of Lean, rather than a general channel, to make it easier to coordinate between developers and to build and test older versions of the project.
    An archive of Lean releases and nightly builds is maintained.

 : A custom local toolchain

    The command {elan}`toolchain link` can be used to establish a custom toolchain name in Elan for a local build of Lean.
    This is especially useful when working on the Lean compiler itself.

Specifying an {deftech}_origin_ instructs Elan to install Lean toolchains from a particular source.
By default, this is the official project repository on GitHub, identified as [`leanprover/lean4`](https://github.com/leanprover/lean4/releases).
If specified, an origin should precede the channel, with a colon, so `stable` is equivalent to `leanprover/lean4:stable`.
When installing nightly releases, `-nightly` is appended to the origin, so `leanprover/lean4:nightly-2025-03-25` consults the [`leanprover/lean4-nightly`](https://github.com/leanprover/lean4-nightly/releases) repository to download releases.
Origins are not used for custom toolchain names.

## Determining the Current Toolchain
%%%
tag := "elan-toolchain-config"
%%%

Elan associates toolchains with directories, and uses the toolchain of the most recent parent directory of the current working directory that has a configured toolchain.
A directory's toolchain may result from a toolchain file or from an override configured with {ref "elan-override"}[`elan override`].

The current toolchain is determined by first searching for a configured toolchain for the current directory, walking up through parent directories until a toolchain version is found or there are no more parents.
A directory has a configured toolchain if there is a configured {tech}[toolchain override] for the directory or if it contains a `lean-toolchain` file.
More recent parents take precedence over their ancestors, and if a directory has both an override and a toolchain file, then the override takes precedence.
If no directory toolchain is found, then Elan's configured {deftech}_default toolchain_ is used as a fallback.

The most common way to configure a Lean toolchain is with a {deftech}_toolchain file_.
The toolchain file is a text file named `lean-toolchain` that contains a single line with a valid {ref "elan-channels"}[toolchain identifier].
This file is typically located in the root directory of a project and checked in to version control with the code, ensuring that everyone working on the project uses the same version.
Updating to a new Lean toolchain requires only editing this file, and the new version is automatically downloaded and run the next time a Lean file is opened or built.

In certain advanced use cases where more flexibility is required, a {deftech}_toolchain override_ can be configured.
Like toolchain files, overrides associate a toolchain version with a directory and its children.
Unlike toolchain files, overrides are stored in Elan's configuration rather than in a local file.
They are typically used when a specific local configuration is required that does not make sense for other developers, such as testing a project with a locally-built Lean compiler.

# Toolchain Locations
%%%
tag := "elan-dir"
%%%

By default, Elan stores installed toolchains in `.elan/toolchains` in the user's home directory, and its proxies are kept in `.elan/bin`, which is added to the path when Elan is installed.
The environment variable {envVar def:=true}`ELAN_HOME` can be used to change this location.
It should be set both prior to installing Elan and in all sessions that use Lean in order to ensure that Elan's files are found.

# Command-Line Interface
%%%
tag := "elan-cli"
%%%

In addition to the proxies that automatically select, install, and invoke the correct versions of Lean tools, Elan provides a command-line interface for querying and configuring its settings.
This tool is called `elan`.
Like {ref "lake"}[Lake], its command-line interface is structured around subcommands.

Elan can be invoked with following flags:

 : {elanOptDef flag}`--help` or {elanOptDef flag}`-h`

  Describes the current subcommand in detail.

 : {elanOptDef flag}`--verbose` or {elanOptDef flag}`-v`

  Enables verbose output.

 : {elanOptDef flag}`--version` or {elanOptDef flag}`-V`

  Displays the Elan version.



```elanHelp
The Lean toolchain installer

USAGE:
    elan [FLAGS] <SUBCOMMAND>

FLAGS:
    -v, --verbose    Enable verbose output
    -h, --help       Prints help information
    -V, --version    Prints version information

SUBCOMMANDS:
    show           Show the active and installed toolchains
    default        Set the default toolchain
    toolchain      Modify or query the installed toolchains
    override       Modify directory toolchain overrides
    run            Run a command with an environment configured for a given toolchain
    which          Display which binary will be run for a given command
    self           Modify the elan installation
    completions    Generate completion scripts for your shell
    help           Prints this message or the help of the given subcommand(s)

DISCUSSION:
    elan manages your installations of the Lean theorem prover.
    It places `lean` and `lake` binaries in your `PATH` that automatically
    select and, if necessary, download the Lean version described in your
    project's `lean-toolchain` file. You can also install, select, run,
    and uninstall Lean versions manually using the commands of the `elan`
    executable.
```

## Querying Toolchains
%%%
tag := "elan-show"
%%%

The {elan}`show` command displays the current toolchain (as determined by the current directory) and lists all installed toolchains.


```elanHelp "show"
elan-show
Show the active and installed toolchains

USAGE:
    elan show

FLAGS:
    -h, --help    Prints help information

DISCUSSION:
    Shows the name of the active toolchain and the version of `lean`.

    If there are multiple toolchains installed then all installed
    toolchains are listed as well.
```

:::elan show
Shows the name of the active toolchain and the version of `lean`.

If there are multiple toolchains installed, then they are all listed.
:::

Here is typical output from {elan}`show` in a project with a `lean-toolchain` file:
```
installed toolchains
--------------------

leanprover/lean4:nightly-2025-03-25
leanprover/lean4:v4.17.0  (resolved from default 'stable')
leanprover/lean4:v4.16.0
leanprover/lean4:v4.9.0

active toolchain
----------------

leanprover/lean4:v4.9.0 (overridden by '/PATH/TO/PROJECT/lean-toolchain')
Lean (version 4.9.0, arm64-apple-darwin23.5.0, commit 8f9843a4a5fe, Release)
```
The `installed toolchains` section lists all the toolchains currently available on the system.
The `active toolchain` section identifies the current toolchain and describes how it was selected.
In this case, the toolchain was selected due to a `lean-toolchain` file.


## Setting the Default Toolchain
%%%
tag := "elan-default"
%%%

Elan's configuration file specifies a {tech}[default toolchain] to be used when there is no `lean-toolchain` file or {tech}[toolchain override] for the current directory.
Rather than manually editing the file, this value is typically changed using the {elan}`default` command.

```elanHelp "default"
elan-default
Set the default toolchain

USAGE:
    elan default <toolchain>

FLAGS:
    -h, --help    Prints help information

ARGS:
    <toolchain>    Toolchain name, such as 'stable', 'nightly', or '3.3.0'. For more information see `elan help
                   toolchain`

DISCUSSION:
    Sets the default toolchain to the one specified.
```

:::elan default "toolchain"
Sets the default toolchain to {elanMeta}`toolchain`, which should be a {ref "elan-channels"}[valid toolchain identifier] such as `stable`, `nightly`, or `4.17.0`.
:::

## Managing Installed Toolchains
%%%
tag := "elan-toolchain"
%%%

The `elan toolchain` family of subcommands is used to manage the installed toolchains.
Toolchains are stored in Elan's {ref "elan-dir"}[toolchain directory].

Installed toolchains can take up substantial disk space.
Elan tracks the Lean projects in which it is invoked, saving a list.
This list of projects can be used to determine which toolchains are in active use and automatically delete unused toolchain versions with {elan}`toolchain gc`.

```elanHelp "toolchain"
elan-toolchain
Modify or query the installed toolchains

USAGE:
    elan toolchain <SUBCOMMAND>

FLAGS:
    -h, --help    Prints help information

SUBCOMMANDS:
    list         List installed toolchains
    install      Install a given toolchain
    uninstall    Uninstall a toolchain
    link         Create a custom toolchain by symlinking to a directory
    gc           Garbage-collect toolchains not used by any known project
    help         Prints this message or the help of the given subcommand(s)

DISCUSSION:
    Many `elan` commands deal with *toolchains*, a single
    installation of the Lean theorem prover. `elan` supports multiple
    types of toolchains. The most basic track the official release
    channels: 'stable' and 'nightly'; but `elan` can also
    install toolchains from the official archives and from local builds.

    Standard release channel toolchain names have the following form:

        [<origin>:]<channel>[-<date>]

        <channel>       = stable|nightly|<version>
        <date>          = YYYY-MM-DD

    'channel' is either a named release channel or an explicit version
    number, such as '4.0.0'. Channel names can be optionally appended
    with an archive date, as in 'nightly-2023-06-27', in which case
    the toolchain is downloaded from the archive for that date.
    'origin' can be used to refer to custom forks of Lean on Github;
    the default is 'leanprover/lean4'. For nightly versions, '-nightly'
    is appended to the value of 'origin'.

    elan can also manage symlinked local toolchain builds, which are
    often used to for developing Lean itself. For more information see
    `elan toolchain help link`.
```

```elanHelp "toolchain" "list"
elan-toolchain-list
List installed toolchains

USAGE:
    elan toolchain list

FLAGS:
    -h, --help    Prints help information
```

:::elan toolchain list
Lists the currently-installed toolchains. This is a subset of the output of {elan}`show`.
:::

```elanHelp "toolchain" "install"
elan-toolchain-install
Install a given toolchain

USAGE:
    elan toolchain install <toolchain>...

FLAGS:
    -h, --help    Prints help information

ARGS:
    <toolchain>...    Toolchain name, such as 'stable', 'nightly', or '3.3.0'. For more information see `elan help
                      toolchain`
```

:::elan toolchain install "toolchain"
Installs the indicated {elanMeta}`toolchain`.
The toolchain's name should be {ref "elan-channels"}[an identifier that's suitable for inclusion in a `lean-toolchain` file].
:::


```elanHelp "toolchain" "uninstall"
elan-toolchain-uninstall
Uninstall a toolchain

USAGE:
    elan toolchain uninstall <toolchain>...

FLAGS:
    -h, --help    Prints help information

ARGS:
    <toolchain>...    Toolchain name, such as 'stable', 'nightly', or '3.3.0'. For more information see `elan help
                      toolchain`
```

:::elan toolchain uninstall "toolchain"
Uninstalls the indicated {elanMeta}`toolchain`.
The toolchain's name should the name of an installed toolchain.
Use {elan}`toolchain list` to see the installed toolchains with their names.
:::

```elanHelp "toolchain" "link"
elan-toolchain-link
Create a custom toolchain by symlinking to a directory

USAGE:
    elan toolchain link <toolchain> <path>

FLAGS:
    -h, --help    Prints help information

ARGS:
    <toolchain>    Toolchain name, such as 'stable', 'nightly', or '3.3.0'. For more information see `elan help
                   toolchain`
    <path>

DISCUSSION:
    'toolchain' is the custom name to be assigned to the new toolchain.

    'path' specifies the directory where the binaries and libraries for
    the custom toolchain can be found. For example, when used for
    development of Lean itself, toolchains can be linked directly out of
    the Lean root directory. After building, you can test out different
    compiler versions as follows:

        $ elan toolchain link master <path/to/lean/root>
        $ elan override set master

    If you now compile a crate in the current directory, the custom
    toolchain 'master' will be used.
```


:::elan toolchain link "«local-name» path"

Creates a new local toolchain named {elanMeta}`local-name`, using the Lean toolchain found at {elanMeta}`path`.

:::


```elanHelp "toolchain" "gc"
elan-toolchain-gc
Garbage-collect toolchains not used by any known project

USAGE:
    elan toolchain gc [FLAGS]

FLAGS:
        --delete    Delete collected toolchains instead of only reporting them
    -h, --help      Prints help information
        --json      Format output as JSON

DISCUSSION:
    Experimental. A toolchain is classified as 'in use' if
    * it is the default toolchain,
    * it is registered as an override, or
    * there is a directory with a `lean-toolchain` file referencing the
      toolchain and elan has been used in the directory before.

    For safety reasons, the command currently requires passing `--delete`
    to actually remove toolchains but this may be relaxed in the future
    when the implementation is deemed stable.
```

:::elan toolchain gc "[\"--delete\"] [\"--json\"]"

This command is still considered experimental.

Determines which of the installed toolchains are in use, offering to delete those that are not.
All the installed toolchains are listed, separated into those that are in use and those that are not.

A toolchain is classified as “in use” if
 * it is the default toolchain,
 * it is registered as an override, or
 * there is a directory with a `lean-toolchain` file referencing the toolchain and elan has been used in the directory before.

For safety reasons, {elan}`toolchain gc` will not actually delete any toolchains unless the {elanOptDef flag}`--delete` flag is passed.
This may be relaxed in the future when the implementation is deemed sufficiently mature.
The {elanOptDef flag}`--json` flag causes {elan}`toolchain gc` to emit the list of used and unused toolchains in a JSON format that's suitable for other tools.
:::

## Managing Directory Overrides
%%%
tag := "elan-override"
%%%

Directory-specific {tech}[toolchain overrides] are a local configuration that takes precedence over `lean-toolchain` files.
The `elan override` commands manage overrides.

```elanHelp "override"
elan-override
Modify directory toolchain overrides

USAGE:
    elan override <SUBCOMMAND>

FLAGS:
    -h, --help    Prints help information

SUBCOMMANDS:
    list     List directory toolchain overrides
    set      Set the override toolchain for a directory
    unset    Remove the override toolchain for a directory
    help     Prints this message or the help of the given subcommand(s)

DISCUSSION:
    Overrides configure elan to use a specific toolchain when
    running in a specific directory.

    elan will automatically select the Lean toolchain specified in
    the `lean-toolchain` file when inside a Lean package, but
    directories can also be assigned their own Lean toolchain manually
    with `elan override`. When a directory has an override then any
    time `lean` or `lake` is run inside that directory, or one of
    its child directories, the override toolchain will be invoked.

    To pin to a specific nightly:

        $ elan override set nightly-2023-09-06

    Or a specific stable release:

        $ elan override set 4.0.0

    To see the active toolchain use `elan show`. To remove the
    override and use the default toolchain again, `elan override
    unset`.
```



:::elan override list
Lists all the currently configured directory overrides in two columns.
The left column contains the directories in which the Lean version is overridden, and the right column lists the toolchain version.
:::


:::elan override set "toolchain"
Sets {elanMeta}`toolchain` as an override for the current directory.
:::




:::elan override unset "[\"--nonexistent\"] [\"--path\" path]"
If {elanOptDef flag}`--nonexistent` flag is provided, all overrides that are configured for directories that don't currently exist are removed.
If {elanOptDef option}`--path` is provided, then the override set for {elanMeta}`path` is removed.
Otherwise, the override for the current directory is removed.
:::

## Running Tools and Commands
%%%
tag := "elan-run"
%%%

The commands in this section provide the ability to run a command in a specific toolchain and to locate a tool from a particular toolchain on disk.
This can be useful when experimenting with different Lean versions, for cross-version testing, and for integrating Elan with other tools.

```elanHelp "run"
elan-run
Run a command with an environment configured for a given toolchain

USAGE:
    elan run [FLAGS] <toolchain> <command>...

FLAGS:
    -h, --help       Prints help information
        --install    Install the requested toolchain if needed

ARGS:
    <toolchain>     Toolchain name, such as 'stable', 'nightly', or '3.3.0'. For more information see `elan help
                    toolchain`
    <command>...

DISCUSSION:
    Configures an environment to use the given toolchain and then runs
    the specified program. The command may be any program, not just
    lean or lake. This can be used for testing arbitrary toolchains
    without setting an override.

    Commands explicitly proxied by `elan` (such as `lean` and
    `lake`) also have a shorthand for this available. The toolchain
    can be set by using `+toolchain` as the first argument. These are
    equivalent:

        $ lake +nightly build

        $ elan run --install nightly lake build
```

:::elan run "[\"--install\"] toolchain command ..."
Configures an environment to use the given toolchain and then runs the specified program.
The toolchain will be installed if the {elanOptDef flag}`--install` flag is provided.
The command may be any program; it does not need to be a command that's part of a toolchain such as `lean` or `lake`.
This can be used for testing arbitrary toolchains without setting an override.
:::

```elanHelp "which"
elan-which
Display which binary will be run for a given command

USAGE:
    elan which <command>

FLAGS:
    -h, --help    Prints help information

ARGS:
    <command>
```

:::elan which "command"
Displays the full path to the toolchain-specific binary for {elanMeta}`command`.
:::

## Managing Elan
%%%
tag := "elan-self"
%%%

Elan can manage its own installation.
It can upgrade itself, remove itself, and help configure tab completion for many popular shells.

```elanHelp "self"
elan-self
Modify the elan installation

USAGE:
    elan self <SUBCOMMAND>

FLAGS:
    -h, --help    Prints help information

SUBCOMMANDS:
    update       Download and install updates to elan
    uninstall    Uninstall elan.
    help         Prints this message or the help of the given subcommand(s)
```


```elanHelp "self" "update"
elan-self-update
Download and install updates to elan

USAGE:
    elan self update

FLAGS:
    -h, --help    Prints help information
```
:::elan self update
Downloads and installs updates to Elan itself.
:::

:::elan self uninstall
Uninstalls Elan.
:::

```elanHelp "completions"
elan-completions
Generate completion scripts for your shell

USAGE:
    elan completions [shell]

FLAGS:
    -h, --help    Prints help information

ARGS:
    <shell>     [possible values: zsh, bash, fish, powershell, elvish]

DISCUSSION:
    One can generate a completion script for `elan` that is
    compatible with a given shell. The script is output on `stdout`
    allowing one to re-direct the output to the file of their
    choosing. Where you place the file will depend on which shell, and
    which operating system you are using. Your particular
    configuration may also determine where these scripts need to be
    placed.

    Here are some common set ups for the three supported shells under
    Unix and similar operating systems (such as GNU/Linux).

    BASH:

    Completion files are commonly stored in `/etc/bash_completion.d/`.
    Run the command:

        $ elan completions bash > /etc/bash_completion.d/elan.bash-completion

    This installs the completion script. You may have to log out and
    log back in to your shell session for the changes to take affect.

    BASH (macOS/Homebrew):

    Homebrew stores bash completion files within the Homebrew directory.
    With the `bash-completion` brew formula installed, run the command:

        $ elan completions bash > $(brew --prefix)/etc/bash_completion.d/elan.bash-completion

    FISH:

    Fish completion files are commonly stored in
    `$HOME/.config/fish/completions`. Run the command:

        $ elan completions fish > ~/.config/fish/completions/elan.fish

    This installs the completion script. You may have to log out and
    log back in to your shell session for the changes to take affect.

    ZSH:

    ZSH completions are commonly stored in any directory listed in
    your `$fpath` variable. To use these completions, you must either
    add the generated script to one of those directories, or add your
    own to this list.

    Adding a custom directory is often the safest bet if you are
    unsure of which directory to use. First create the directory; for
    this example we'll create a hidden directory inside our `$HOME`
    directory:

        $ mkdir ~/.zfunc

    Then add the following lines to your `.zshrc` just before
    `compinit`:

        fpath+=~/.zfunc

    Now you can install the completions script using the following
    command:

        $ elan completions zsh > ~/.zfunc/_elan

    You must then either log out and log back in, or simply run

        $ exec zsh

    for the new completions to take affect.

    CUSTOM LOCATIONS:

    Alternatively, you could save these files to the place of your
    choosing, such as a custom directory inside your $HOME. Doing so
    will require you to add the proper directives, such as `source`ing
    inside your login script. Consult your shells documentation for
    how to add such directives.

    POWERSHELL:

    The powershell completion scripts require PowerShell v5.0+ (which
    comes Windows 10, but can be downloaded separately for windows 7
    or 8.1).

    First, check if a profile has already been set

        PS C:\> Test-Path $profile

    If the above command returns `False` run the following

        PS C:\> New-Item -path $profile -type file -force

    Now open the file provided by `$profile` (if you used the
    `New-Item` command it will be
    `%USERPROFILE%\Documents\WindowsPowerShell\Microsoft.PowerShell_profile.ps1`

    Next, we either save the completions file into our profile, or
    into a separate file and source it inside our profile. To save the
    completions into our profile simply use

        PS C:\> elan completions powershell >>
%USERPROFILE%\Documents\WindowsPowerShell\Microsoft.PowerShell_profile.ps1
```

:::elan completions "shell"
Generates shell completion scripts for Elan, enabling tab completion for Elan commands in a variety of shells.
See the output of `elan help completions` for a description of how to install them.
:::
