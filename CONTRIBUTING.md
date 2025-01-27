# External Contribution Guidelines

Thank you for helping out with the Lean reference manual!

In the interest of getting as much documentation as possible written quickly, while still maintaining a consistent voice and style and keeping the technical quality high, all contributions will either be carefully reviewed. However, because review can be very time consuming, we may decline to review some contributions. This means that slow-to-review PRs may just be closed. Nobody wants this to happen, so please get in touch to discuss your plans to contribute ahead of time so we can agree on suitable parameters.

## Issues

Issues are a great way to communicate your priorities and needs for documentation, and they are an important input into our planning and prioritization process as we write the Lean reference manual. Please upvote issues that are important to you. Pithy technical examples as comments to documentation requests are also an incredibly useful contribution.

## Small Fixes

Pull requests that fix typos and small mistakes are welcome. Please don't group too many in one PR, which makes them difficult to review.

## Substantial Content

Please remember to get in touch ahead of time to plan a larger contribution. In general, text included in the reference manual should live up to the following:
 * Empirical claims about Lean should be tested, either via examples or hidden test cases.
 * Examples should be clearly marked as such, separating the description of the system from the illustrative examples.
 * Technical terms should be introduced using the `deftech` role and referred to using the `tech` role.
 * Write in US English, deferring to the Chicago Manual of Style when in doubt. Exceptions to this style may be added and documented.
 * One sentence per line, to make diffs easier to follow.

## Markup

The reference manual is written in Verso's manual genre.
In addition to what Verso provides, there are a number of additional roles, code block styles, and directives:

### Roles

Please use the following roles where they make sense:

 * `` {lean}`TERM` `` - `TERM` is a Lean term, to be elaborated as such and included it in the rendered document with appropriate highlighting.
   The optional named argument `type` specifies an expected type, e.g. `` {lean type:="Nat"}`.succ .zero` ``

 * `` {name}`X` `` - `X` is a constant in the Lean environment.
   The optional positional argument can be used to override name resolution; if it is provided, then the positional argument is used to resolve the name but the contents of the directive are rendered.
   `` {name Lean.Elab.Command.CommandElabM}`CommandElabM` `` renders as `CommandElabM` with the metadata from the full name.

 * `` {keywordOf KIND}`KW` `` - `KW` is an atom from the syntax kind `KIND`.

 * `` {keyword}`KW` `` - `KW` is an atom from an unspecified syntax kind.
 
 * `` {tactic}`TAC` `` - `TAC` is a tactic name
 
 * `` {option}`OPT` `` - `OPT` is the name of an option

 * `{TODO}[...]` specifies a task to be rendered in draft versions of the manual

### Code Blocks

 * `lean` specifies that the code block contains Lean commands. The named arguments are:
   * `name` - names the code block for later reference in `leanOutput`
   * `keep` - whether to keep or discard changes made to the environment (default: `true`) 
   * `error` - the code is expected to contain an error (default: `false`)

 * `leanTerm` specifies that the code block contains a Lean term. The named arguments are:
   * `name` - names the code block for later reference in `leanOutput`
   * `keep` - whether to keep or discard changes made to the environment (default: `true`) 
   * `error` - the code is expected to contain an error (default: `false`)

 * `leanOutput NAME` specifies that the code block contains an output from a prior `lean` block.
   The optional named argument `severity` restricts the output to information, warning, or error output.
   
 * `signature` specifies that the code block contains the signature of an existing constant.
 
 * `syntaxError NAME` specifies that the code block contains invalid Lean syntax, and saves the message under `NAME` for `leanOutput`.
   The optional named argument `category` specifies the syntactic category (default: `term`).

### Directives

 * `:::TODO` specifies a task to be rendered in draft versions of the manual
 * `:::example NAME` indicates an example. `NAME` is a string literal that contains valid Verso inline markup.
   Unless the named argument `keep` is `true`, changes made to the Lean environment in the example are discarded.
   Within an `example`, `lean` blocks are elaborated before paragraphs, so inline `lean` roles can refer to names defined later in the example.
 * `:::planned N` describes content that is not yet written, tracked at issue `N` in this repository
 * `:::syntax` describes the syntax of a Lean construct, using a custom DSL based on Lean's quasiquotation mechanism.
   This allows the Lean parser to validate the description, while at the same time decoupling the specifics of the implementation from the structure of the documentation.
 
## CI

The CI requires that various checks are passed.

One of them is that the text must live up to a number of rules written with Vale. The style implementation is still quite incomplete; just because your prose passes the linter doesn't mean it will necessarily be accepted!

To run the check, first install Vale. The next step is to preprocess the generated HTML to remove features that Vale can't cope with. Finally, Vale itself can be run.

To preprocess the HTML, use the script `.vale/scripts/rewrite_html.py`. It requires BeautifulSoup, so here's the overall steps to get it working the first time:

```
$ cd .vale/scripts
$ python3 -m venv venv
$ . ./venv/bin/activate # or the appropriate script for your shell, e.g. activate.fish
$ pip install beautifulsoup4
```
After that, just run
```
$ . .vale/scripts/venv/bin/activate
```
to set up the Python environment.

The next step is to run this on Verso's output. If it's in `_out/html-multi`, do this via:
```
$ cd _out
$ python ../.vale/scripts/rewrite_html.py html-multi html-vale
```

Now, run `vale`:
```
$ vale html-vale
```

### Deployments from PRs

To enable contributions from external forks while allowing HTML previews, the CI does the following:
 1. `ci.yml` builds the HTML for the pull request and saves it to artifact storage
 2. `label-pr.yml` is triggered when `ci.yml` completes. It (re)labels the
    PR with `HTML available` to indicate that the artifact was built.
 3. Whenever the label is added, `pr-deploy.yml` runs _in the context
    of `main`_ with access to secrets. It can deploy the previews.

The second two steps run the CI code on `main`, not the config from the PR.
