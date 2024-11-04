# External Contribution Guidelines

Thank you for helping out with the Lean reference manual!

In the interest of getting as much documentation as possible written quickly, while still maintaining a consistent voice and style and keeping the technical quality high, all contributions will either be carefully reviewed. However, because review can be very time consuming, we may decline to review some contributions. This means that slow-to-review PRs may just be closed. Nobody wants this to happen, so please get in touch to discuss your plans to contribute ahead of time so we can agree on suitable parameters.

## Issues

Issues are a great way to communicate your priorities and needs for documentation, and they are an important input into our planning and prioritization process as we write the Lean reference manual. Please upvote issues that are important to you. Pithy technical examples as comments to documentation requests are also an incredibly useful contribution.

## Small Fixes

Pull requests that fix typos and small mistakes are welcome. Please don't group too many in one PR, which makes them difficult to review.

## External Content

Please remember to get in touch ahead of time to plan a contribution. In general, text included in the reference manual should live up to the following:
 * Empirical claims about Lean should be tested, either via examples or hidden test cases.
 * Examples should be clearly marked as such, separating the description of the system from the illustrative examples.
 * Technical terms should be introduced using the `deftech` role and referred to using the `tech` role.
 * Write in US English, deferring to the Chicago Manual of Style when in doubt. Exceptions to this style may be added and documented.
 * One sentence per line, to make diffs easier to follow.

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
