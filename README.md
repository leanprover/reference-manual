# Mathlib Documentation

**WIP: Jon Eugster 24/01/2025. Wait and see :)**

## Reading the Manual

The latest release of this reference manual can be read [here](nowhere).

## Code origin / Installation

This is all adapted code from the [Lean Language Reference](https://github.com/leanprover/reference-manual) which has been repurposed to
display mathlib text. **You should check there for installation instructions.**

Any problems not directly related to the content itself are probably carried over from there, too...

## Building the Reference Manual Locally

To build the manual, run the following command:

```
lake exe generate-manual --depth 2
```

Then run a local web server on its output:
```
python3 -m http.server 8880 --directory _out/html-multi
```

Then open <http://localhost:8880> in your browser.

## Development

In theory, one should be able to update this by calling a simple

```
lake update
```

However, this requires Verso to be compatible with the Lean version Mathlib uses.

## Contributing

We happily accept content around Mathlib to this guide.

