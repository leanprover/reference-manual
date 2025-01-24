# Mathlib Documentation


## Reading the Manual

WIP: Jon Eugster 24/01/2025. Wait and see :)

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
python3 -m http.server 8880 --directory _out/html-multi &
```

Then open <http://localhost:8880> in your browser.

## Contributing

We happily accept content around Mathlib to this guide.

