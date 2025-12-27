# Mathlib Documentation

## Reading the Manual

The latest release of this Mathlib manual can be read [here](https://leanprover-community.github.io/mathlib-manual/html-multi/).

## Code origin / Installation

This is mostly adapted code from the [Lean Language Reference](https://github.com/leanprover/reference-manual). **You should check there for installation instructions.**

Any problems beyond the content itself are probably carried over from there, and might need fixing there.

## Building the Manual Locally


To build the manual, run the following command:

```
lake exe generate-manual --depth 2
```

Then run a local web server on its output:
```
python3 ./server.py 8880 &
```

Then open <http://localhost:8880> in your browser.

## Development

In theory, one should be able to update this by setting the desired toolchain in `lean-toolchain` and then call

```
lake update
```

However, this requires Verso to be compatible with the Lean version Mathlib uses.

## Contributing

We happily accept content!
