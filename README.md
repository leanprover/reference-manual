# Mathlib Documentation


## Reading the Manual

WIP: Jon Eugster 24/01/2025. Wait and see :)

The latest release of this reference manual can be read [here]().

For developers:
 * The output of building the current state of the `main` branch can be read [here](https://lean-reference-manual-review.netlify.app/).
 * Each pull request in this repository causes two separate previews to be generated, one with extra information that's only useful to those actively working on the text, such as TODO notes and symbol coverage progress bars. These are posted by a bot to the PR after the first successful build.

## Installation

### MacOS

```
brew install poppler
```

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

Please see [CONTRIBUTING.md](CONTRIBUTING.md) for more information.

