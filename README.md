# Lean Language Reference

## Reading the Manual

The output of building the current state of the `main` branch can be read at <https://lean-reference-manual-draft.netlify.app/>.

## Building the Reference Manual

To read the manual, run the following command:

```
lake exe generate-manual --depth 2
```

Then run a local web server on its output:
```
python3 -m http.server 8880 --directory _out/html-multi &
```

Then open <http://localhost:8880> in your browser.
