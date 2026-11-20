import globals from "globals";
import shared from "./eslint.shared.mjs";

// The browser scripts in static/ are the repository's own JavaScript. The generated sites and
// the dependency directories are left out.
export default [
    {
        ignores: ["**/*.min.js", "node_modules/", ".lake/", "**/.lake/", "_out/", "_tutorial-out/"],
    },
    {
        files: ["**/*.js"],
        languageOptions: {
            ecmaVersion: 2024,
            sourceType: "script",
            globals: { ...globals.browser },
        },
    },
    ...shared,
];
