// Open all details tags when printing.
//
// From https://stackoverflow.com/questions/19646684/force-open-the-details-summary-tag-for-print-in-chrome

window.matchMedia("print").addEventListener("change", (evt) => {
    if (evt.matches) {
        /** @type {NodeListOf<HTMLDetailsElement>} */
        const elms = document.body.querySelectorAll("details:not([open])");
        for (const e of elms) {
            e.setAttribute("open", "");
            e.dataset["wasclosed"] = "";
        }
    } else {
        /** @type {NodeListOf<HTMLDetailsElement>} */
        const elms = document.body.querySelectorAll("details[data-wasclosed]");
        for (const e of elms) {
            e.removeAttribute("open");
            delete e.dataset["wasclosed"];
        }
    }
});
