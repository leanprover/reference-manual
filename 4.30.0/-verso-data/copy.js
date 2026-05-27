document.addEventListener("DOMContentLoaded", () => {

  const targets = [
    ...document.querySelectorAll("pre"),
    ...document.querySelectorAll("code.hl.lean.block")
  ];

  targets.forEach((el, idx) => {
    const button = document.createElement("button");
    button.textContent = "Copy";
    button.classList.add("copy-button");

    const wrapper = document.createElement("div");
    wrapper.classList.add("code-block-wrapper");

    el.parentNode.insertBefore(wrapper, el);
    wrapper.appendChild(el);
    wrapper.appendChild(button);

    button.addEventListener("click", () => {
      const text = el.innerText;
      navigator.clipboard.writeText(text.trim()).then(() => {
        button.textContent = "Copied!";
        setTimeout(() => (button.textContent = "Copy"), 1500);
      }).catch(err => {
        console.error("Copy failed", err);
        button.textContent = "Error";
      });
    });
  });
});
