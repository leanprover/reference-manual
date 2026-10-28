document.addEventListener('DOMContentLoaded', () => {
    initNavHighlight();
    initDropdownArrows();
    initDropdownKeyboard();
});

// Sliding highlight that follows hovered nav links
function initNavHighlight() {
    document.querySelectorAll('.desktop-menu-part').forEach(menu => {
        const links = menu.querySelectorAll('.nav-link');
        if (!links.length) return;

        const highlight = document.createElement('div');
        highlight.className = 'nav-hover-highlight';
        menu.style.position = 'relative';
        menu.appendChild(highlight);

        let currentTarget = null;

        function moveHighlight(el) {
            const menuRect = menu.getBoundingClientRect();
            const elRect = el.getBoundingClientRect();
            const x = elRect.left - menuRect.left;
            const y = elRect.top - menuRect.top;

            if (currentTarget === null) {
                // Snap to position on first hover, then enable transitions
                highlight.style.transition = 'none';
                highlight.style.left = x + 'px';
                highlight.style.top = y + 'px';
                highlight.style.width = elRect.width + 'px';
                highlight.style.height = elRect.height + 'px';
                highlight.getBoundingClientRect(); // force reflow
                highlight.style.transition = '';
                highlight.classList.add('visible');
            } else {
                highlight.style.left = x + 'px';
                highlight.style.top = y + 'px';
                highlight.style.width = elRect.width + 'px';
                highlight.style.height = elRect.height + 'px';
            }
            currentTarget = el;
        }

        links.forEach(link => {
            link.addEventListener('mouseenter', () => moveHighlight(link));
        });

        menu.addEventListener('mouseleave', () => {
            highlight.classList.remove('visible');
            currentTarget = null;
        });
    });
}

// CSS-transition chevron for dropdowns
function initDropdownArrows() {
    document.querySelectorAll('.nav-dropdown-wrapper').forEach(wrapper => {
        wrapper.addEventListener('mouseenter', () => wrapper.classList.add('is-open'));
        wrapper.addEventListener('mouseleave', () => wrapper.classList.remove('is-open'));
    });
}

// Keyboard: close dropdown on Escape
function initDropdownKeyboard() {
    document.querySelectorAll('.nav-dropdown-wrapper').forEach(wrapper => {
        document.addEventListener('keydown', (e) => {
            if (e.key === 'Escape' && wrapper.matches(':hover')) {
                wrapper.querySelector('.nav-dropdown-trigger')?.blur();
            }
        });
    });
}
