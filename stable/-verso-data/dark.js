function setInput() {
  const checkbox = document.querySelector('input.change-theme');
  if (checkbox) {
    checkbox.checked = document.documentElement.classList.contains('dark-theme');
  }
}

function setFavicon(path) {
  let link = document.querySelector("link[rel~='icon']");
  if (!link) {
    link = document.createElement('link');
    link.rel = 'icon';
    document.head.appendChild(link);
  }
  link.href = path;
}

function applyTheme(theme) {
  const root = document.documentElement;

  if (theme === 'dark') {
    root.classList.add('dark-theme');
    root.classList.remove('light-theme');
  } else {
    root.classList.add('light-theme');
    root.classList.remove('dark-theme');
  }

  setInput();
}

function getStored(key) {
  try {
    return localStorage.getItem(key);
  } catch (e) {
    console.warn(`localStorage get failed for ${key}:`, e);
    return null;
  }
}

function setStored(key, value) {
  try {
    localStorage.setItem(key, value);
  } catch (e) {
    console.warn(`localStorage set failed for ${key}:`, e);
  }
}

function updateFaviconForSystemTheme(systemTheme) {
  const iconPath = systemTheme === 'dark'
    ? '/static/favicon-light.ico'
    : '/static/favicon-dark.ico';

  setFavicon(iconPath);
}

function registerTheme() {
  const mediaQuery = window.matchMedia('(prefers-color-scheme: dark)');
  const currentSystemTheme = mediaQuery.matches ? 'dark' : 'light';

  const storedSystemTheme = getStored('theme-system');
  const storedLocalTheme = getStored('theme-local');

  updateFaviconForSystemTheme(currentSystemTheme);

  if (storedSystemTheme !== currentSystemTheme) {
    if (!storedLocalTheme || storedLocalTheme === storedSystemTheme) {
      setStored('theme-local', currentSystemTheme);
      applyTheme(currentSystemTheme);
    } else {
      applyTheme(storedLocalTheme);
    }
  } else {
    applyTheme(storedLocalTheme || currentSystemTheme);
  }

  setInput();

  const themeToggleBtns = document.querySelectorAll('.change-theme');
  themeToggleBtns.forEach((btn) => {
    btn.addEventListener('click', () => {
      const isDark = document.documentElement.classList.contains('dark-theme');
      const newTheme = isDark ? 'light' : 'dark';

      setStored('theme-local', newTheme);
      applyTheme(newTheme);
    });
  });

  mediaQuery.addEventListener('change', (e) => {
    const newSystemTheme = e.matches ? 'dark' : 'light';
    const oldSystemTheme = getStored('theme-system');
    const localTheme = getStored('theme-local');

    if (newSystemTheme !== oldSystemTheme) {
      setStored('theme-system', newSystemTheme);
      updateFaviconForSystemTheme(newSystemTheme);

      if (!localTheme || localTheme === oldSystemTheme) {
        setStored('theme-local', newSystemTheme);
        applyTheme(newSystemTheme);
      }
    }
  });
}

window.addEventListener('DOMContentLoaded', () => {
  registerTheme();
})
