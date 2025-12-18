/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoBlog
import VersoWeb.Theme

import VersoWeb.Components.Footer
import VersoWeb.Components.NavBar

open Verso Genre Blog Output Html Multi
open Web Components Theme

namespace LeanLangOrg

/--
Default footer configuration with all standard links
-/
def footer : FooterConfig := {
  columns := #[
    -- Get Started column
    {
      heading := "Get Started"
      headingId := some "get-started"
      ariaLabel := some "LEAN"
      items := #[
        { title := "Install", url := "/install" },
        { title := "Learn", url := "/learn" },
        { title := "Community", url := "/community" },
        { title := "Reservoir", url := "https://reservoir.lean-lang.org/", blank := true }
      ]
    },
    -- Documentation column
    {
      heading := "Documentation"
      headingId := some "documentation"
      ariaLabel := some "Documentation"
      items := #[
        { title := "Language reference", url := "/doc/reference/latest/" },
        { title := "Lean API", url := "/doc/api/" },
        { title := "Use cases", url := "/use-cases" },
        { title := "Cite Lean", url := "/learn#how-to-cite-lean" }
      ]
    },
    -- Resources column
    {
      heading := "Resources"
      headingId := some "resources"
      ariaLabel := some "Resources"
      items := #[
        { title := "Lean playground", url := "https://live.lean-lang.org/?from=lean", blank := true },
        { title := "VS Code extension", url := "https://marketplace.visualstudio.com/items?itemName=leanprover.lean4", blank := true },
        { title := "Loogle", url := "https://loogle.lean-lang.org/", blank := true },
        { title := "Mathlib", url := "https://github.com/leanprover-community/mathlib4", blank := true }
      ]
    },
    -- FRO column
    {
      heading := "FRO"
      headingId := some "fro"
      ariaLabel := some "FRO"
      items := #[
        { title := "Vision", url := "/fro" },
        { title := "Team", url := "/fro/team" },
        { title := "Roadmap", url := "/fro/roadmap/y3" },
        { title := "Contact", url := "/fro/contact" }
      ]
    },
    -- Policies column
    {
      heading := "Policies"
      headingId := some "policies"
      ariaLabel := some "Policies"
      items := #[
        { title := "Privacy Policy", url := "/privacy" },
        { title := "Terms of Use", url := "/terms" },
        { title := "Lean Trademark Policy", url := "/trademark-policy" }
      ]
    }
  ]
  socialLinks := #[
    { url := "https://bsky.app/profile/lean-lang.org", icon := Icon.blueskyLogo, ariaLabel := some "Bluesky" },
    { url := "https://www.linkedin.com/company/lean-fro", icon := Icon.linkedinLogo, ariaLabel := some "LinkedIn" },
    { url := "https://functional.cafe/@leanprover", icon := Icon.mastodonLogo, ariaLabel := some "Mastodon" },
    { url := "https://x.com/leanprover", icon := Icon.xLogo, ariaLabel := some "X (Twitter)" },
    { url := "https://leanprover.zulipchat.com/", icon := Icon.zulipLogo, ariaLabel := some "Zulip" },
    { url := "https://github.com/leanprover/", icon := Icon.githubLogo, ariaLabel := some "GitHub" }
  ]
  copyrightText := "© 2025 Lean FRO. All rights reserved."
  showThemeSwitcher := true
}

/--
Helper to create FRO home navigation item
-/
def navFroItem (path : Path) : NavBarItem :=
  { title := .text false "Home"
  , url := some "/fro"
  , active := path == #["fro"] }

/--
Function to get all the items that redirect to pages.
-/
def getPageItems : TemplateM (Array NavBarItem) := do
  let links ← Verso.Web.Util.getDirLinks
  return links.map fun (active, url, title) => { title, url, active }

def isFro (path : Path) : Bool := path[0]?.isEqSome "fro"

/--
Build NavBarConfig for FRO section
-/
def buildFroNavBarConfig : TemplateM NavBarConfig := do
  let leftItems ← getPageItems
  let path ← currentPath

  let froPathItems (path : Path) : Array NavBarItem := #[
    { title := .text false "About", url := some "/fro/about", active := path == #["fro", "about"] },
    { title := .text false "Team", url := some "/fro/team", active := path == #["fro", "team"] },
    { title := .text false "Roadmap", url := some "/fro/roadmap", active := path == #["fro", "roadmap"] },
    { title := .text false "Contact", url := some "/fro/contact", active := path == #["fro", "contact"] }
  ]

  let externalLinks : Array NavBarItem := #[
    { title := .text false "Playground", url := some "https://live.lean-lang.org/?from=lean", blank := true },
    { title := .text false "Reservoir", url := some "https://reservoir.lean-lang.org/", blank := true }
  ]

  let rightItems : Array NavBarItem := #[
    { title := Icon.moon, alt := some "Change Theme", classes := some "change-theme" },
    { title := Icon.github, alt := some "Github", url := some "https://github.com/leanprover/lean4", blank := true }
  ]

  let menuItems := #[navFroItem path] ++ froPathItems path

  return {
    leftItems := leftItems
    rightItems := rightItems
    menuItems := menuItems
    externalLinks := externalLinks
    subNavBar := if isFro path then some (SubNavBarConfig.mk (froPathItems path)) else none
  }

def socialMeta : SocialMeta :=
  { title := "Lean Programming Language",
    description := "Lean is an open-source programming language and proof assistant that enables correct, maintainable, and formally verified code.",
    image := "https://lean-lang.org/static/png/banner.png",
    url := "https://lean-lang.org",
    siteName := "Lean Language",
    alt := "Lean Programming Language",
    articleCreator := "@leanprover",
  }

def headConfig : HeadConfig :=
  { description := socialMeta.description,
    faviconWhite := "https://lean-lang.org/static/favicon-light.ico",
    faviconDark := "https://lean-lang.org/static/favicon-dark.ico",
    appleTouchIcon := "https://lean-lang.org/static/apple-touch-icon.png",
    color := "#3D6AC9"
  }

/--
Default theme configuration with all design tokens
-/
def colorTheme : ThemeConfig := {
  variables := [
    -- Typography
    { name := "font-primary", value := "'Open Sans', Arial, sans-serif" },
    { name := "font-secondary", value := "'Oranienbaum', serif" },
    { name := "fs-xs", value := "0.75rem" },
    { name := "fs-sm", value := "0.875rem" },
    { name := "fs-base", value := "1rem" },
    { name := "fs-md", value := "17px" },
    { name := "fs-lg", value := "1.25rem" },
    { name := "fs-xl", value := "2rem" },
    { name := "fs-2xl", value := "3.3rem" },

    -- Spacing
    { name := "space-1", value := "0.25rem" },
    { name := "space-2", value := "0.5rem" },
    { name := "space-3", value := "0.75rem" },
    { name := "space-4", value := "1rem" },
    { name := "space-5", value := "1.25rem" },
    { name := "space-6", value := "1.5rem" },
    { name := "space-8", value := "2rem" },
    { name := "space-10", value := "2.5rem" },
    { name := "space-12", value := "3rem" },
    { name := "space-13", value := "3.5rem" },
    { name := "space-14", value := "4rem" },
    { name := "space-16", value := "5rem" },

    -- Semantic spacing
    { name := "gap-sm", value := "var(--space-2)" },
    { name := "gap-md", value := "10px" },
    { name := "gap-lg", value := "30px" },
    { name := "gap-xl", value := "100px" },

    -- Section padding
    { name := "section-padding", value := "var(--space-10)" },
    { name := "section-padding-top", value := "var(--space-16)" },

    -- Border Radius
    { name := "radius-sm", value := "0.25rem" },
    { name := "radius-md", value := "0.5rem" },
    { name := "radius-lg", value := "1rem" },
    { name := "radius-pill", value := "9999px" },

    -- Sizes
    { name := "container-width", value := "1240px" },
    { name := "logo-size", value := "1.25rem" },
    { name := "logo-footer-size", value := "60px" },
    { name := "icon-size", value := "64px" },

    -- Layout
    { name := "nav-padding-y", value := "var(--space-6)" },
    { name := "nav-padding-x", value := "10vw" },
    { name := "nav-height", value := "calc(var(--nav-padding-y) * 2 + 2em)" },

    -- Transitions
    { name := "transition-fast", value := "0.2s" },
    { name := "transition-base", value := "0.3s" },
    { name := "transition-slow", value := "0.6s" },
    { name := "transition-delay-none", value := "0s" },
    { name := "transition-delay-small", value := "0.05s" },
    { name := "transition-delay-medium", value := "0.1s" },
    { name := "transition-delay-large", value := "0.15s" },

    -- Animation
    { name := "animation-delay", value := "10000ms" },

    -- Z-Index
    { name := "z-below", value := "-1" },
    { name := "z-normal", value := "0" },
    { name := "z-above", value := "1" },
    { name := "z-header", value := "1000" },

    -- Colors
    { name := "color-surface", value := "#fff" },
    { name := "color-primary", value := "#386EE0" },
    { name := "color-primary-focus", value := "#1D4ED8" },
    { name := "color-primary-light", value := "#4a90e2" },
    { name := "color-secondary", value := "#607D8B" },
    { name := "color-text", value := "#333" },
    { name := "color-text-contrast", value := "white" },
    { name := "color-text-light", value := "#64748b" },
    { name := "color-muted", value := "#607D8B" },
    { name := "color-bg", value := "#F9FBFD" },
    { name := "color-bg-translucent", value := "rgba(249, 251, 253, 0.81)" },
    { name := "color-white", value := "#fff" },
    { name := "color-border", value := "#E4EBF3" },
    { name := "color-border-nav", value := "#E4EBF3" },
    { name := "color-border-light", value := "#D1D9E2" },
    { name := "color-hover", value := "rgba(56, 110, 224, 0.08)" },
    { name := "color-link-hover", value := "#0073e6" },
    { name := "color-shadow", value := "rgba(35, 55, 139, 0.1)" },

    -- Components
    { name := "btn-bg", value := "var(--color-primary)" },
    { name := "btn-text", value := "var(--color-white)" },
    { name := "btn-font", value := "var(--font-primary)" },
    { name := "btn-radius", value := "var(--radius-md)" },

    -- Card specific
    { name := "card-bg", value := "var(--color-white)" },
    { name := "card-border", value := "var(--color-border-light)" },

    -- Testimonial specific
    { name := "testimonial-bg", value := "var(--color-primary)" },
    { name := "testimonial-text", value := "var(--color-white)" }
  ],

  darkVariables := [

    -- Dark theme color overrides
    { name := "color-surface", value := "#121212" },
    { name := "color-primary", value := "#3b94ff" },
    { name := "color-primary-focus", value := "#669df6" },
    { name := "color-primary-light", value := "#6aadfe" },
    { name := "color-secondary", value := "#aabfc9" },
    { name := "color-text", value := "#eee" },
    { name := "color-text-light", value := "#bbb" },
    { name := "color-text-contrast", value := "white" },
    { name := "color-muted", value := "#90a4ae" },
    { name := "color-bg", value := "#181818" },
    { name := "color-bg-translucent", value := "rgba(24, 24, 24, 0.85)" },
    { name := "color-white", value := "#1e1e1e" },
    { name := "color-border", value := "#333" },
    { name := "color-border-nav", value := "#333" },
    { name := "color-border-light", value := "#444" },
    { name := "color-hover", value := "rgba(255, 255, 255, 0.08)" },
    { name := "color-link-hover", value := "#4d9efc" },
    { name := "color-shadow", value := "rgba(0, 0, 0, 0.5)" },

    -- Component overrides
    { name := "btn-bg", value := "var(--color-primary)" },
    { name := "btn-text", value := "var(--color-white)" },
    { name := "card-bg", value := "#1f1f1f" },
    { name := "card-border", value := "#2a2a2a" },
    { name := "testimonial-bg", value := "#2e3a59" },
    { name := "testimonial-text", value := "#fff" }
  ]
}

/--
Lean-specific page type detection functions.
-/

def isMarkdownPage : Path → Bool
  | #[] | #["fro"] | #["404"] => false
  | _ => true

def indexPage : Path → Bool
  | _ => false

def needsTitle : Path → Bool
  | #["learn"] | #["install"] | #["404"] => false
  | _ => true

def isInstallPage (path : Path) : Bool :=
  path[0]?.isEqSome "install"

def isUseCases : Path → Bool
  | #["use-cases"] => true
  | _ => false

def isRoadmap : Path → Bool
  | #["fro", "roadmap"] => true
  | _ => false

def isPagePost : Path → Bool
  | #["use-cases", _] | #["fro", "roadmap", _] => true
  | _ => false


/--
Lean-specific post configuration.
-/
def postConfig : PostConfig :=
  { hasSpecialStyling := fun path => if isFro path then some "fro" else none }

/--
Lean website layout configuration.
-/
def layoutConfig : LayoutConfig :=
  { isMarkdownPage := isMarkdownPage,
    isIndexPage := indexPage,
    needsTitle := needsTitle,
    isPagePost := isPagePost,
    postConfig := postConfig,
    hasSpecialStyling := fun path => if isFro path then some "fro" else none,
    renderPostList := fun path html =>
      if isUseCases path then
        {{ <div class="use-cases-grid"> {{ html }} </div> }}
      else
        html
  }

def theme : Theme :=
  Verso.Web.theme
    { siteName := "Lean Lang", rootTitle := "Lean enables correct, maintainable, and formally verified code", socialMeta, headConfig, variables := colorTheme }
    layoutConfig
    buildFroNavBarConfig
    {{
      <script async src="https://plausible.io/js/pa-RTua_4FfKHhfAvAc3liZd.js"></script>
      <script>
        "window.plausible=window.plausible||function(){(plausible.q=plausible.q||[]).push(arguments)},plausible.init=plausible.init||function(i){plausible.o=i||{}};
        plausible.init()"
      </script>
    }}
    (pure footer)
