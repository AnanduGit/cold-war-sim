# ❄️ Cold War

A real-time 3D ICBM defense simulation running on an interactive globe. Antarctic penguin forces launch ballistic missiles in waves at Arctic bear air defense sites. Bears must intercept them all to survive.

Built entirely in a single React + Three.js file. No backend. No build step. Runs in any modern browser.

---

## Simulation

- 🐧 **Penguins** launch ICBMs in 10 escalating waves from 5 Antarctic sites
- 🐻‍❄️ **Bears** operate radar-guided interceptor systems at 5 Arctic bases
- Penguins win if all bear bases are destroyed before wave 10 ends
- Bears win if they survive all 10 waves

Real-world intercept rates hover around 30% — roughly matching actual strategic defense exchange ratios.

---

## Physics & AI

**Missiles**
- Ballistic arc trajectory via `sin(progress × π)` — rises steeply, peaks at midpoint, curves down to surface
- Evasion fuel budget — each missile gets 3 maneuvers maximum, then flies straight and predictable
- Noisy CEP targeting — guidance drift modeled at launch, no perfect strikes
- Threat-aware evasion — only evades when inside radar range

**Interceptors**
- Staleness-aware lead pursuit — prediction confidence degrades as radar track ages
- Smart distribution — targets the least-covered missile in range, not just the closest
- Maximum 2 interceptors per missile globally, 4 per site
- 550-frame fuel limit — runs out of fuel, falls back to surface under gravity
- Radar updates every 90 frames with positional noise

**Radar**
- 115-unit detection range per bear site
- 700ms launch delay after detection (reaction time)
- Sonar-pulse ring animation on each base
- Sites repair HP every 3 successful intercepts

---

## Controls (Mobile)

| Gesture | Action |
|---|---|
| 1 finger drag | Rotate globe |
| 2 finger pinch | Zoom in/out |
| 2 finger drag | Pan |
| 2 finger twist | Roll |

Mouse: left drag to rotate, scroll to zoom.

---

## Tech

- **React** — UI, state, shell/app architecture
- **Three.js r128** — 3D globe, missile/interceptor meshes, trails, explosions
- **TopoJSON / world-atlas** — 50m resolution country borders and coastlines
- Single file, no build tooling required
- Persistent battle history via storage API

---

## How to Run

Open in [Claude.ai](https://claude.ai) as an artifact, or drop the JSX into a React sandbox like [StackBlitz](https://stackblitz.com).

---

## Background

Built iteratively over 46 versions in a Claude.ai conversation — physics debugging, AI tuning, gesture controls, and balance all developed through natural language and code review. No IDE, no debugger, just an Android phone and a chat window.

Made with ❤️ by Claude
