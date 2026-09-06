# Interactive website

[**Explore the live site →**](https://emad-ii.github.io/chirality-standard-model/)

The paper’s interactive edition: a scroll-driven classification, historical illustrations, D3 exhibits, a Three.js root explorer, particle and anomaly demonstrations, and chaptered films. Four reading paths change the page’s order and depth. Glossary entries and folded chapters keep the background within reach.

The main argument begins with compact algebra inclusions and the entire adjoint complement. Complex type and a nonzero cubic radical are imposed together; homogeneity appears as the geometric realization.

## Develop

Use Node 22.13 or later. From this directory:

```sh
npm ci
npm run dev
```

The startup task copies the current papers, notebook, certificate and videos from their canonical locations in the parent repository. [Illustration credits](ASSET_NOTES.md) accompany the checked-in artwork.

## Check and publish

```sh
npm run sync:assets
npm run check
npm run build:pages
node scripts/check-pages.mjs
```

GitHub Pages serves the static export at `/chirality-standard-model/`. [The publishing workflow](../.github/workflows/pages.yml) performs these website checks and deploys that export. It does not rebuild LaTeX, render videos or run a server. Changes to the checked-in PDFs or MP4s are copied into the next site build.

The download manifest records SHA-256 hashes and is checked against the source files. The full ZIP link points to GitHub’s archive of the complete repository; there is no second, stale copy of the research bundle.

## Reading and motion

Curious readers start with Wu, physics readers with the particle constraints, mathematicians with the hypotheses, and reviewers with the evidence. The URL preserves the path; on static hosting, the browser restores its query string after hydration. Links into folded chapters open the necessary material.

Exhibits move gently only while visible. Interaction or keyboard focus pauses automatic selection changes. The page-wide pause control and reduced-motion preferences stop nonessential movement. Three.js rendering is capped at 30 frames per second and stops off-screen. A failed 3D download or graphics context leaves the flat diagram and coordinate inspector available. The existing dark presentation is preserved.

## What the checks cover

- Root coordinates, Coxeter projections, six representative cells under 720 reflected states, cubic coefficients and branching arithmetic.
- All 32 subsets of one matter family across five anomaly channels; Higgs-slider arithmetic; the particle gallery.
- Four reading routes, optional chapter coverage, deep-link mapping and motion policies.
- Rotation and representation identities over 1,441 angles.
- React component tests for route changes, focus, timers, reduced motion and graphics failures.
- Download identity, Pages asset paths, static HTML and linked media.

These are presentation and consistency tests. The manuscript proofs, exhaustive Python searches and finite Lean theorems remain in the [research verification layer](../verification/README.md). The six small checks exposed inside the website do not replace that layer.

The optional WebMCP interface exposes the same visible E₆ selection and local checks; the page works without it.

Website created with GPT-6 Astra.
