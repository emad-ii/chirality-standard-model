# From Chirality to the Standard Model — film production

An original visual explanation of the paper, with a twelve-minute narrative plan and a finished 78-second Hyperframes pilot of the final equal-rank selection. The plan and narration are drafts for a longer film; the pilot is the rendered video.

## Start here

- `PRODUCTION-PLAN.md`: timed storyboard, visual language, tools, sources, review gates and delivery specification.
- `NARRATION.md`: complete first narration draft, approximately 1,450 words before the recording and timing pass.
- `outputs/one-survivor-pilot.mp4`: rendered silent visual pilot, once the render completes.
- `outputs/one-survivor-pilot.vtt`: pilot captions.
- `outputs/source-manifest.json`: source hashes generated when rendering locally.

The pilot shows the final six equal-rank candidates, their separate cubic coefficients, the E₆ radical, a projection of the 240 E₈ roots, and three complete 27-dimensional blocks. It retains the vectorlike components and singlets while explaining the net chiral class. The historical, introductory and second-classification chapters are planned and scripted, not yet animated.

## Run it

Node 22 or later, FFmpeg and the Chrome renderer used by Hyperframes are required. The first render may download that browser. No HeyGen account or paid service is needed for this local, silent pilot.

```sh
npm ci
npm test
npm run lint:film
npm run preview
```

Render with a single worker:

```sh
npm run render:pilot
node scripts/export-support.mjs
node scripts/check-export.mjs
```

The single-worker setting is deliberate. Render chapters serially during production; do not saturate the laptop for draft iterations. The locked dependencies and playhead-driven animations improve reproducibility. Native renders can still differ across machines because of browser and font versions; no cross-machine bit-identical guarantee is claimed.

## Editable source

`index.html` holds the composition. `film.css` controls its typography and layout. `film.mjs` owns its finite, seekable timeline. `data.mjs` contains the sourced coefficients, actual root construction and caption timings. No image model draws equations or generates mathematical data.

The tests check cubic-index arithmetic, root lengths/counts, orthonormal projection, complete representation dimension counts, caption coverage and absence of an autonomous animation clock. The coefficients are also compared with the website in this same repository. They validate this visualisation, not the classification theorem.

## Review status

Independent agent reviews of the physics and teaching sequence informed the plan. Visual samples have been rendered and inspected. These are editorial checks, not a substitute for nonexpert learner testing or an independent proof audit.

Remaining main-film production: recorded narration and timing pass; whole-film animatic; detailed historical and geometric scenes; certificate-based E₆ intersection sequence; sound design; learner review; final captions and 4K master. Do not publish the pilot as the completed explanatory film.

## Voice and sound

The narrator has not been selected. The project does not use a cloned voice, a presenter avatar, another creator's recordings, copyrighted music or paid cloud rendering. The user's requested Richard Behiel reference sets an ambition for clarity and depth, not an attribution or a style/voice impersonation.

Pronunciation notes for recording: “Lie” sounds like “Lee”; SU(3) is “ess you three”; E₆ is “ee six”; q is “cue”; `27 ⊠ 3` is “twenty-seven tensor three”; `χ` here is “chi”, the net chiral class. Read “the restriction to E₆” rather than narrating a symbolic arrow as a physical process.
