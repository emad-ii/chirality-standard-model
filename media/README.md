# The films

Two complementary views of the argument, with the videos, captions and editable source kept beside the paper.

| Film | Watch | Source |
| :--- | :--- | :--- |
| **The equations, one at a time** | [Equation film](equations/equation-story.mp4) · [captions](equations/equation-story.vtt) | [Manim scene](equations/equation_story.py) |
| **One survivor** | [78-second selection pilot](pilot/outputs/one-survivor-pilot.mp4) · [captions](pilot/outputs/one-survivor-pilot.vtt) | [Hyperframes composition and tests](pilot/) |

Both are deliberately silent: the explanation is on screen and in the captions. The [website](https://emad-ii.github.io/chirality-standard-model/#equation-film) presents the equation film with chapter navigation and a transcript.

The selection pilot shows the final six full-rank candidates, their separate cubic coefficients and the surviving representation. Its source folder also holds a draft plan and narration for a longer film; those are production material, not a completed twelve-minute video.

## Render the equation film

Use Python with Manim Community 0.20.1, FFmpeg and LaTeX available. From the repository root:

```sh
manim -qh --fps 24 --renderer=cairo media/equations/equation_story.py EquationStory
```

See [the pilot’s instructions](pilot/README.md) for its single-worker render. The published site uses the checked-in MP4 files; it needs no rendering service or account.

Video materials created with GPT-6 Astra.
