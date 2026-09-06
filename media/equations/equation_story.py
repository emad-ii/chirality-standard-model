"""The paper's algebraic argument, rendered with Manim Community.

Render with: manim -qh --fps 24 --renderer=cairo
media/equations/equation_story.py EquationStory
The published MP4 has 1,969 frames at 24 fps. Captions and the website
chapter links use that frame timeline. No narration is assumed.
"""
import os
from pathlib import Path

# Apply these before importing Manim / NumPy. The encoder is capped separately.
for _key in (
    "OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS", "BLIS_NUM_THREADS",
):
    os.environ[_key] = "2"

from manim import (
    Scene, Text, MathTex, VGroup, RoundedRectangle, Line, Dot,
    FadeIn, FadeOut, Write, LaggedStart,
    DOWN, UP, LEFT, RIGHT, config,
)
from manim.renderer.cairo_renderer import CairoRenderer
from manim.scene.scene_file_writer import SceneFileWriter

config.background_color = "#080b10"
config.media_dir = str(Path(__file__).resolve().parent / "media")
BLUE = "#8bbcff"
IVORY = "#ede9df"
COPPER = "#eeaa82"
GREEN = "#9acbb9"
MUTED = "#9bafc6"


class LimitedThreadWriter(SceneFileWriter):
    """Cap PyAV/libx264 workers before any frame enters the encoder."""

    def open_partial_movie_stream(self, file_path=None):
        super().open_partial_movie_stream(file_path)
        self.video_stream.codec_context.thread_count = 2
        self.video_stream.codec_context.options = {
            **self.video_stream.codec_context.options,
            "threads": "2",
            "x264-params": "threads=2:lookahead-threads=1",
        }


class EquationStory(Scene):
    def __init__(self, **kwargs):
        if kwargs.get("renderer") is None:
            kwargs["renderer"] = CairoRenderer(file_writer_class=LimitedThreadWriter)
        super().__init__(**kwargs)

    def construct(self):
        def words(text, size=23, color=IVORY):
            obj = Text(text, font="Helvetica Neue", font_size=size, color=color)
            if obj.width > 12:
                obj.scale_to_fit_width(12)
            return obj

        def page(number, heading, explanation):
            self.clear()
            self.chapter_number = number
            self.chapter_heading = heading
            tag = words("FROM CHIRALITY TO THE STANDARD MODEL", 12, MUTED).to_corner(UP + LEFT, buff=.42)
            title = words(heading, 34).move_to(UP * 2.65)
            label = words(f"{number:02d} / 06", 14, BLUE).to_corner(UP + RIGHT, buff=.42)
            rule = Line(LEFT * 6.4, RIGHT * 6.4, color="#2c3e54", stroke_width=1).shift(UP * 2.1)
            caption = words(explanation, 22, MUTED).move_to(DOWN * 2.4)
            dots = VGroup(*[Dot(radius=.035, color=BLUE if i < number else "#324458") for i in range(6)])
            dots.arrange(RIGHT, buff=.18).to_edge(DOWN, buff=.3)
            self.add(tag, label, rule, dots)
            self.play(FadeIn(title, shift=UP * .12), FadeIn(caption), run_time=.8)
            return title, caption

        page(1, "Start with a compact Lie-algebra inclusion.",
             "Start with an effective, proper inclusion of compact real Lie algebras.\nNo physical homogeneous-space hypothesis is assumed.")
        eq = MathTex(r"\mathfrak h\subsetneq\mathfrak g,\qquad\mathfrak q=\mathfrak g/\mathfrak h",
                     font_size=60, color=IVORY).shift(UP * .55)
        self.play(Write(eq), run_time=1.8)
        definitions = VGroup(
            words("g : a compact real Lie algebra", 20, BLUE),
            words("h : a proper subalgebra containing no nonzero ideal of g", 20, COPPER),
            words("q : the entire adjoint complement", 20, GREEN),
        ).arrange(DOWN, buff=.2).shift(DOWN * .8)
        self.play(LaggedStart(*[FadeIn(d, shift=RIGHT * .15) for d in definitions], lag_ratio=.2), run_time=1.2)
        self.wait(7.2)

        page(2, "First input: a complex-type complement.",
             "The real module q is irreducible of complex type.\nIts complexification gives two inequivalent irreducible modules.")
        condition = MathTex(r"\operatorname{End}_{\mathfrak h}(\mathfrak q)\cong\mathbb C",
                            font_size=48, color=IVORY).shift(UP * .9)
        halves = MathTex(r"\mathfrak q_{\mathbb C}=", r"V", r"\oplus", r"V^*",
                        font_size=70, color=IVORY).shift(DOWN * .15)
        halves[1].set_color(BLUE)
        halves[3].set_color(COPPER)
        inequivalent = MathTex(r"V\not\cong V^*", font_size=36, color=MUTED).shift(DOWN * 1.25)
        self.play(Write(condition), run_time=1.5)
        self.play(Write(halves), run_time=1.5)
        self.play(FadeIn(inequivalent), run_time=.8)
        self.wait(7.2)

        page(3, "Other input: a nonzero cubic radical.",
             "Alongside complex type, require a nonzero cubic radical.\nOne radical input kills the cubic for every h, h pair, including mixed inputs.")
        trace = MathTex(r"c_V(X,Y,Z)=\tfrac12\operatorname{Tr}_V(T_X\{T_Y,T_Z\})",
                        font_size=39, color=IVORY).shift(UP * 1)
        radical = MathTex(r"\mathfrak k=\operatorname{Rad}(c_V)", font_size=48, color=BLUE).shift(DOWN * .05)
        condition = MathTex(r"c_V(\mathfrak k,\mathfrak h,\mathfrak h)=0",
                            r"\qquad \mathfrak k\ne0", font_size=45, color=GREEN).shift(DOWN * 1.2)
        self.play(Write(trace), run_time=1.6)
        self.play(FadeIn(radical), run_time=.8)
        self.play(Write(condition), run_time=1.4)
        self.wait(8.4)

        page(4, "Both inputs reduce the problem to six candidates.",
             "The long paper's all-rank reduction leaves these six candidates.\nFive radicals vanish; only E8 containing E6 + A2 survives.")
        reduction = MathTex(
            r"\text{Both inputs}\Longrightarrow\mathfrak g\ \text{simple},\quad"
            r"\mathfrak h\ \text{semisimple and maximal}",
            font_size=28, color=BLUE,
        ).shift(UP * 1.65)
        pairs = [
            r"G_2\supset A_2", r"F_4\supset A_2+A_2", r"E_6\supset A_2^3",
            r"E_7\supset A_5+A_2", r"E_8\supset A_8", r"E_8\supset E_6+A_2",
        ]
        cards = VGroup()
        for i, pair in enumerate(pairs):
            box = RoundedRectangle(width=3.85, height=1.05, corner_radius=.08,
                                   stroke_color="#435a72", stroke_width=1, fill_color="#142033", fill_opacity=1)
            label = MathTex(pair, font_size=27, color=IVORY).move_to(box)
            cards.add(VGroup(box, label))
        cards.arrange_in_grid(rows=2, cols=3, buff=(.3, .35)).move_to(UP * .05)
        self.play(FadeIn(reduction), LaggedStart(*[FadeIn(c) for c in cards], lag_ratio=.12), run_time=1.8)
        self.wait(3)
        self.play(*[c.animate.set_opacity(.15) for c in cards[:5]],
                  cards[5][0].animate.set_stroke(GREEN, width=2), run_time=1.5)
        result = MathTex(r"\operatorname{Rad}(c_V)=\mathfrak e_6",
                         font_size=43, color=GREEN).shift(DOWN * 1.7)
        self.play(Write(result), run_time=1.1)
        self.wait(5.8)

        page(5, "The representation already carries a factor of three.",
             "Under Spin(10), each 27 splits into a 16, a 10 and a singlet.\nUnder SU(5), its net chiral content is one familiar family.")
        representation = MathTex(r"V=\mathbf{27}\otimes\mathbf3", font_size=58, color=BLUE).shift(UP * 1.12)
        branch = MathTex(r"\mathbf{27}=\mathbf{16}\oplus\mathbf{10}\oplus\mathbf1",
                         font_size=44, color=IVORY).shift(UP * .1)
        su5 = MathTex(r"\mathbf{27}=",
                     r"(\mathbf{10}\oplus\overline{\mathbf5})",
                     r"\oplus(\mathbf5\oplus\overline{\mathbf5})",
                     r"\oplus2\,\mathbf1", font_size=33).shift(DOWN * 1.0)
        su5[1].set_color(BLUE)
        su5[2].set_color(COPPER)
        su5[3].set_color(MUTED)
        self.play(Write(representation), run_time=1.3)
        self.play(Write(branch), run_time=1.5)
        self.play(Write(su5), run_time=1.7)
        self.wait(8.5)

        page(6, "Count the mathematical net chiral class.",
             "After Standard Model restriction, conjugate pairs and singlets have zero class.\nThe result is a mathematical class of three net families.")
        eq = MathTex(r"\chi(V)=3\,\chi(F_{\mathrm{SM}})", font_size=65, color=IVORY).shift(UP * .85)
        self.play(Write(eq), run_time=1.8)
        families = VGroup()
        for i in range(3):
            frame = RoundedRectangle(width=2.8, height=1.2, corner_radius=.07,
                                     stroke_color=BLUE, fill_color="#142f4c", fill_opacity=.8)
            label = MathTex(r"\chi(F_{\mathrm{SM}})", font_size=32, color=BLUE).move_to(frame)
            families.add(VGroup(frame, label))
        families.arrange(RIGHT, buff=.4).shift(DOWN * .6)
        self.play(LaggedStart(*[FadeIn(f, shift=UP * .2) for f in families], lag_ratio=.3), run_time=1.5)
        self.wait(8.5)
        self.play(FadeOut(families), run_time=.8)
        dual = MathTex(r"\chi(V^*)=-3\,\chi(F_{\mathrm{SM}})", font_size=39, color=COPPER).shift(DOWN * .65)
        self.play(Write(dual), run_time=1.1)
        self.wait(3.5)
