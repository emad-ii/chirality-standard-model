# Why Chirality?

The classification begins from a measured fact about nature and turns it into an inverse mathematical question.

## From parity to a chiral weak interaction

Parity reverses the three spatial coordinates. If parity were an exact symmetry, an experiment and its mirror image would obey the same laws.

In 1956, Tsung-Dao Lee and Chen-Ning Yang reviewed the evidence and found that parity conservation had not been established in weak interactions. They proposed direct tests. Chien-Shiung Wu, Ernest Ambler, Raymond Hayward, Dale Hoppes, and Ralph Hudson carried out one of them using oriented cobalt-60 nuclei. The angular distribution of the emitted electrons was not mirror-symmetric. Their 1957 result established parity violation in beta decay.

The two-component and $V-A$ descriptions of weak interactions then made the handed structure explicit. The electroweak Standard Model encodes it in the representations of its fermion fields: left-chiral quarks and leptons transform as $SU(2)_L$ doublets, while the corresponding right-chiral charged fields transform as singlets.

This history has three distinct mathematical layers:

| Layer | Meaning |
| --- | --- |
| **Parity** | The spatial reflection $(t,\mathbf x)\mapsto(t,-\mathbf x)$ |
| **Lorentz chirality** | The two inequivalent Weyl representations $(\tfrac12,0)$ and $(0,\tfrac12)$ |
| **Gauge chirality** | Left- and right-chiral fields carry different internal gauge representations |

Wu and collaborators established parity violation experimentally. Modern electroweak theory expresses the observed handedness through Lorentz and gauge chirality.

## Chirality organises interactions and mass

For a charged Standard Model fermion, the left- and right-chiral fields have different electroweak quantum numbers. A direct Dirac mass term cannot be an electroweak singlet. The Higgs doublet supplies the missing quantum numbers through a gauge-invariant Yukawa interaction. For the electron,

$$
\mathcal L_Y=-y_e\,\overline L\,\Phi\,e_R+\text{h.c.}
$$

Expanding the neutral Higgs component around its vacuum value,

$$
\Phi^0=\frac{v+h}{\sqrt2},
$$

turns the same invariant coupling into both a mass and an interaction with the physical Higgs field:

$$
\mathcal L_Y
=-\frac{y_ev}{\sqrt2}\,\overline e e
-\frac{y_e}{\sqrt2}\,h\overline e e,
\qquad
m_e=\frac{y_ev}{\sqrt2}.
$$

The logical order is therefore

$$
\text{chiral representations}
\longrightarrow
\text{invariant couplings}
\longrightarrow
\text{vacuum}
\longrightarrow
\text{mass terms}.
$$

The same representation data also determine the cubic gauge-anomaly tensor. A consistent chiral gauge sector must be anomaly-free.

## Neutrinos expose a separate structural choice

The minimal renormalisable Standard Model contains no right-handed neutrino and gives neutrinos zero mass. Massive neutrinos can be incorporated by adding right-handed singlets and Dirac Yukawa couplings, by introducing lepton-number-violating Majorana structure, or through a higher-dimensional effective operator. These possibilities correspond to different extensions of the field and symmetry data.

The example is useful because it separates two questions cleanly:

1. Which chiral matter representations are present?
2. Which invariant operators and vacuum data generate their masses?

The classification in this repository begins with the first question.

## The conventional construction and the inverse question

A conventional chiral gauge model is assembled in a forward order:

1. choose a gauge algebra;
2. choose complex matter representations;
3. choose their multiplicities;
4. test gauge-anomaly cancellation;
5. add invariant couplings and symmetry-breaking data.

The paper turns the first four steps into a classification problem. It considers connected, infinitesimally effective compact homogeneous pairs $(G,H)$ whose isotropy module is irreducible and of complex type. Writing

$$
q_{\mathbb C}=V\oplus V^{\ast},
$$

it asks when the cubic trace tensor of $V$ has a nonzero ideal-valued radical. The hypotheses contain no preferred exceptional group, representation dimension, subgroup chain, or family multiplicity.

Up to duality, the unique survivor is

$$
\mathfrak e_8\supset\mathfrak e_6\oplus\mathfrak{su}(3)_M,
\qquad
V=\mathbf{27}\boxtimes\mathbf3,
\qquad
\mathrm{Rad}(c_V)=\mathfrak e_6.
$$

The familiar branching tables now appear at the end of the argument. Their role is to identify the content of the uniquely selected module, rather than to supply the initial choice.

## Primary sources and standard reviews

- T. D. Lee and C. N. Yang, [“Question of Parity Conservation in Weak Interactions”](https://doi.org/10.1103/PhysRev.104.254), *Physical Review* **104** (1956), 254–258.
- C. S. Wu, E. Ambler, R. W. Hayward, D. D. Hoppes, and R. P. Hudson, [“Experimental Test of Parity Conservation in Beta Decay”](https://doi.org/10.1103/PhysRev.105.1413), *Physical Review* **105** (1957), 1413–1415.
- R. P. Feynman and M. Gell-Mann, [“Theory of the Fermi Interaction”](https://doi.org/10.1103/PhysRev.109.193), *Physical Review* **109** (1958), 193–198.
- M. Goldhaber, A. W. Grodzins, and A. W. Sunyar, [“Helicity of Neutrinos”](https://doi.org/10.1103/PhysRev.109.1015), *Physical Review* **109** (1958), 1015–1017.
- S. Weinberg, [“Baryon- and Lepton-Nonconserving Processes”](https://doi.org/10.1103/PhysRevLett.43.1566), *Physical Review Letters* **43** (1979), 1566–1570.
- Particle Data Group, [“Electroweak Model and Constraints on New Physics”](https://pdg.lbl.gov/2023/reviews/rpp2023-rev-standard-model.pdf), *Review of Particle Physics*.
- Particle Data Group, [“Neutrino Masses, Mixing, and Oscillations”](https://pdg.lbl.gov/2023/reviews/rpp2022-rev-neutrino-mixing.pdf), *Review of Particle Physics*.
