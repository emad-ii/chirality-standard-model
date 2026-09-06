'use client';
import { useRef, useState } from 'react';
import { Slider } from '@/components/ui/slider';
import { ToggleGroup, ToggleGroupItem } from '@/components/ui/toggle-group';
import { multiplets } from '@/lib/particle-physics';
import {
  AmbientExhibit,
  DemoControl,
  useGentleDemo,
} from '@/components/exhibit-motion';
import {
  initialVector,
  orderedRotation,
  rotationSeparation,
  phaseVector,
  weakDoublet,
  nextDemoAngle,
  type Vector3,
} from '@/lib/symmetry-lab';

const axes: Vector3[] = [
  [1, 0, 0],
  [0, 1, 0],
  [0, 0, 1],
];
const colours = ['#8bbcff', '#f1a17d', '#91c9b5'];
const project = ([x, y, z]: Vector3) => [
  150 + 80 * (x - 0.65 * y),
  145 + 80 * (0.3 * x + 0.45 * y - z),
];
const format = (n: number) => (Math.abs(n) < 0.0001 ? '0.00' : n.toFixed(2));

function RotationFrame({
  angle,
  order,
}: {
  angle: number;
  order: 'xz' | 'zx';
}) {
  const v = orderedRotation(initialVector, angle, order);
  const [px, py] = project(v);
  return (
    <div className="rotation-frame">
      <span className="eyebrow">
        {order === 'xz' ? 'X, THEN Z' : 'Z, THEN X'}
      </span>
      <svg
        viewBox="0 0 300 290"
        aria-label={`${order === 'xz' ? 'X then Z' : 'Z then X'} rotation of a unit vector: (${v.map(format).join(', ')})`}
      >
        <title>
          Projection of a three-dimensional vector and its rotated coordinate
          frame.
        </title>
        {axes.map((axis, i) => {
          const [x, y] = project(axis);
          const [a, b] = project(orderedRotation(axis, angle, order));
          return (
            <g key={i}>
              <path
                d={`M150 145 L${x} ${y}`}
                stroke="#46586b"
                strokeDasharray="3 5"
              />
              <path
                d={`M150 145 L${a} ${b}`}
                stroke={colours[i]}
                opacity=".65"
                strokeWidth="2"
              />
              <text x={x + 7} y={y + 4} fill="#a2b9d3" fontSize="16">
                {'xyz'[i]}
              </text>
            </g>
          );
        })}
        <circle cx="150" cy="145" r="3" fill="#e4edf8" />
        <path d={`M150 145 L${px} ${py}`} stroke="#e7c795" strokeWidth="3" />
        <circle cx={px} cy={py} r="7" fill="#e7c795" />
        <circle cx={px} cy={py} r="16" fill="#e7c795" opacity=".12" />
      </svg>
      <output aria-live="off">({v.map(format).join(', ')})</output>
    </div>
  );
}

function RotationLab({ depth }: { depth: string }) {
  const [angle, setAngle] = useState(45);
  const host = useRef<HTMLDivElement>(null);
  const demo = useGentleDemo(
    host,
    () => setAngle((n) => nextDemoAngle(n, 15, 90)),
    10000,
  );
  return (
    <div
      className="foundation-lab"
      id="lie-algebra"
      ref={host}
      {...demo.handlers}
    >
      <DemoControl {...demo} />
      <div className="foundation-intro">
        <span className="eyebrow">01 / A GROUP AND ITS ALGEBRA</span>
        <h3>
          Two turns.
          <br />
          Does the order matter?
        </h3>
        <p>
          Start with the same gold arrow. Turn it about the x-axis, then the
          z-axis. Now reverse the order. At most angles, the arrow ends
          somewhere else.
        </p>
        <p>
          All rotations of three-dimensional space about the origin form the{' '}
          <strong>Lie group SO(3)</strong>. You can combine rotations, undo
          them, and vary the angle continuously. Its{' '}
          <strong>Lie algebra</strong> describes the infinitesimal turns: the
          basic directions of change from which finite rotations can be built.
        </p>
        <p>
          Each basic direction is a <strong>generator</strong>. The{' '}
          <strong>Lie bracket</strong> records how two such changes fail to
          commute. Here, doing the turns in a different order gives a different
          result. That rule is part of the algebra’s structure.
        </p>
      </div>
      <AmbientExhibit className="foundation-instrument">
        <div className="rotation-pair">
          <RotationFrame angle={angle} order="xz" />
          <RotationFrame angle={angle} order="zx" />
        </div>
        <label id="rotation-angle-label" className="foundation-slider-label">
          Angle of each turn <output aria-live="off">{angle}°</output>
        </label>
        <Slider
          min={0}
          max={90}
          step={1}
          value={[angle]}
          onValueChange={(v) => setAngle(Array.isArray(v) ? v[0] : v)}
          aria-labelledby="rotation-angle-label"
        />
        <p className="instrument-answer">
          {angle === 0
            ? 'No turn: both arrows coincide.'
            : `Endpoint separation: ${rotationSeparation(angle).toFixed(3)} unit lengths.`}{' '}
          <span>Try 0°, then 90°.</span>
        </p>
      </AmbientExhibit>
      <details
        className="inline-depth foundation-detail"
        open={depth === 'math' ? true : undefined}
      >
        <summary>
          From the picture to the bracket <span>+</span>
        </summary>
        <p>
          For matrix generators X and Z, the Lie bracket is [Z,X] = ZX − XZ.
          Expanding the two orders gives e<sup>tZ</sup>e<sup>tX</sup> − e
          <sup>tX</sup>e<sup>tZ</sup> = t²[Z,X] + O(t³). The first-order turns
          agree; their second-order difference remembers the order.
        </p>
        <p>
          The displayed rotations act on ordinary three-dimensional vectors. The
          paper uses internal symmetries acting on field components. The
          mathematical language is shared; internal dimensions are not
          additional spatial directions.
        </p>
      </details>
    </div>
  );
}

function RepresentationLab({ depth }: { depth: string }) {
  const [mode, setMode] = useState('phase');
  const [angle, setAngle] = useState(60);
  const host = useRef<HTMLDivElement>(null);
  const demo = useGentleDemo(
    host,
    () => setAngle((n) => nextDemoAngle(n, 30, mode === 'doublet' ? 720 : 360)),
    10000,
  );
  const doublet = weakDoublet(angle);
  return (
    <div
      className="foundation-lab"
      id="representations"
      ref={host}
      {...demo.handlers}
    >
      <DemoControl {...demo} />
      <div className="foundation-intro">
        <span className="eyebrow">02 / HOW A SYMMETRY ACTS</span>
        <h3>
          One transformation.
          <br />
          Different responses.
        </h3>
        <p>
          A symmetry alone does not tell us what matter exists. We also need its{' '}
          <strong>representation</strong>: the rule telling each field how to
          respond to that symmetry.
        </p>
        <p>
          {mode === 'phase'
            ? 'For the circle group U(1), charge fixes how fast a field’s complex phase turns. A charge-two field turns twice as far as a charge-one field under the same transformation. The arrows below are complex amplitudes, not spinning particles.'
            : 'For SU(2), the transformation acts on a pair of complex field components. One transformation can mix them while preserving the total squared amplitude. A doublet counts two components, not two spatial dimensions or two generations.'}
        </p>
      </div>
      <div className="foundation-instrument">
        <ToggleGroup
          value={[mode]}
          onValueChange={(v) => {
            if (v[0]) {
              setMode(v[0]);
              if (v[0] === 'phase') setAngle((a) => Math.min(a, 360));
            }
          }}
          className="lab-tabs"
          aria-label="Representation example"
        >
          <ToggleGroupItem value="phase">U(1): a phase</ToggleGroupItem>
          <ToggleGroupItem value="doublet">SU(2): a doublet</ToggleGroupItem>
        </ToggleGroup>
        <AmbientExhibit>
          {mode === 'phase' ? (
            <div className="phase-pair">
              {[1, 2].map((charge) => {
                const [re, im] = phaseVector(angle, charge);
                return (
                  <div key={charge}>
                    <span className="eyebrow">CHARGE {charge}</span>
                    <svg
                      viewBox="0 0 240 240"
                      aria-label={`Charge ${charge}: complex phase ${format(re)} + ${format(im)}i`}
                    >
                      <circle
                        cx="120"
                        cy="120"
                        r="80"
                        fill="none"
                        stroke="#40536c"
                      />
                      <path d="M20 120H220 M120 20V220" stroke="#26374b" />
                      <text x="201" y="140" fill="#a2b9d3" fontSize="14">
                        Re
                      </text>
                      <text x="130" y="28" fill="#a2b9d3" fontSize="14">
                        Im
                      </text>
                      <path
                        d={`M120 120 L${120 + re * 80} ${120 - im * 80}`}
                        stroke={colours[charge - 1]}
                        strokeWidth="2"
                      />
                      <circle
                        cx={120 + re * 80}
                        cy={120 - im * 80}
                        r="6"
                        fill={colours[charge - 1]}
                      />
                    </svg>
                    <output aria-live="off">
                      ψ → e<sup>{charge === 1 ? 'iθ' : '2iθ'}</sup>ψ
                    </output>
                  </div>
                );
              })}
            </div>
          ) : (
            <div className="doublet-display">
              <div className="doublet-amplitudes">
                {doublet.map((a, i) => (
                  <div key={i}>
                    <span>
                      {i === 0 ? 'Upper component' : 'Lower component'}
                    </span>
                    <strong>{format(a)}</strong>
                    <div className="amplitude-track">
                      <div style={{ width: `${100 * a * a}%` }} />
                    </div>
                    <small>Squared amplitude {(a * a).toFixed(2)}</small>
                  </div>
                ))}
              </div>
              <p>
                A weak doublet has two complex components that the symmetry can
                mix. This particular SU(2) transformation sends (1, 0) to
                (cos(θ/2), sin(θ/2)); the sum of squared amplitudes stays one.
              </p>
              <p className="instrument-answer">
                At 360°, the doublet changes sign. At 720°, it returns. Here we
                show internal weak isospin, not a particle’s spin in space.
                These are transformed field components, not probabilities for a
                physical neutrino-to-electron conversion.
              </p>
            </div>
          )}
        </AmbientExhibit>
        <label
          id="representation-angle-label"
          className="foundation-slider-label"
        >
          Transformation angle <output aria-live="off">{angle}°</output>
        </label>
        <Slider
          min={0}
          max={mode === 'doublet' ? 720 : 360}
          step={5}
          value={[angle]}
          onValueChange={(v) => setAngle(Array.isArray(v) ? v[0] : v)}
          aria-labelledby="representation-angle-label"
        />
      </div>
      <details
        className="inline-depth foundation-detail"
        open={depth === 'math' ? true : undefined}
      >
        <summary>
          Representation, irreducibility and complex type <span>+</span>
        </summary>
        <p>
          A smooth finite-dimensional group representation is a map ρ: G → GL(V)
          with ρ(g₁g₂) = ρ(g₁)ρ(g₂). Differentiating it gives a Lie-algebra
          representation, preserving brackets. Its dimension counts components
          in V, not copies of a family or dimensions of spacetime.
        </p>
        <p>
          An irreducible representation has no proper nonzero invariant subspace
          under the full group. A weak doublet is irreducible under SU(2),
          although a single chosen rotation can be diagonalised. The two U(1)
          examples above are separate one-dimensional representations.
        </p>
        <p>
          “Complex type” is stronger than having complex entries: the
          representation is inequivalent to its conjugate. The SU(2) doublet is
          pseudoreal, not complex type. The paper instead starts with a real
          irreducible adjoint complement q whose commuting endomorphisms form ℂ.
          Its complexification is V ⊕ V*, with V and V* inequivalent.
        </p>
      </details>
    </div>
  );
}

export function ChargeKey() {
  const [lower, setLower] = useState(false);
  const [quarks, setQuarks] = useState(false);
  const multiplet = multiplets.find((p) => p.id === (quarks ? 'Q' : 'L'))!;
  // Use the same integer-normalised hypercharges as the anomaly exhibit.
  const chargeSixths = (lower ? -3 : 3) + multiplet.q;
  const charges: Record<number, string> = {
    [-6]: '−1',
    0: '0',
    4: '+⅔',
    [-2]: '−⅓',
  };
  const components = quarks
    ? ['Up quark', 'Down quark']
    : ['Neutrino', 'Electron'];
  return (
    <div className="charge-key" id="charge-key">
      <div>
        <span className="eyebrow">WORK OUT THE CHARGES</span>
        <h3>Read the label: {multiplet.rep}</h3>
        <ToggleGroup
          className="lab-tabs"
          aria-label="Matter doublet"
          value={[quarks ? 'quarks' : 'leptons']}
          onValueChange={(values) => {
            if (values[0]) setQuarks(values[0] === 'quarks');
          }}
        >
          <ToggleGroupItem value="leptons">Lepton doublet</ToggleGroupItem>
          <ToggleGroupItem value="quarks">Quark doublet</ToggleGroupItem>
        </ToggleGroup>
        <p>
          {quarks
            ? 'For the left-chiral quark field, 3 means a colour triplet, 2 means a weak doublet, and ⅙ is its hypercharge Y. Each of the two weak components has three colour components, making six in total.'
            : 'For the left-chiral lepton field, 1 means a colour singlet, 2 means a weak doublet, and −½ is its hypercharge Y. A singlet is unchanged by that group’s transformations; a doublet has two components.'}
        </p>
        <p>
          The weak-isospin labels T₃ are +½ and −½; both components share Y. Add
          the two numbers to find electric charge Q, measured in units of the
          positive elementary charge. Choose a component below.
        </p>
      </div>
      <ToggleGroup
        className="lab-tabs"
        value={[lower ? 'lower' : 'upper']}
        onValueChange={(v) => {
          if (v[0]) setLower(v[0] === 'lower');
        }}
        aria-label="Weak-doublet component"
      >
        <ToggleGroupItem value="upper">{components[0]}</ToggleGroupItem>
        <ToggleGroupItem value="lower">{components[1]}</ToggleGroupItem>
      </ToggleGroup>
      <output
        className="charge-key-equation"
        aria-label="Calculated electric charge"
        aria-live="polite"
      >
        Q = T₃ + Y = {lower ? '−½' : '+½'} {quarks ? '+ ⅙' : '− ½'} ={' '}
        <strong>{charges[chargeSixths]}</strong>
      </output>
      <p className="lab-note">
        The right-chiral electron is (1, 1)<sub>−1</sub>. It is a weak singlet:
        T₃ = 0. Its electric charge is also −1, despite its different
        electroweak representation.
      </p>
    </div>
  );
}

export function SymmetryWorkbench({
  depth,
  returnToCharges = false,
}: {
  depth: string;
  returnToCharges?: boolean;
}) {
  return (
    <section className="section foundations" id="foundations">
      <div className="section-number">
        <span aria-hidden="true" />
        <span className="label-rule" />A LANGUAGE FOR MATTER
      </div>
      <div className="section-heading">
        <h2>
          From a small turn
          <br />
          to a particle’s <em>charges.</em>
        </h2>
        <p className="section-lead">
          Rotate an experiment and its orientation changes. If the physical laws
          stay the same, that transformation is a symmetry. Lie theory gives us
          a language for continuous symmetries. Representation theory tells us
          how they act on the things we want to describe.
        </p>
        <p className="foundation-field-definition">
          Particle physics uses this language for internal transformations too.
          These mix components of fields, rather than turning an object in
          space. The familiar rotation below gives us a way to learn the rules
          before applying them to particle charges.
        </p>
      </div>
      <RotationLab depth={depth} />
      <RepresentationLab depth={depth} />
      <div className="algebra-dictionary" id="algebra-dictionary">
        <div className="guide-opening">
          <span className="eyebrow">KEEP THREE IDEAS SEPARATE</span>
          <h3>The symmetry. Its action. The number of copies.</h3>
          <p>
            An algebra supplies the transformation rules. A representation
            realises those rules as matrices acting on components. We can then
            have several fields with the same transformation rules. These are
            three different choices, and three different counts.
          </p>
        </div>
        <div className="guide-table-wrap">
          <table className="guide-table">
            <caption>
              Generators and representation dimensions count different things.
            </caption>
            <thead>
              <tr>
                <th scope="col">Symmetry</th>
                <th scope="col">Generators</th>
                <th scope="col">A representation</th>
                <th scope="col">Components</th>
              </tr>
            </thead>
            <tbody>
              <tr>
                <th scope="row">SU(2)</th>
                <td>3</td>
                <td>Weak doublet</td>
                <td>2</td>
              </tr>
              <tr>
                <th scope="row">SU(3)</th>
                <td>8</td>
                <td>Colour triplet</td>
                <td>3</td>
              </tr>
              <tr>
                <th scope="row">E₆</th>
                <td>78</td>
                <td>The 27 used in the paper</td>
                <td>27</td>
              </tr>
            </tbody>
          </table>
        </div>
        <p className="guide-bridge">
          SU(2), for example, has three independent generators. On a doublet,
          each is represented by a 2 × 2 matrix. Three families of doublets
          would be three copies of that two-component representation.
        </p>
        <details
          className="inline-depth"
          open={depth === 'math' ? true : undefined}
        >
          <summary>
            What are the adjoint and the Killing–Cartan list? <span>+</span>
          </summary>
          <p>
            An algebra can act on itself: a generator X changes another element
            Z through the bracket [X,Z]. This is the adjoint representation,
            whose dimension equals the number of generators. The eight gluons
            carry the adjoint colour index; quarks carry a three-component
            colour index instead.
          </p>
          <p>
            The Killing–Cartan classification is complete for finite-dimensional
            complex simple Lie algebras, equivalently for compact real simple
            Lie algebras: Aₙ, Bₙ, Cₙ, Dₙ and G₂, F₄, E₆, E₇, E₈. “Simple” means
            non-abelian with no nonzero proper ideal, an algebraic part
            preserved by brackets with everything else.
          </p>
          <p>
            A semisimple Lie algebra is a finite direct sum of simple Lie
            algebras. The factors commute with one another. A simple algebra is
            the one-factor case; e₆ ⊕ su(3) is an example with two factors.
            Every finite-dimensional compact Lie algebra splits into a
            semisimple part and an abelian centre. The centre commutes with the
            entire algebra. This includes arbitrary finite ranks, sums and
            repetitions. The classification exhausts the algebras; specifying
            embeddings, representations and global group identifications is
            further mathematical work.
          </p>
          <p>
            The paper links these choices by putting a smaller algebra inside a
            larger one and letting the smaller algebra act on all the remaining
            directions. This remaining space is its adjoint complement. The
            classification asks when that space has the specified chiral and
            cubic-anomaly properties.
          </p>
        </details>
      </div>
      {returnToCharges && (
        <a className="primary-link" href="#charge-key">
          Return to particle charges →
        </a>
      )}
      <p className="source-note">
        For the formal definitions and classification:{' '}
        <a
          href="https://damtp.cam.ac.uk/user/ho/GNotes.pdf"
          target="_blank"
          rel="noreferrer"
        >
          Hugh Osborn’s Group Theory notes ↗
        </a>
        . For their role in particle physics:{' '}
        <a
          href="https://www.damtp.cam.ac.uk/user/tong/sm/standardmodel.pdf"
          target="_blank"
          rel="noreferrer"
        >
          David Tong’s Standard Model notes ↗
        </a>
        . The diagrams evaluate the rotations and amplitudes shown here
        directly.
      </p>
    </section>
  );
}
