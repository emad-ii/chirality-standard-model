import { act, fireEvent, render, screen } from '@testing-library/react';
import { describe, expect, it, vi } from 'vitest';
import { ChargeKey } from '@/components/symmetry-workbench';
import {
  StandardModelGuide,
  MathematicsAndMeasurement,
} from '@/components/standard-model-guide';
import { MotionProvider } from '@/components/exhibit-motion';
import {
  chapterForAnchor,
  readerPaths,
  omittedChapters,
} from '@/lib/reader-paths';
import { multiplets } from '@/lib/particle-physics';
import { installMotionPreference } from './setup';

describe('physics explanations and their working examples', () => {
  it('calculates both lepton and quark doublets using the anomaly exhibit’s hypercharges', () => {
    render(<ChargeKey />);
    const result = () =>
      screen.getByLabelText('Calculated electric charge').textContent;
    expect(multiplets.find((p) => p.id === 'L')?.q).toBe(-3);
    expect(result()).toBe('Q = T₃ + Y = +½ − ½ = 0');
    fireEvent.click(screen.getByRole('button', { name: 'Electron' }));
    expect(result()).toBe('Q = T₃ + Y = −½ − ½ = −1');
    fireEvent.click(screen.getByRole('button', { name: 'Quark doublet' }));
    expect(multiplets.find((p) => p.id === 'Q')?.q).toBe(1);
    expect(result()).toBe('Q = T₃ + Y = −½ + ⅙ = −⅓');
    fireEvent.click(screen.getByRole('button', { name: 'Up quark' }));
    expect(result()).toBe('Q = T₃ + Y = +½ + ⅙ = +⅔');
    fireEvent.click(screen.getByRole('button', { name: 'Lepton doublet' }));
    expect(result()).toBe('Q = T₃ + Y = +½ − ½ = 0');
  });

  it('provides the gauge explanation without requiring motion or WebGL', () => {
    const view = render(<StandardModelGuide />);
    expect(screen.getByRole('heading', { name: 'Colour' })).toBeTruthy();
    expect(screen.getByRole('heading', { name: 'Weak isospin' })).toBeTruthy();
    expect(screen.getByRole('heading', { name: 'Hypercharge' })).toBeTruthy();
    expect(view.container.querySelector('canvas')).toBeNull();
    expect(view.container.textContent).toContain('three generations');
    expect(view.container.querySelector('details')?.textContent).toContain(
      'neighbouring points',
    );
  });

  it('keeps each calculation attached to its observation and primary source', () => {
    installMotionPreference(true);
    render(
      <MotionProvider>
        <MathematicsAndMeasurement />
      </MotionProvider>,
    );
    for (const [label, equation, source] of [
      [
        'W and Z',
        'mW = gv/2',
        'https://cern-courier.web.cern.ch/a/finding-the-w-and-z/',
      ],
      [
        'Quarks and gluons',
        'CF = (N² − 1)/(2N)',
        'https://pdg.lbl.gov/2025/reviews/rpp2025-rev-qcd.pdf',
      ],
      ['The Higgs', 'mf = yf v/√2', 'https://arxiv.org/abs/2207.00092'],
    ]) {
      fireEvent.click(screen.getByRole('button', { name: label }));
      expect(
        screen.getByRole('heading', { name: 'The observation' }),
      ).toBeTruthy();
      expect(
        screen.getByText(
          (_, element) =>
            element?.className === 'guide-equation' &&
            element.textContent!.includes(equation),
        ),
      ).toBeTruthy();
      expect(screen.getByRole('link').getAttribute('href')).toBe(source);
    }
  });

  it('advances gently, but stops when the reader chooses an example', async () => {
    vi.useFakeTimers();
    render(
      <MotionProvider>
        <MathematicsAndMeasurement />
      </MotionProvider>,
    );
    await act(async () => {
      await Promise.resolve();
    });
    await act(async () => {
      vi.advanceTimersByTime(48000);
    });
    expect(
      screen.getByRole('heading', {
        name: 'The algebra leaves a trace in particle collisions.',
      }),
    ).toBeTruthy();
    const higgs = screen.getByRole('button', {
      name: 'The Higgs',
    });
    fireEvent.pointerDown(higgs);
    fireEvent.click(higgs);
    await act(async () => {
      vi.advanceTimersByTime(72000);
    });
    expect(
      screen.getByRole('heading', {
        name: 'Finding the particle begins the next test.',
      }),
    ).toBeTruthy();
  });

  it('does not auto-advance under reduced motion', async () => {
    vi.useFakeTimers();
    installMotionPreference(true);
    render(
      <MotionProvider>
        <MathematicsAndMeasurement />
      </MotionProvider>,
    );
    await act(async () => {
      vi.advanceTimersByTime(72000);
    });
    expect(
      screen.getByRole('heading', {
        name: 'A theory tells an experiment what to look for.',
      }),
    ).toBeTruthy();
  });

  it('makes the new sections reachable from all four reading paths', () => {
    for (const [anchor, chapter] of [
      ['standard-model', 'physics'],
      ['math-and-measurement', 'physics'],
      ['algebra-dictionary', 'foundations'],
    ] as const) {
      expect(chapterForAnchor(anchor)).toBe(chapter);
      for (const path of readerPaths) {
        expect(
          [...path.chapters, ...omittedChapters(path.id)].filter(
            (id) => id === chapter,
          ),
        ).toHaveLength(1);
      }
    }
  });
});
