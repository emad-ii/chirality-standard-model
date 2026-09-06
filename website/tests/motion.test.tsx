import { useRef, useState } from 'react';
import { act, fireEvent, render, screen } from '@testing-library/react';
import { describe, expect, it, vi } from 'vitest';
import {
  DemoControl,
  MotionControl,
  MotionProvider,
  useGentleDemo,
  useMotion,
  useSceneClock,
} from '@/components/exhibit-motion';
import { installMotionPreference, intersections } from './setup';

function Probe() {
  const { enabled } = useMotion();
  return (
    <output aria-label="Effective motion">
      {enabled ? 'running' : 'paused'}
    </output>
  );
}
function Demo() {
  const ref = useRef<HTMLDivElement>(null);
  const [value, setValue] = useState(0);
  const demo = useGentleDemo(ref, () => setValue((v) => v + 1), 1000);
  return (
    <div ref={ref} {...demo.handlers}>
      <DemoControl {...demo} />
      <button onClick={() => setValue(40)}>Choose value</button>
      <output aria-label="Demo value">{value}</output>
    </div>
  );
}
const settle = async () => {
  await act(async () => {
    await Promise.resolve();
  });
};
const tick = async (ms: number) => {
  await act(async () => {
    vi.advanceTimersByTime(ms);
  });
};

describe('actual motion components', () => {
  it('honours initial reduced motion and changes to the preference', async () => {
    const { media, listeners } = installMotionPreference(true);
    const view = render(
      <MotionProvider>
        <MotionControl />
        <Probe />
      </MotionProvider>,
    );
    await settle();
    expect(screen.getByLabelText('Effective motion').textContent).toBe(
      'paused',
    );
    expect((screen.getByRole('button') as HTMLButtonElement).disabled).toBe(
      true,
    );
    act(() => media.change(false));
    expect(screen.getByLabelText('Effective motion').textContent).toBe(
      'running',
    );
    act(() => media.change(true));
    expect(screen.getByLabelText('Effective motion').textContent).toBe(
      'paused',
    );
    view.unmount();
    expect(listeners.size).toBe(0);
  });

  it('restores and persists the pause preference', async () => {
    localStorage.setItem('chirality-motion-v1', 'paused');
    render(
      <MotionProvider>
        <MotionControl />
        <Probe />
      </MotionProvider>,
    );
    await settle();
    expect(screen.getByLabelText('Effective motion').textContent).toBe(
      'paused',
    );
    fireEvent.click(
      screen.getByRole('button', { name: 'Resume gentle animations' }),
    );
    expect(localStorage.getItem('chirality-motion-v1')).toBe('playing');
    fireEvent.click(
      screen.getByRole('button', { name: 'Pause all gentle animations' }),
    );
    expect(localStorage.getItem('chirality-motion-v1')).toBe('paused');
  });

  it('works when optional preference storage throws', async () => {
    vi.spyOn(Storage.prototype, 'getItem').mockImplementation(() => {
      throw new Error('denied');
    });
    vi.spyOn(Storage.prototype, 'setItem').mockImplementation(() => {
      throw new Error('denied');
    });
    render(
      <MotionProvider>
        <MotionControl />
        <Probe />
      </MotionProvider>,
    );
    await settle();
    fireEvent.click(
      screen.getByRole('button', { name: 'Pause all gentle animations' }),
    );
    expect(screen.getByLabelText('Effective motion').textContent).toBe(
      'paused',
    );
  });

  it('does not leave demonstrations ticking offscreen, hidden, focused or unmounted', async () => {
    vi.useFakeTimers();
    const view = render(
      <MotionProvider>
        <Demo />
      </MotionProvider>,
    );
    await settle();
    await tick(1100);
    expect(screen.getByLabelText('Demo value').textContent).toBe('1');
    act(() => {
      intersections.forEach((observer) => observer.emit(false));
    });
    await tick(2000);
    expect(screen.getByLabelText('Demo value').textContent).toBe('1');
    act(() => {
      intersections.forEach((observer) => observer.emit(true));
    });
    vi.spyOn(document, 'hidden', 'get').mockReturnValue(true);
    fireEvent(document, new Event('visibilitychange'));
    await tick(2000);
    expect(screen.getByLabelText('Demo value').textContent).toBe('1');
    vi.spyOn(document, 'hidden', 'get').mockReturnValue(false);
    fireEvent(document, new Event('visibilitychange'));
    fireEvent.focus(screen.getByRole('button', { name: 'Choose value' }));
    await tick(2000);
    expect(screen.getByLabelText('Demo value').textContent).toBe('1');
    fireEvent.blur(screen.getByRole('button', { name: 'Choose value' }), {
      relatedTarget: document.body,
    });
    await tick(1100);
    expect(screen.getByLabelText('Demo value').textContent).toBe('2');
    view.unmount();
    expect(vi.getTimerCount()).toBe(0);
    expect(intersections.size).toBe(0);
  });

  it('manual keyboard selection stops the automatic demonstration', async () => {
    vi.useFakeTimers();
    render(
      <MotionProvider>
        <Demo />
      </MotionProvider>,
    );
    await settle();
    const button = screen.getByRole('button', { name: 'Choose value' });
    fireEvent.keyDown(button, { key: 'Enter' });
    fireEvent.click(button);
    fireEvent.blur(button, { relatedTarget: document.body });
    await tick(5000);
    expect(screen.getByLabelText('Demo value').textContent).toBe('40');
    expect(
      screen.getByRole('button', {
        name: 'Resume this automatic demonstration',
      }),
    ).toBeTruthy();
  });

  it('labels a reduced-motion demonstration by its actual disabled state', async () => {
    installMotionPreference(true);
    render(
      <MotionProvider>
        <Demo />
      </MotionProvider>,
    );
    await settle();
    const control = screen.getByRole('button', {
      name: 'Automatic demonstration disabled by your reduced-motion preference',
    });
    expect((control as HTMLButtonElement).disabled).toBe(true);
  });

  it('cancels the scene clock when motion is disabled and on unmount', async () => {
    vi.useFakeTimers();
    const { media } = installMotionPreference();
    const draw = vi.fn();
    function Scene() {
      const ref = useRef<HTMLDivElement>(null);
      useSceneClock(ref, draw);
      return <div ref={ref} />;
    }
    const view = render(
      <MotionProvider>
        <Scene />
      </MotionProvider>,
    );
    await settle();
    await tick(200);
    expect(draw).toHaveBeenCalled();
    act(() => media.change(true));
    const calls = draw.mock.calls.length;
    await tick(1000);
    expect(draw.mock.calls.length).toBe(calls);
    view.unmount();
    expect(vi.getTimerCount()).toBe(0);
  });
});
