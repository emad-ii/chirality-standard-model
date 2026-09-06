'use client';
import {
  createContext,
  useContext,
  useEffect,
  useRef,
  useState,
  type ReactNode,
  type RefObject,
} from 'react';
import { Pause, Play } from 'lucide-react';
import { Button } from '@/components/ui/button';
import { motionAllowed } from '@/lib/motion-policy';

const MotionContext = createContext({
  enabled: false,
  reduced: true,
  paused: false,
  toggle: () => {},
});
export function MotionProvider({ children }: { children: ReactNode }) {
  const [reduced, setReduced] = useState(true);
  const [paused, setPaused] = useState(false);
  const [foreground, setForeground] = useState(true);
  useEffect(() => {
    const preference = matchMedia('(prefers-reduced-motion: reduce)');
    const sync = () => {
      setReduced(preference.matches);
      setForeground(!document.hidden);
    };
    queueMicrotask(() => {
      sync();
      try {
        setPaused(localStorage.getItem('chirality-motion-v1') === 'paused');
      } catch {
        /* Optional storage. */
      }
    });
    preference.addEventListener('change', sync);
    document.addEventListener('visibilitychange', sync);
    return () => {
      preference.removeEventListener('change', sync);
      document.removeEventListener('visibilitychange', sync);
    };
  }, []);
  const toggle = () =>
    setPaused((previous) => {
      try {
        localStorage.setItem(
          'chirality-motion-v1',
          previous ? 'playing' : 'paused',
        );
      } catch {
        /* Optional storage. */
      }
      return !previous;
    });
  const enabled = motionAllowed(paused, reduced, foreground);
  return (
    <MotionContext.Provider value={{ enabled, reduced, paused, toggle }}>
      <div data-site-motion={enabled ? 'running' : 'paused'}>{children}</div>
    </MotionContext.Provider>
  );
}
export const useMotion = () => useContext(MotionContext);
export function MotionControl() {
  const { paused, reduced, toggle } = useMotion();
  return (
    <Button
      variant="ghost"
      className="motion-control"
      disabled={reduced}
      onClick={toggle}
      aria-label={
        reduced
          ? 'Animations disabled by your reduced-motion preference'
          : paused
            ? 'Resume gentle animations'
            : 'Pause all gentle animations'
      }
      aria-pressed={paused || reduced}
    >
      {paused || reduced ? <Play size={15} /> : <Pause size={15} />}
      <span>
        {reduced ? 'Reduced motion' : paused ? 'Resume motion' : 'Pause motion'}
      </span>
    </Button>
  );
}
export function useInView<T extends Element>(
  ref: RefObject<T | null>,
  once = false,
  identity: string | null = null,
) {
  const [visible, setVisible] = useState(false);
  useEffect(() => {
    if (!ref.current) return;
    const observer = new IntersectionObserver(
      ([entry]) => {
        setVisible(entry.isIntersecting);
        if (once && entry.isIntersecting) observer.disconnect();
      },
      { threshold: 0.08 },
    );
    observer.observe(ref.current);
    return () => observer.disconnect();
  }, [ref, once, identity]);
  return visible;
}
/** A capped clock per visible scene; never runs in a hidden chapter or background tab. */
export function useSceneClock<T extends Element>(
  ref: RefObject<T | null>,
  tick: (seconds: number, delta: number) => void,
  active = true,
) {
  const { enabled } = useMotion();
  const visible = useInView(ref);
  const callback = useRef(tick);
  const elapsed = useRef(0);
  useEffect(() => {
    callback.current = tick;
  }, [tick]);
  useEffect(() => {
    if (!enabled || !visible || !active) return;
    let frame = 0,
      previous = 0;
    const loop = (time: number) => {
      if (!previous) previous = time;
      if (time - previous >= 1000 / 30) {
        const delta = Math.min((time - previous) / 1000, 0.08);
        elapsed.current += delta;
        previous = time;
        callback.current(elapsed.current, delta);
      }
      frame = requestAnimationFrame(loop);
    };
    frame = requestAnimationFrame(loop);
    return () => cancelAnimationFrame(frame);
  }, [enabled, visible, active]);
  return enabled && visible && active;
}
/** Automatic demonstrations yield to pointer and keyboard interaction. */
export function useGentleDemo(
  ref: RefObject<HTMLDivElement | null>,
  advance: () => void,
  delay = 14000,
  identity: string | null = null,
) {
  const visible = useInView(ref, false, identity);
  const { enabled } = useMotion();
  const [automatic, setAutomatic] = useState(true);
  const [focused, setFocused] = useState(false);
  const [hovered, setHovered] = useState(false);
  const callback = useRef(advance);
  useEffect(() => {
    callback.current = advance;
  }, [advance]);
  const running = enabled && visible && automatic && !focused && !hovered;
  useEffect(() => {
    if (!running) return;
    const timer = setInterval(() => callback.current(), delay);
    return () => clearInterval(timer);
  }, [running, delay]);
  const stop = () => setAutomatic(false);
  const interaction = (target: EventTarget | null) => {
    if (target instanceof Element && !target.closest('[data-demo-control]'))
      stop();
  };
  return {
    running,
    automatic,
    stop,
    toggle: () => setAutomatic((a) => !a),
    handlers: {
      onPointerEnter: (e: React.PointerEvent) => {
        if (e.pointerType === 'mouse') setHovered(true);
      },
      onPointerLeave: () => setHovered(false),
      onPointerDownCapture: (e: React.PointerEvent) => interaction(e.target),
      onKeyDownCapture: (e: React.KeyboardEvent) => {
        if (e.key !== 'Tab') interaction(e.target);
      },
      onFocusCapture: () => setFocused(true),
      onBlurCapture: (e: React.FocusEvent) => {
        if (!e.currentTarget.contains(e.relatedTarget)) setFocused(false);
      },
    },
  };
}
export function DemoControl({
  automatic,
  toggle,
}: {
  automatic: boolean;
  toggle: () => void;
}) {
  const { enabled, reduced } = useMotion();
  return (
    <Button
      data-demo-control
      variant="ghost"
      size="sm"
      className="demo-control"
      onClick={toggle}
      disabled={!enabled}
      aria-label={
        reduced
          ? 'Automatic demonstration disabled by your reduced-motion preference'
          : !enabled
            ? 'Automatic demonstration paused by motion settings'
            : automatic
              ? 'Pause this automatic demonstration'
              : 'Resume this automatic demonstration'
      }
      aria-pressed={automatic && enabled}
    >
      {automatic && enabled ? <Pause size={12} /> : <Play size={12} />}
      {reduced
        ? 'Motion reduced'
        : !enabled
          ? 'Motion paused'
          : automatic
            ? 'Auto · pause'
            : 'Auto · resume'}
    </Button>
  );
}
export function AmbientExhibit({
  children,
  className = '',
}: {
  children: ReactNode;
  className?: string;
}) {
  const ref = useRef<HTMLDivElement>(null);
  const visible = useInView(ref);
  const { enabled } = useMotion();
  return (
    <div
      ref={ref}
      className={'ambient-exhibit ' + className}
      data-exhibit-motion={visible && enabled ? 'running' : 'paused'}
    >
      {children}
    </div>
  );
}
