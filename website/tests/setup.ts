import { afterEach, beforeEach, vi } from 'vitest';
import { cleanup } from '@testing-library/react';

export const intersections = new Set<TestIntersectionObserver>();
export class TestIntersectionObserver {
  targets = new Set<Element>();
  constructor(private callback: IntersectionObserverCallback) {
    intersections.add(this);
  }
  observe(target: Element) {
    this.targets.add(target);
    this.emit(true);
  }
  unobserve(target: Element) {
    this.targets.delete(target);
  }
  disconnect() {
    this.targets.clear();
    intersections.delete(this);
  }
  emit(isIntersecting: boolean) {
    this.callback(
      [...this.targets].map(
        (target) => ({ target, isIntersecting }) as IntersectionObserverEntry,
      ),
      this as unknown as IntersectionObserver,
    );
  }
}

export function installMotionPreference(initial = false) {
  const listeners = new Set<() => void>();
  const media = {
    matches: initial,
    media: '(prefers-reduced-motion: reduce)',
    addEventListener: (_name: string, listener: () => void) =>
      listeners.add(listener),
    removeEventListener: (_name: string, listener: () => void) =>
      listeners.delete(listener),
    change(value: boolean) {
      this.matches = value;
      listeners.forEach((listener) => listener());
    },
  };
  vi.stubGlobal(
    'matchMedia',
    vi.fn(() => media),
  );
  return { media, listeners };
}

beforeEach(() => {
  localStorage.clear();
  history.replaceState(null, '', '/');
  vi.stubGlobal('IntersectionObserver', TestIntersectionObserver);
  vi.spyOn(document, 'hidden', 'get').mockReturnValue(false);
  installMotionPreference();
});

afterEach(() => {
  cleanup();
  intersections.clear();
  vi.useRealTimers();
  vi.restoreAllMocks();
  vi.unstubAllGlobals();
});
