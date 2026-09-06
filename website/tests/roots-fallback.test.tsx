import { StrictMode } from 'react';
import { act, fireEvent, render, screen } from '@testing-library/react';
import { beforeEach, expect, it, vi } from 'vitest';
import { MotionProvider } from '@/components/exhibit-motion';
import { inspectCell, roots, edges, spacePoints } from '@/lib/e6';
import * as THREE from 'three';

const hardware = vi.hoisted(() => ({
  fail: true,
  failAt: '',
  observers: [] as Array<{
    callback: () => void;
    disconnect: ReturnType<typeof vi.fn>;
  }>,
  renderers: [] as Array<{
    domElement: HTMLCanvasElement;
    render: ReturnType<typeof vi.fn>;
    dispose: ReturnType<typeof vi.fn>;
    forceContextLoss: ReturnType<typeof vi.fn>;
    debug: { checkShaderErrors: boolean; onShaderError: (() => void) | null };
  }>,
}));
// Replace only the GPU boundary. React, Three geometry and OrbitControls remain real.
vi.mock('three', async (importOriginal) => ({
  ...(await importOriginal<typeof import('three')>()),
  WebGLRenderer: class {
    domElement = document.createElement('canvas');
    debug = {
      checkShaderErrors: true,
      onShaderError: null as (() => void) | null,
    };
    render = vi.fn((_scene: THREE.Scene, _camera: THREE.Camera) => {
      if (hardware.failAt === 'render') throw new Error('draw failed');
    });
    dispose = vi.fn();
    forceContextLoss = vi.fn();
    setPixelRatio = vi.fn(() => {
      if (hardware.failAt === 'pixel') throw new Error('setup failed');
    });
    setSize = vi.fn(() => {
      if (hardware.failAt === 'size') throw new Error('resize failed');
    });
    constructor() {
      if (hardware.fail) throw new Error('WebGL unavailable');
      hardware.renderers.push(this);
    }
  },
}));
import Roots3D from '@/components/roots-3d';

beforeEach(() => {
  hardware.fail = true;
  hardware.failAt = '';
  hardware.renderers.length = 0;
  hardware.observers.length = 0;
  vi.stubGlobal(
    'ResizeObserver',
    class {
      constructor(public callback: () => void) {
        hardware.observers.push(this);
      }
      observe() {}
      disconnect = vi.fn();
    },
  );
});

it('retains every root and its data when WebGL cannot initialise', async () => {
  const inspected = inspectCell(3);
  const view = render(
    <StrictMode>
      <MotionProvider>
        <Roots3D
          groups={[inspected.D, inspected.A, inspected.T]}
          common={inspected.common}
          show={[true, true, true]}
        />
      </MotionProvider>
    </StrictMode>,
  );
  await act(async () => {
    await Promise.resolve();
  });
  expect(screen.getByText(/3D is unavailable here/)).toBeTruthy();
  for (const name of ['↶ Turn left', 'Turn right ↷', 'Reset view']) {
    expect(
      (screen.getByRole('button', { name }) as HTMLButtonElement).disabled,
    ).toBe(true);
  }
  const selector = screen.getByLabelText(
    'Inspect any root · keyboard or pointer',
  );
  if (!(selector instanceof HTMLSelectElement))
    throw new Error('Missing native root selector');
  expect(selector.disabled).toBe(false);
  expect(selector.options).toHaveLength(72);
  fireEvent.change(selector, { target: { value: '15' } });
  expect(selector.value).toBe('15');
  expect(
    view.container.querySelector('output[for="root-inspect"]')?.textContent,
  ).toContain(`Root 16: (${roots[15].join(', ')})`);
  expect(
    view.container.querySelector('output[aria-live="polite"]')?.textContent,
  ).toContain('Root 16:');
  expect(view.container.querySelector('canvas')).toBeNull();
});

it('handles a context-loss event and disposes the renderer on unmount', async () => {
  hardware.fail = false;
  const inspected = inspectCell(5);
  const view = render(
    <StrictMode>
      <MotionProvider>
        <Roots3D
          groups={[inspected.D, inspected.A, inspected.T]}
          common={inspected.common}
          show={[true, true, true]}
        />
      </MotionProvider>
    </StrictMode>,
  );
  await act(async () => {
    await Promise.resolve();
  });
  const renderer = hardware.renderers.at(-1)!;
  expect(renderer).toBeTruthy();
  expect(renderer.render).toHaveBeenCalled();
  const lost = new Event('webglcontextlost', { cancelable: true });
  fireEvent(renderer.domElement, lost);
  await act(async () => {
    await Promise.resolve();
  });
  expect(lost.defaultPrevented).toBe(true);
  expect(screen.getByText(/3D is unavailable here/)).toBeTruthy();
  expect(
    screen
      .getAllByRole('status')
      .some((status) => status.textContent?.includes('3D is unavailable here')),
  ).toBe(true);
  expect(
    (screen.getByRole('button', { name: 'Reset view' }) as HTMLButtonElement)
      .disabled,
  ).toBe(true);
  const selector = screen.getByLabelText(
    'Inspect any root · keyboard or pointer',
  );
  fireEvent.change(selector, { target: { value: '71' } });
  expect(
    view.container.querySelector('output[for="root-inspect"]')?.textContent,
  ).toContain('Root 72:');
  view.unmount();
  for (const instance of hardware.renderers) {
    expect(instance.dispose).toHaveBeenCalledOnce();
    expect(instance.forceContextLoss).toHaveBeenCalledOnce();
    expect(instance.domElement.isConnected).toBe(false);
  }
});

function rootView(cell = 5, show = [true, true, true]) {
  const data = inspectCell(cell);
  return (
    <MotionProvider>
      <Roots3D
        groups={[data.D, data.A, data.T]}
        common={data.common}
        show={show}
      />
    </MotionProvider>
  );
}
const settle = async () => {
  await act(async () => {
    await Promise.resolve();
  });
};

it.each(['pixel', 'size', 'render'])(
  'releases partial setup after a %s failure',
  async (failAt) => {
    hardware.fail = false;
    hardware.failAt = failAt;
    vi.spyOn(HTMLElement.prototype, 'clientWidth', 'get').mockReturnValue(800);
    vi.spyOn(HTMLElement.prototype, 'clientHeight', 'get').mockReturnValue(600);
    const view = render(<StrictMode>{rootView()}</StrictMode>);
    await settle();
    expect(screen.getByText(/3D is unavailable here/)).toBeTruthy();
    expect(view.container.querySelector('canvas')).toBeNull();
    view.unmount();
    for (const renderer of hardware.renderers) {
      expect(renderer.dispose).toHaveBeenCalledOnce();
      expect(renderer.forceContextLoss).toHaveBeenCalledOnce();
    }
    for (const observer of hardware.observers)
      expect(observer.disconnect).toHaveBeenCalledOnce();
  },
);

it('stops its clock and releases geometry after a later draw failure', async () => {
  hardware.fail = false;
  vi.useFakeTimers();
  const disposeGeometry = vi.spyOn(THREE.BufferGeometry.prototype, 'dispose');
  const disposeMaterial = vi.spyOn(THREE.Material.prototype, 'dispose');
  const disposeInstances = vi.spyOn(THREE.InstancedMesh.prototype, 'dispose');
  const view = render(rootView());
  await settle();
  await act(async () => {
    vi.advanceTimersByTime(200);
  });
  const renderer = hardware.renderers.at(-1)!;
  hardware.failAt = 'render';
  await act(async () => {
    vi.advanceTimersByTime(200);
  });
  expect(screen.getByText(/3D is unavailable here/)).toBeTruthy();
  const calls = renderer.render.mock.calls.length;
  await act(async () => {
    vi.advanceTimersByTime(5000);
  });
  expect(renderer.render.mock.calls.length).toBe(calls);
  expect(vi.getTimerCount()).toBe(0);
  expect(disposeGeometry).toHaveBeenCalledTimes(6);
  expect(disposeMaterial).toHaveBeenCalledTimes(7);
  expect(disposeInstances).toHaveBeenCalledOnce();
  view.unmount();
  expect(renderer.dispose).toHaveBeenCalledOnce();
});

it('handles later resize failure even if renderer disposal also throws', async () => {
  hardware.fail = false;
  vi.spyOn(HTMLElement.prototype, 'clientWidth', 'get').mockReturnValue(800);
  vi.spyOn(HTMLElement.prototype, 'clientHeight', 'get').mockReturnValue(600);
  const view = render(rootView());
  await settle();
  const renderer = hardware.renderers.at(-1)!;
  renderer.dispose.mockImplementation(() => {
    throw new Error('dispose failed');
  });
  hardware.failAt = 'size';
  act(() => hardware.observers.at(-1)!.callback());
  await settle();
  expect(screen.getByText(/3D is unavailable here/)).toBeTruthy();
  expect(renderer.forceContextLoss).toHaveBeenCalledOnce();
  expect(renderer.domElement.isConnected).toBe(false);
  view.unmount();
  expect(renderer.dispose).toHaveBeenCalledOnce();
});

it('handles a non-throwing shader error after the current render finishes', async () => {
  hardware.fail = false;
  const view = render(rootView());
  await settle();
  const renderer = hardware.renderers.at(-1)!;
  expect(renderer.debug.checkShaderErrors).toBe(true);
  const reportError = renderer.debug.onShaderError!;
  act(() => {
    reportError();
    reportError();
  });
  expect(renderer.dispose).not.toHaveBeenCalled();
  await settle();
  expect(screen.getByText(/3D is unavailable here/)).toBeTruthy();
  expect(renderer.dispose).toHaveBeenCalledOnce();
  expect(renderer.debug.onShaderError).toBeNull();
  view.unmount();
  expect(renderer.dispose).toHaveBeenCalledOnce();
});

it('reuses line buffers while preserving exact edge selections across all cells', async () => {
  hardware.fail = false;
  const view = render(rootView());
  await settle();
  const renderer = hardware.renderers.at(-1)!;
  const scene = renderer.render.mock.calls.at(-1)![0] as THREE.Scene;
  const lines: THREE.LineSegments<
    THREE.BufferGeometry,
    THREE.LineBasicMaterial
  >[] = [];
  scene.traverse((object) => {
    if (object instanceof THREE.LineSegments) lines.push(object);
  });
  const selected = lines.find((line) => line.material.vertexColors)!.geometry;
  const gold = lines.find(
    (line) => line.material.color.getHexString() === 'ffdc99',
  )!.geometry;
  const selectedPositions = selected.getAttribute('position');
  const selectedColours = selected.getAttribute('color');
  const goldPositions = gold.getAttribute('position');
  for (let cell = 0; cell < 6; cell++) {
    for (const show of [
      [true, true, true],
      [false, true, false],
      [false, false, false],
    ]) {
      view.rerender(rootView(cell, show));
      const data = inspectCell(cell);
      const groups = [data.D, data.A, data.T];
      const expected = edges.filter(([a, b]) =>
        groups.some(
          (group, k) => show[k] && group.includes(a) && group.includes(b),
        ),
      );
      const expectedGold = edges.filter(
        ([a, b]) => data.common.includes(a) && data.common.includes(b),
      );
      expect(selected.getAttribute('position')).toBe(selectedPositions);
      expect(selected.getAttribute('color')).toBe(selectedColours);
      expect(gold.getAttribute('position')).toBe(goldPositions);
      expect(selected.drawRange.count).toBe(expected.length * 2);
      expect(gold.drawRange.count).toBe(expectedGold.length * 2);
      for (const [geometry, active] of [
        [selected, expected],
        [gold, expectedGold],
      ] as const) {
        expect(
          Array.from(geometry.getAttribute('position').array).slice(
            0,
            active.length * 6,
          ),
        ).toEqual(
          Array.from(
            new Float32Array(
              active.flatMap(([a, b]) => [
                ...spacePoints[a],
                ...spacePoints[b],
              ]),
            ),
          ),
        );
      }
    }
  }
  fireEvent.click(
    screen.getByRole('switch', { name: 'Focus the common intersection' }),
  );
  expect(selected.drawRange.count).toBe(0);
  expect(selected.getAttribute('position')).toBe(selectedPositions);
  view.unmount();
});
