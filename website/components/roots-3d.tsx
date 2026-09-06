'use client';
import { useEffect, useRef, useState } from 'react';
import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';
import { Button } from '@/components/ui/button';
import { Switch } from '@/components/ui/switch';
import {
  NativeSelect,
  NativeSelectOption,
} from '@/components/ui/native-select';
import {
  useInView,
  useSceneClock,
  useMotion,
} from '@/components/exhibit-motion';
import { spacePoints, edges, roots } from '@/lib/e6';

type Props = { groups: number[][]; common: number[]; show: boolean[] };
type Viewer = {
  update: (props: Props, isolate: boolean) => void;
  tick: (t: number, dt: number) => void;
  turn: (angle: number) => void;
  reset: () => void;
  inspect: (index: number) => void;
};

export default function Roots3D(props: Props) {
  const container = useRef<HTMLDivElement>(null);
  const api = useRef<Viewer | null>(null);
  const latest = useRef(props);
  const { enabled } = useMotion();
  const motion = useRef(enabled);
  const isolated = useRef(false);
  const [isolate, setIsolate] = useState(false);
  const [unavailable, setUnavailable] = useState(false);
  const [hovered, setHovered] = useState<number | null>(null);
  const [selected, setSelected] = useState(0);
  const [inspectionAnnouncement, setInspectionAnnouncement] = useState('');
  const selectedRef = useRef(0);
  const reading = useRef(false);
  const ready = useInView(container, true);
  useSceneClock(container, (t, dt) => api.current?.tick(t, dt), !unavailable);
  useEffect(() => {
    latest.current = props;
    motion.current = enabled;
    isolated.current = isolate;
    api.current?.update(props, isolate);
  }, [props, isolate, enabled]);
  useEffect(() => {
    selectedRef.current = selected;
    api.current?.inspect(selected);
  }, [selected]);
  useEffect(() => {
    const element = container.current;
    if (!element || !ready) return;
    let disposed = false;
    let mounted = true;
    const cleanups: Array<() => void> = [];
    // Register ownership immediately: partial setup and runtime failure share teardown.
    const own = <T extends { dispose: () => void }>(resource: T): T => {
      cleanups.push(() => resource.dispose());
      return resource;
    };
    const release = () => {
      if (disposed) return;
      disposed = true;
      api.current = null;
      for (const cleanup of cleanups.reverse()) {
        try {
          cleanup();
        } catch {
          /* Finish releasing the remaining resources. */
        }
      }
      cleanups.length = 0;
    };
    const teardown = () => {
      mounted = false;
      release();
    };
    const fail = () => {
      release();
      queueMicrotask(() => {
        if (mounted) setUnavailable(true);
      });
    };
    try {
      const renderer = new THREE.WebGLRenderer({
        antialias: true,
        alpha: true,
        powerPreference: 'low-power',
      });
      cleanups.push(() => renderer.domElement.remove());
      cleanups.push(() => renderer.forceContextLoss());
      own(renderer);
      let shaderFailed = false;
      renderer.debug.checkShaderErrors = true;
      renderer.debug.onShaderError = () => {
        if (shaderFailed || disposed) return;
        shaderFailed = true;
        // A failed shader may report without throwing. Finish Three's current
        // program setup before disposing its resources.
        queueMicrotask(() => {
          if (mounted) fail();
        });
      };
      cleanups.push(() => {
        renderer.debug.onShaderError = null;
      });
      renderer.setPixelRatio(Math.min(devicePixelRatio, 1.5));
      renderer.toneMapping = THREE.ACESFilmicToneMapping;
      renderer.toneMappingExposure = 1.35;
      renderer.domElement.setAttribute('role', 'img');
      renderer.domElement.setAttribute(
        'aria-label',
        'E6 root projection. Gold marks the common intersection; a white wireframe marks the inspected root. Drag to turn, or use the controls and root selector below.',
      );
      element.appendChild(renderer.domElement);
      const scene = new THREE.Scene();
      const camera = new THREE.PerspectiveCamera(40, 1, 0.1, 60);
      camera.position.set(3.8, 1.8, 8.2);
      const controls = own(new OrbitControls(camera, renderer.domElement));
      controls.enableZoom = false;
      controls.enablePan = false;
      controls.rotateSpeed = 0.55;
      controls.enableDamping = false;
      controls.saveState();
      const group = new THREE.Group();
      scene.add(group);
      scene.add(new THREE.HemisphereLight('#c7e4ff', '#16263c', 2.5));
      const key = new THREE.DirectionalLight('#e8f4ff', 4);
      key.position.set(3, 6, 5);
      scene.add(key);
      const rim = new THREE.PointLight('#edaf76', 55, 20);
      rim.position.set(-4, 1, -3);
      scene.add(rim);
      const sphere = own(new THREE.SphereGeometry(1, 18, 12));
      const material = own(
        new THREE.MeshStandardMaterial({
          metalness: 0.4,
          roughness: 0.24,
        }),
      );
      const nodes = own(
        new THREE.InstancedMesh(sphere, material, roots.length),
      );
      const dummy = new THREE.Object3D();
      group.add(nodes);
      const inspectionMaterial = own(
        new THREE.MeshBasicMaterial({
          color: '#ffffff',
          wireframe: true,
          transparent: true,
          opacity: 0.7,
        }),
      );
      const inspectionMarker = new THREE.Mesh(sphere, inspectionMaterial);
      inspectionMarker.scale.setScalar(0.14);
      inspectionMarker.position.fromArray(spacePoints[selectedRef.current]);
      group.add(inspectionMarker);
      const colours = roots.map(() => new THREE.Color('#607c9d'));
      const targets = colours.map((c) => c.clone());
      const sizes = roots.map(() => 0.048),
        targetSizes = [...sizes];
      let commonSet = new Set<number>();
      const baseGeometry = own(new THREE.BufferGeometry());
      baseGeometry.setAttribute(
        'position',
        new THREE.Float32BufferAttribute(
          edges.flatMap(([a, b]) => [...spacePoints[a], ...spacePoints[b]]),
          3,
        ),
      );
      const baseMaterial = own(
        new THREE.LineBasicMaterial({
          color: '#6d94c0',
          transparent: true,
          opacity: 0.09,
          depthWrite: false,
        }),
      );
      const baseLines = new THREE.LineSegments(baseGeometry, baseMaterial);
      group.add(baseLines);
      const selectedGeometry = own(new THREE.BufferGeometry());
      const selectedPositions = new THREE.Float32BufferAttribute(
        new Float32Array(edges.length * 6),
        3,
      );
      const selectedColours = new THREE.Float32BufferAttribute(
        new Float32Array(edges.length * 6),
        3,
      );
      selectedGeometry.setAttribute('position', selectedPositions);
      selectedGeometry.setAttribute('color', selectedColours);
      selectedGeometry.setDrawRange(0, 0);
      const selectedMaterial = own(
        new THREE.LineBasicMaterial({
          vertexColors: true,
          transparent: true,
          opacity: 0.48,
          depthWrite: false,
        }),
      );
      group.add(new THREE.LineSegments(selectedGeometry, selectedMaterial));
      const goldGeometry = own(new THREE.BufferGeometry());
      const goldPositions = new THREE.Float32BufferAttribute(
        new Float32Array(edges.length * 6),
        3,
      );
      goldGeometry.setAttribute('position', goldPositions);
      goldGeometry.setDrawRange(0, 0);
      const goldMaterial = own(
        new THREE.LineBasicMaterial({
          color: '#ffdc99',
          transparent: true,
          opacity: 0.96,
          depthWrite: false,
        }),
      );
      group.add(new THREE.LineSegments(goldGeometry, goldMaterial));
      const glowGeometry = own(new THREE.BufferGeometry());
      glowGeometry.setAttribute(
        'position',
        new THREE.Float32BufferAttribute(spacePoints.flat(), 3),
      );
      glowGeometry.setAttribute(
        'colour',
        new THREE.Float32BufferAttribute(
          roots.flatMap(() => [0.4, 0.6, 1]),
          3,
        ),
      );
      glowGeometry.setAttribute(
        'size',
        new THREE.Float32BufferAttribute(
          roots.map(() => 14),
          1,
        ),
      );
      const glowMaterial = own(
        new THREE.ShaderMaterial({
          transparent: true,
          depthWrite: false,
          blending: THREE.AdditiveBlending,
          vertexShader:
            'attribute vec3 colour; attribute float size; varying vec3 tint; void main(){tint=colour;vec4 mv=modelViewMatrix*vec4(position,1.);gl_PointSize=size*(8./-mv.z);gl_Position=projectionMatrix*mv;}',
          fragmentShader:
            'varying vec3 tint;void main(){float r=length(gl_PointCoord-.5)*2.;float a=exp(-5.*r*r)*.3;if(r>1.)discard;gl_FragColor=vec4(tint,a);}',
        }),
      );
      const glow = new THREE.Points(glowGeometry, glowMaterial);
      group.add(glow);
      // Faint frame marks the view, not an additional root or subsystem.
      const frameGeo = own(new THREE.BufferGeometry()).setFromPoints(
        Array.from({ length: 129 }, (_, i) => {
          const a = (i / 128) * Math.PI * 2;
          return new THREE.Vector3(
            2.65 * Math.cos(a),
            -2.65,
            2.65 * Math.sin(a),
          );
        }),
      );
      const frameMat = own(
        new THREE.LineBasicMaterial({
          color: '#466381',
          transparent: true,
          opacity: 0.25,
        }),
      );
      scene.add(new THREE.Line(frameGeo, frameMat));
      let rootUnderPointer = false,
        dragging = false,
        holdUntil = 0,
        initial = true;
      const draw = () => {
        if (disposed || shaderFailed || document.hidden) return;
        try {
          renderer.render(scene, camera);
        } catch {
          fail();
        }
      };
      const syncNodes = (blend: number) => {
        roots.forEach((_, i) => {
          colours[i].lerp(targets[i], blend);
          sizes[i] += (targetSizes[i] - sizes[i]) * blend;
          dummy.position.fromArray(spacePoints[i]);
          dummy.scale.setScalar(sizes[i]);
          dummy.updateMatrix();
          nodes.setMatrixAt(i, dummy.matrix);
          nodes.setColorAt(i, colours[i]);
          const c = colours[i];
          glowGeometry.attributes.colour.setXYZ(i, c.r, c.g, c.b);
          glowGeometry.attributes.size.setX(
            i,
            sizes[i] < 0.025 ? 0 : commonSet.has(i) ? 35 : 17,
          );
        });
        nodes.instanceMatrix.needsUpdate = true;
        if (nodes.instanceColor) nodes.instanceColor.needsUpdate = true;
        glowGeometry.attributes.colour.needsUpdate = true;
        glowGeometry.attributes.size.needsUpdate = true;
      };
      const update = ({ groups, common, show }: Props, only: boolean) => {
        if (disposed) return;
        commonSet = new Set(common);
        const membership = roots.map((_, i) =>
          groups.findIndex((g, k) => show[k] && g.includes(i)),
        );
        roots.forEach((_, i) => {
          const j = membership[i],
            active = j >= 0;
          targets[i].set(
            commonSet.has(i)
              ? '#ffdc99'
              : only
                ? '#142338'
                : j < 0
                  ? '#263b52'
                  : ['#83c7ff', '#f0a588', '#82d6b2'][j],
          );
          targetSizes[i] = commonSet.has(i)
            ? 0.088
            : only
              ? 0.015
              : active
                ? 0.052
                : 0.028;
        });
        const highlight = edges.filter(
          ([a, b]) =>
            !only &&
            groups.some((g, k) => show[k] && g.includes(a) && g.includes(b)),
        );
        highlight.forEach(([a, b], i) => {
          selectedPositions.setXYZ(
            i * 2,
            spacePoints[a][0],
            spacePoints[a][1],
            spacePoints[a][2],
          );
          selectedPositions.setXYZ(
            i * 2 + 1,
            spacePoints[b][0],
            spacePoints[b][1],
            spacePoints[b][2],
          );
          selectedColours.setXYZ(
            i * 2,
            targets[a].r,
            targets[a].g,
            targets[a].b,
          );
          selectedColours.setXYZ(
            i * 2 + 1,
            targets[b].r,
            targets[b].g,
            targets[b].b,
          );
        });
        selectedPositions.needsUpdate = true;
        selectedColours.needsUpdate = true;
        selectedGeometry.setDrawRange(0, highlight.length * 2);
        selectedGeometry.computeBoundingSphere();
        const goldEdges = edges.filter(
          ([a, b]) => commonSet.has(a) && commonSet.has(b),
        );
        goldEdges.forEach(([a, b], i) => {
          goldPositions.setXYZ(
            i * 2,
            spacePoints[a][0],
            spacePoints[a][1],
            spacePoints[a][2],
          );
          goldPositions.setXYZ(
            i * 2 + 1,
            spacePoints[b][0],
            spacePoints[b][1],
            spacePoints[b][2],
          );
        });
        goldPositions.needsUpdate = true;
        goldGeometry.setDrawRange(0, goldEdges.length * 2);
        goldGeometry.computeBoundingSphere();
        baseMaterial.opacity = only ? 0.025 : 0.09;
        // Paused/reduced-motion users still get every selected result immediately.
        if (initial || !motion.current) syncNodes(1);
        initial = false;
        draw();
      };
      const resize = () => {
        if (disposed) return;
        const w = element.clientWidth,
          h = element.clientHeight;
        if (!w || !h) return;
        try {
          renderer.setSize(w, h, false);
          camera.aspect = w / h;
          camera.updateProjectionMatrix();
          draw();
        } catch {
          fail();
        }
      };
      const observer = new ResizeObserver(resize);
      cleanups.push(() => observer.disconnect());
      observer.observe(element);
      const raycaster = new THREE.Raycaster(),
        pointer = new THREE.Vector2();
      const point = (event: PointerEvent) => {
        if (dragging) return;
        const r = renderer.domElement.getBoundingClientRect();
        pointer.set(
          ((event.clientX - r.left) / r.width) * 2 - 1,
          -((event.clientY - r.top) / r.height) * 2 + 1,
        );
        raycaster.setFromCamera(pointer, camera);
        const hit = raycaster.intersectObject(nodes)[0];
        rootUnderPointer = Boolean(hit);
        setHovered(hit?.instanceId ?? null);
        if (hit) holdUntil = performance.now() + 2000;
      };
      const leave = () => {
        rootUnderPointer = false;
        setHovered(null);
      };
      const start = () => {
        dragging = true;
        leave();
      };
      const end = () => {
        dragging = false;
        holdUntil = performance.now() + 3500;
      };
      const lost = (event: Event) => {
        event.preventDefault();
        fail();
      };
      renderer.domElement.addEventListener('webglcontextlost', lost);
      cleanups.push(() =>
        renderer.domElement.removeEventListener('webglcontextlost', lost),
      );
      renderer.domElement.addEventListener('pointermove', point);
      cleanups.push(() =>
        renderer.domElement.removeEventListener('pointermove', point),
      );
      renderer.domElement.addEventListener('pointerleave', leave);
      cleanups.push(() =>
        renderer.domElement.removeEventListener('pointerleave', leave),
      );
      controls.addEventListener('start', start);
      cleanups.push(() => controls.removeEventListener('start', start));
      controls.addEventListener('end', end);
      cleanups.push(() => controls.removeEventListener('end', end));
      controls.addEventListener('change', draw);
      cleanups.push(() => controls.removeEventListener('change', draw));
      api.current = {
        update,
        tick: (t, dt) => {
          if (disposed) return;
          if (
            !dragging &&
            !rootUnderPointer &&
            !reading.current &&
            performance.now() > holdUntil
          ) {
            group.rotation.y += dt * 0.075;
            group.rotation.x = Math.sin(t * 0.095) * 0.08;
          }
          syncNodes(initial ? 1 : Math.min(1, dt * 5));
          glowMaterial.opacity = 0.9;
          controls.update();
          draw();
        },
        turn: (angle) => {
          group.rotation.y += angle;
          holdUntil = performance.now() + 3500;
          draw();
        },
        reset: () => {
          group.rotation.set(0, 0, 0);
          controls.reset();
          holdUntil = performance.now() + 2000;
          draw();
        },
        inspect: (index) => {
          inspectionMarker.position.fromArray(spacePoints[index]);
          holdUntil = performance.now() + 5000;
          draw();
        },
      };
      resize();
      update(latest.current, isolated.current);
    } catch {
      fail();
    }
    return teardown;
  }, [ready]);
  return (
    <div
      className="three-view"
      onFocusCapture={() => {
        reading.current = true;
      }}
      onBlurCapture={(event) => {
        if (!event.currentTarget.contains(event.relatedTarget))
          reading.current = false;
      }}
    >
      <div className="three-scene-heading">
        <span>THE E₆ ROOT SYSTEM</span>
        <strong>
          72 <small>directions</small>
        </strong>
      </div>
      <div
        className="three-canvas"
        ref={container}
        data-unavailable={unavailable}
      />
      {unavailable && (
        <output className="webgl-fallback">
          3D is unavailable here. You can still inspect all 72 roots below,
          switch to the flat projection, and run every numerical check.
        </output>
      )}
      <div className="root-readout" aria-live="off">
        {hovered === null ? (
          <>
            <span>CHOOSE A ROOT BELOW · DRAG TO ROTATE</span>
            <strong>{props.common.length} common roots in gold</strong>
          </>
        ) : (
          <>
            <span>
              ROOT {hovered + 1}
              {props.common.includes(hovered) ? ' · COMMON INTERSECTION' : ''}
            </span>
            <strong>({roots[hovered].join(', ')})</strong>
          </>
        )}
      </div>
      <div className="three-toolbar">
        <Button
          variant="ghost"
          size="sm"
          disabled={unavailable}
          onClick={() => api.current?.turn(-Math.PI / 7)}
        >
          ↶ Turn left
        </Button>
        <Button
          variant="ghost"
          size="sm"
          disabled={unavailable}
          onClick={() => api.current?.turn(Math.PI / 7)}
        >
          Turn right ↷
        </Button>
        <Button
          variant="ghost"
          size="sm"
          disabled={unavailable}
          onClick={() => api.current?.reset()}
        >
          Reset view
        </Button>
      </div>
      <label className="root-isolate" htmlFor="root-isolate">
        <Switch
          id="root-isolate"
          checked={isolate}
          disabled={unavailable}
          onCheckedChange={setIsolate}
        />{' '}
        Focus the common intersection
      </label>
      <div className="root-inspector">
        <label htmlFor="root-inspect">
          Inspect any root · keyboard or pointer
        </label>
        <NativeSelect
          id="root-inspect"
          value={selected}
          onChange={(event) => {
            const index = Number(event.target.value);
            setSelected(index);
            setInspectionAnnouncement(
              `Root ${index + 1}: (${roots[index].join(', ')}). ${['D', 'A', 'Θ'].map((label, i) => `${label}: ${props.groups[i].includes(index) ? 'yes' : 'no'}`).join('. ')}. ${props.common.includes(index) ? 'Common intersection.' : 'Not common.'}`,
            );
          }}
        >
          {roots.map((_, i) => (
            <NativeSelectOption key={i} value={i}>
              Root {i + 1}
              {props.common.includes(i) ? ' · common' : ''}
            </NativeSelectOption>
          ))}
        </NativeSelect>
        <output htmlFor="root-inspect" aria-live="off">
          Root {selected + 1}: ({roots[selected].join(', ')})<br />
          {['D', 'A', 'Θ']
            .map(
              (label, i) =>
                `${label}: ${props.groups[i].includes(selected) ? 'yes' : 'no'}`,
            )
            .join(' · ')}
          <br />
          {props.common.includes(selected)
            ? 'In the common intersection.'
            : 'Not in the common intersection.'}
        </output>
        <output className="sr-only" aria-live="polite">
          {inspectionAnnouncement}
        </output>
        <p>
          Six integer coordinates in the simple-root basis. Membership is
          calculated from the selected cell, including layers you have hidden.
          The white inspection marker does not change membership.
        </p>
      </div>
      <p className="three-caption">
        A 3D projection of six-dimensional root data. Gold edges join common
        roots with inner product 1. Drag to explore; automatic rotation yields
        while you inspect.
      </p>
    </div>
  );
}
