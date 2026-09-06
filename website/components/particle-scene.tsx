'use client';
import { useEffect, useRef, useState } from 'react';
import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';
import { Button } from '@/components/ui/button';
import { useSceneClock } from '@/components/exhibit-motion';
import { chiralPacket, transverseWave } from '@/lib/scene-geometry';
import type { Particle } from '@/lib/particle-physics';

export default function ParticleScene({
  particle,
  coupling = 0,
  vectorlike = false,
  massless = false,
}: {
  particle: Particle;
  coupling?: number;
  vectorlike?: boolean;
  massless?: boolean;
}) {
  const host = useRef<HTMLDivElement>(null);
  const controlsRef = useRef<{
    turn: () => void;
    update: (v: number) => void;
    tick: (t: number, dt: number) => void;
  } | null>(null);
  const [failed, setFailed] = useState(false);
  const latest = useRef(coupling);
  useSceneClock(host, (t, dt) => controlsRef.current?.tick(t, dt));
  useEffect(() => {
    latest.current = coupling;
    controlsRef.current?.update(coupling);
  }, [coupling]);
  useEffect(() => {
    const element = host.current;
    if (!element) return;
    let renderer: THREE.WebGLRenderer;
    try {
      renderer = new THREE.WebGLRenderer({
        alpha: true,
        antialias: true,
        powerPreference: 'low-power',
      });
    } catch {
      queueMicrotask(() => setFailed(true));
      return;
    }
    renderer.setPixelRatio(Math.min(devicePixelRatio, 1.5));
    renderer.toneMapping = THREE.ACESFilmicToneMapping;
    renderer.toneMappingExposure = 1.25;
    renderer.domElement.setAttribute('role', 'img');
    renderer.domElement.setAttribute(
      'aria-label',
      'Symbolic field illustration for ' +
        particle.name +
        '. Left and right components are labelled below. The wave shapes do not depict a particle’s physical shape.',
    );
    element.appendChild(renderer.domElement);
    const scene = new THREE.Scene();
    const camera = new THREE.PerspectiveCamera(38, 1, 0.1, 50);
    camera.position.set(0, 0.35, 7.8);
    const orbit = new OrbitControls(camera, renderer.domElement);
    orbit.enableZoom = false;
    orbit.enablePan = false;
    orbit.enableDamping = false;
    orbit.minAzimuthAngle = -0.65;
    orbit.maxAzimuthAngle = 0.65;
    orbit.minPolarAngle = 1.12;
    orbit.maxPolarAngle = 1.95;
    orbit.rotateSpeed = 0.45;
    scene.add(new THREE.HemisphereLight('#c9e6ff', '#13172b', 2.5));
    const key = new THREE.DirectionalLight('#d2eaff', 4);
    key.position.set(2, 3, 5);
    scene.add(key);
    const rim = new THREE.PointLight('#e6997f', 50, 15);
    rim.position.set(-3, -1, 2);
    scene.add(rim);
    const group = new THREE.Group();
    scene.add(group);
    const geometries: THREE.BufferGeometry[] = [],
      materials: THREE.Material[] = [];
    const fermion = particle.kind !== 'boson' && particle.kind !== 'higgs';
    const colour =
      particle.kind === 'quark'
        ? '#91cfff'
        : particle.kind === 'higgs'
          ? '#c8a5f1'
          : particle.kind === 'boson'
            ? '#9cddc0'
            : '#f5b391';
    const packets: THREE.Group[] = [],
      travellers: {
        mesh: THREE.Mesh;
        curve: THREE.CatmullRomCurve3;
        phase: number;
      }[] = [];
    const tube = (
      coords: [number, number, number][],
      colour: string,
      radius: number,
      opacity = 1,
    ) => {
      const curve = new THREE.CatmullRomCurve3(
        coords.map((p) => new THREE.Vector3(...p)),
      );
      const geo = new THREE.TubeGeometry(curve, 100, radius, 7, false);
      const mat = new THREE.MeshStandardMaterial({
        color: colour,
        emissive: colour,
        emissiveIntensity: 0.3,
        metalness: 0.25,
        roughness: 0.28,
        transparent: true,
        opacity,
      });
      geometries.push(geo);
      materials.push(mat);
      return { mesh: new THREE.Mesh(geo, mat), curve };
    };
    const moteGeometry = new THREE.SphereGeometry(0.043, 12, 8);
    geometries.push(moteGeometry);
    const addMote = (
      parent: THREE.Group,
      curve: THREE.CatmullRomCurve3,
      tint: string,
      phase: number,
    ) => {
      const mat = new THREE.MeshBasicMaterial({ color: tint });
      materials.push(mat);
      const mesh = new THREE.Mesh(moteGeometry, mat);
      mesh.position.copy(curve.getPointAt(phase));
      parent.add(mesh);
      travellers.push({ mesh, curve, phase });
    };
    if (fermion) {
      [-1, 1].forEach((hand, index) => {
        const packet = new THREE.Group();
        packet.position.x = hand * 1.18;
        group.add(packet);
        packets.push(packet);
        const ghost = particle.kind === 'neutrino' && index === 1;
        const tint = index === 0 || vectorlike ? colour : '#8fc9ff';
        if (!ghost) {
          for (let ribbon = 0; ribbon < 3; ribbon++) {
            const { mesh, curve } = tube(
              chiralPacket(hand as -1 | 1, (ribbon * 2 * Math.PI) / 3),
              tint,
              ribbon === 0 ? 0.045 : 0.019,
              ribbon === 0 ? 0.95 : 0.48,
            );
            packet.add(mesh);
            addMote(packet, curve, '#fff2d3', ribbon / 3);
          }
        }
        const outline = new THREE.BufferGeometry().setFromPoints(
          Array.from({ length: 97 }, (_, i) => {
            const a = (i / 96) * Math.PI * 2;
            return new THREE.Vector3(0.77 * Math.cos(a), 1.42 * Math.sin(a), 0);
          }),
        );
        const outlineMat = new THREE.LineDashedMaterial({
          color: ghost ? '#52667e' : tint,
          transparent: true,
          opacity: ghost ? 0.35 : 0.16,
          dashSize: 0.045,
          gapSize: 0.075,
        });
        const contour = new THREE.Line(outline, outlineMat);
        contour.computeLineDistances();
        packet.add(contour);
        geometries.push(outline);
        materials.push(outlineMat);
        if (massless && !ghost) {
          const arrow = (offset: number, direction: number, tint: string) => {
            const from = new THREE.Vector3(offset, -direction * 1.05, 0.8);
            const a = new THREE.ArrowHelper(
              new THREE.Vector3(0, direction, 0),
              from,
              2.1,
              tint,
              0.17,
              0.12,
            );
            packet.add(a);
            geometries.push(a.line.geometry, a.cone.geometry);
            materials.push(
              a.line.material as THREE.Material,
              a.cone.material as THREE.Material,
            );
          };
          arrow(0.28, 1, '#f5f7fa');
          arrow(-0.28, hand, '#f5b391');
        }
      });
    } else if (particle.kind === 'higgs') {
      const packet = new THREE.Group();
      group.add(packet);
      packets.push(packet);
      for (let shell = 0; shell < 3; shell++) {
        const geo = new THREE.IcosahedronGeometry(0.53 + shell * 0.25, 3);
        const mat = new THREE.MeshStandardMaterial({
          color: colour,
          emissive: colour,
          emissiveIntensity: 0.15,
          roughness: 0.32,
          metalness: 0.2,
          transparent: true,
          opacity: shell === 0 ? 0.8 : 0.1,
          wireframe: shell > 0,
          depthWrite: shell === 0,
        });
        const sphere = new THREE.Mesh(geo, mat);
        packet.add(sphere);
        geometries.push(geo);
        materials.push(mat);
      }
    } else {
      const packet = new THREE.Group();
      group.add(packet);
      packets.push(packet);
      const channels = particle.id === 'gluon' ? 3 : 2;
      for (let i = 0; i < channels; i++) {
        const tint =
          channels === 3 ? ['#8fc9ff', '#f4b194', '#91d5b6'][i] : colour;
        const { mesh, curve } = tube(
          transverseWave((i * Math.PI) / 2),
          tint,
          0.035,
          0.85,
        );
        const layer = new THREE.Group();
        layer.rotation.x = (i * Math.PI) / channels;
        layer.add(mesh);
        packet.add(layer);
        addMote(layer, curve, '#e7fff4', i / channels);
      }
    }
    const bridge = new THREE.Group();
    group.add(bridge);
    const bridgeMaterials: THREE.MeshStandardMaterial[] = [];
    for (let j = 0; j < 3; j++) {
      const coords: [number, number, number][] = Array.from(
        { length: 61 },
        (_, i) => {
          const u = i / 60;
          return [
            (u - 0.5) * 2.1,
            Math.sin(u * Math.PI * 2) * 0.12 + (j - 1) * 0.11,
            0.05,
          ];
        },
      );
      const { mesh, curve } = tube(coords, '#ffdc92', 0.023, 0);
      bridge.add(mesh);
      bridgeMaterials.push(mesh.material);
      addMote(bridge, curve, '#ffe6a8', j / 3);
    }
    let disposed = false,
      dragging = false,
      holdUntil = 0;
    const draw = () => {
      if (!disposed && !document.hidden) renderer.render(scene, camera);
    };
    const update = (value: number) => {
      bridge.visible = fermion && particle.kind !== 'neutrino' && value > 0;
      bridgeMaterials.forEach((m) => {
        m.opacity = value * 0.88;
      });
      bridge.scale.y = 0.6 + value * 1.8;
      bridge.scale.z = 0.6 + value;
      draw();
    };
    const resize = () => {
      const w = element.clientWidth,
        h = element.clientHeight;
      if (!w || !h) return;
      renderer.setSize(w, h, false);
      camera.aspect = w / h;
      camera.position.z = w / h < 1.05 ? 8.5 : 7.8;
      camera.updateProjectionMatrix();
      draw();
    };
    const observer = new ResizeObserver(resize);
    observer.observe(element);
    const start = () => {
      dragging = true;
    };
    const end = () => {
      dragging = false;
      holdUntil = performance.now() + 3500;
    };
    orbit.addEventListener('start', start);
    orbit.addEventListener('end', end);
    orbit.addEventListener('change', draw);
    controlsRef.current = {
      update,
      turn: () => {
        group.rotation.y = group.rotation.y > 0.2 ? -0.32 : 0.32;
        holdUntil = performance.now() + 3500;
        draw();
      },
      tick: (t) => {
        if (!dragging && performance.now() > holdUntil) {
          group.rotation.y +=
            (Math.sin(t * 0.13) * 0.16 - group.rotation.y) * 0.035;
          group.rotation.x = Math.sin(t * 0.11) * 0.07;
        }
        packets.forEach((p, i) => {
          p.rotation.y = fermion
            ? Math.sin(t * 0.25) * 0.3 * (i ? 1 : -1)
            : t * 0.035;
          if (particle.kind === 'higgs')
            p.scale.setScalar(1 + Math.sin(t * 0.7) * 0.035);
        });
        travellers.forEach(({ mesh, curve, phase }) =>
          mesh.position.copy(curve.getPointAt((t * 0.09 + phase) % 1)),
        );
        draw();
      },
    };
    resize();
    update(latest.current);
    return () => {
      disposed = true;
      controlsRef.current = null;
      observer.disconnect();
      orbit.removeEventListener('start', start);
      orbit.removeEventListener('end', end);
      orbit.removeEventListener('change', draw);
      orbit.dispose();
      [...new Set(geometries)].forEach((g) => g.dispose());
      [...new Set(materials)].forEach((m) => m.dispose());
      renderer.dispose();
      renderer.forceContextLoss();
      renderer.domElement.remove();
    };
  }, [particle.id, particle.kind, particle.name, massless, vectorlike]);
  const fermion = particle.kind !== 'boson' && particle.kind !== 'higgs';
  return (
    <div className="particle-scene">
      <div className="particle-canvas" ref={host} />
      {failed && (
        <p className="particle-fallback">
          3D is unavailable here. All field properties and calculations remain
          in the text below.
        </p>
      )}
      <div className="particle-field-labels" key={particle.id}>
        {fermion ? (
          <>
            <div>
              <strong>
                {particle.symbol}
                <sub>L</sub>
              </strong>
              <span>{vectorlike ? 'ELECTRIC CHARGE −1' : 'WEAK DOUBLET'}</span>
            </div>
            <div>
              <strong>
                {particle.symbol}
                <sub>R</sub>
              </strong>
              <span>
                {particle.kind === 'neutrino'
                  ? 'NOT IN THE MINIMAL MODEL'
                  : vectorlike
                    ? 'ELECTRIC CHARGE −1'
                    : 'WEAK SINGLET'}
              </span>
            </div>
          </>
        ) : (
          <div>
            <strong>{particle.symbol}</strong>
            <span>SPIN {particle.spin}</span>
          </div>
        )}
      </div>
      <Button
        variant="ghost"
        className="particle-turn"
        onClick={() => controlsRef.current?.turn()}
      >
        Turn the field view ↻
      </Button>
      <p className="instrument-note">
        {massless
          ? 'Massless particle limit: white = momentum, copper = spin. Opposed for L, aligned for R. For antiparticles the chirality/helicity relation reverses.'
          : 'Wave ribbons distinguish field components; their shapes and motion are illustrative, not particle trajectories or classical spin. Drag to change the view.'}
      </p>
    </div>
  );
}
