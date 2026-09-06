export type Vector3 = [number, number, number];
export const initialVector: Vector3 = [
  1 / Math.sqrt(3),
  1 / Math.sqrt(3),
  1 / Math.sqrt(3),
];
export const radians = (degrees: number) => {
  if (!Number.isFinite(degrees))
    throw new RangeError('A finite angle is required.');
  return (degrees * Math.PI) / 180;
};
export function nextDemoAngle(angle: number, step: number, limit: number) {
  if (
    ![angle, step, limit].every(Number.isFinite) ||
    angle < 0 ||
    angle > limit ||
    step <= 0 ||
    limit <= 0
  )
    throw new RangeError(
      'An in-range angle and positive finite step and limit are required.',
    );
  return angle >= limit ? 0 : Math.min(limit, angle + step);
}
export function rotateX([x, y, z]: Vector3, a: number): Vector3 {
  const c = Math.cos(a),
    s = Math.sin(a);
  return [x, c * y - s * z, s * y + c * z];
}
export function rotateZ([x, y, z]: Vector3, a: number): Vector3 {
  const c = Math.cos(a),
    s = Math.sin(a);
  return [c * x - s * y, s * x + c * y, z];
}
export function orderedRotation(
  v: Vector3,
  degrees: number,
  order: 'xz' | 'zx',
): Vector3 {
  const a = radians(degrees);
  return order === 'xz' ? rotateZ(rotateX(v, a), a) : rotateX(rotateZ(v, a), a);
}
export function rotationSeparation(degrees: number) {
  const a = orderedRotation(initialVector, degrees, 'xz');
  const b = orderedRotation(initialVector, degrees, 'zx');
  return Math.hypot(...a.map((v, i) => v - b[i]));
}
export function phaseVector(degrees: number, charge: number): [number, number] {
  if (!Number.isInteger(charge))
    throw new RangeError('Integer U(1) charge required.');
  const a = radians(degrees) * charge;
  return [Math.cos(a), Math.sin(a)];
}
export function weakDoublet(degrees: number): [number, number] {
  const a = radians(degrees) / 2;
  // exp(-i θ σ_y / 2) acting on (1,0): a real slice of a complex doublet.
  return [Math.cos(a), Math.sin(a)];
}
export function leptonCharge(t3: number) {
  return t3 - 0.5;
}
