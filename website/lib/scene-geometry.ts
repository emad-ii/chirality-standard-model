/** Symbolic wave packets for teaching, not solutions for a particle's spatial shape. */
export function chiralPacket(
  hand: -1 | 1,
  phase = 0,
  samples = 120,
): [number, number, number][] {
  if (!Number.isFinite(phase) || !Number.isInteger(samples) || samples < 8)
    throw new Error('Invalid packet sampling');
  return Array.from({ length: samples + 1 }, (_, i) => {
    const u = i / samples;
    const envelope = Math.sin(Math.PI * u) * 0.6;
    const angle = 4 * Math.PI * u + phase;
    return [
      envelope * Math.cos(angle),
      (u - 0.5) * 2.5,
      hand * envelope * Math.sin(angle),
    ];
  });
}
export function transverseWave(
  phase = 0,
  samples = 120,
): [number, number, number][] {
  if (!Number.isFinite(phase) || !Number.isInteger(samples) || samples < 8)
    throw new Error('Invalid wave sampling');
  return Array.from({ length: samples + 1 }, (_, i) => {
    const u = i / samples;
    return [
      (u - 0.5) * 3.5,
      Math.sin(4 * Math.PI * u + phase) * Math.sin(Math.PI * u) * 0.58,
      0,
    ];
  });
}
