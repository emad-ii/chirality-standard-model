export function motionAllowed(
  paused: boolean,
  reduced: boolean,
  foreground: boolean,
  visible = true,
) {
  return !paused && !reduced && foreground && visible;
}
export function nextHiggsFrame(
  value: number,
  direction: number,
): { value: number; direction: number } {
  const nextDirection = value >= 100 ? -1 : value <= 0 ? 1 : direction;
  return {
    value: Math.max(0, Math.min(100, value + nextDirection * 10)),
    direction: nextDirection,
  };
}
