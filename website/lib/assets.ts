/** Local and GitHub project-page assets share one explicitly configured prefix. */
export function asset(path: string): string {
  return (process.env.NEXT_PUBLIC_BASE_PATH ?? '') + '/' + path.replace(/^\/+/, '');
}
