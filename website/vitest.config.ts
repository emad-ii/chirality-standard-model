import { fileURLToPath } from 'node:url';
import react from '@vitejs/plugin-react';
import { defineConfig } from 'vitest/config';

// Component tests run in a simulated DOM, not a browser or GPU renderer.
export default defineConfig({
  plugins: [react()],
  resolve: { alias: { '@': fileURLToPath(new URL('.', import.meta.url)) } },
  test: {
    environment: 'jsdom',
    environmentOptions: {
      jsdom: { url: 'http://localhost/', pretendToBeVisual: true },
    },
    include: ['tests/**/*.test.tsx'],
    setupFiles: ['tests/setup.ts'],
    maxWorkers: 1,
    execArgv: ['--no-experimental-webstorage'],
    fileParallelism: false,
  },
});
