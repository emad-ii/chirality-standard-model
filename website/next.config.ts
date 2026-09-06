import type { NextConfig } from 'next';

const nextConfig: NextConfig = {
  output: 'export',
  basePath: process.env.GITHUB_PAGES === 'true' ? '/chirality-standard-model' : '',
  trailingSlash: true,
};

export default nextConfig;
