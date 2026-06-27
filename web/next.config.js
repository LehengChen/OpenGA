/** @type {import('next').NextConfig} */
const nextConfig = {
  // Full Next.js server (SSR + /api Route Handlers), deployed on Vercel.
  // (Was `output: "export"` for the old static/Tauri build.)
  images: {
    unoptimized: true,
  },
  // Bundle the project data (copied to web/projects by the prebuild step) into
  // the /api serverless functions so they can read the store at runtime.
  outputFileTracingIncludes: {
    "/api/**/*": ["./projects/**/*"],
  },
  // Enable SharedArrayBuffer in dev mode (requires cross-origin isolation)
  async headers() {
    return [
      {
        source: "/(.*)",
        headers: [
          { key: "Cross-Origin-Opener-Policy", value: "same-origin" },
          { key: "Cross-Origin-Embedder-Policy", value: "require-corp" },
        ],
      },
    ];
  },
  // Suppress file watcher errors in dev mode
  webpack: (config, { dev }) => {
    if (dev) {
      config.watchOptions = {
        ...config.watchOptions,
        ignored: /node_modules/,
        poll: 1000,
        aggregateTimeout: 300,
      };
    }
    return config;
  },
};

module.exports = nextConfig;
