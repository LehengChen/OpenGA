import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';

// Static (Pages) build: `VITE_STATIC=1` switches the app to read pre-rendered
// JSON, and `PAGES_BASE` sets the repo subpath the site is served from.
const isStatic = Boolean(process.env.VITE_STATIC);
const base = isStatic ? process.env.PAGES_BASE ?? '/OpenGA/' : '/';

export default defineConfig({
  root: 'src',
  base,
  define: {
    'import.meta.env.VITE_STATIC': JSON.stringify(isStatic ? '1' : '')
  },
  plugins: [react()],
  optimizeDeps: {
    include: [
      'react',
      'react-dom/client',
      'react-router-dom',
      'react-markdown',
      'rehype-katex',
      'remark-math',
      'katex'
    ]
  },
  build: {
    outDir: '../dist',
    emptyOutDir: true
  },
  server: {
    port: 5173,
    headers: {
      'Cache-Control': 'no-store'
    },
    proxy: {
      '^/api/': {
        target: 'http://localhost:3001',
        changeOrigin: true
      }
    }
  },
  preview: {
    port: 4173
  }
});
