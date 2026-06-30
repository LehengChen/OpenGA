import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';

export default defineConfig({
  root: 'src',
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
