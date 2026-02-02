import { defineConfig } from 'vite';
import topLevelAwait from 'vite-plugin-top-level-await';
import { viteStaticCopy } from 'vite-plugin-static-copy';
import nodePolyfills from 'rollup-plugin-polyfill-node';
import crossOriginIsolation from 'vite-plugin-cross-origin-isolation'
 
export default defineConfig({
  base: '/YAPNE-Yet-Another-Petri-Net-Editor',
  build: {
    target: 'esnext',
    commonjsOptions: {
      transformMixedEsModules: true,
      include: [/z3-solver/, /node_modules/]
    },
    rollupOptions: {
      plugins: [
        nodePolyfills()
      ]
    }
  },
  define: { 
    global: 'globalThis',
    'process.env': {},
  },
  optimizeDeps: {
    include: ['z3-solver', 'mathjs'],
    exclude: ['webppl'],
    esbuildOptions: {
      define: {
        global: 'globalThis'
      },
      plugins: []
    }
  },
  resolve: {
    alias: {
      // Node polyfills handled by rollup-plugin-polyfill-node
    }
  },
  plugins: [
    nodePolyfills({
      include: ['util', 'buffer', 'process', 'path', 'stream', 'events', 'assert'],
      globals: {
        Buffer: true,
        global: true,
        process: true,
      },
    }),
    topLevelAwait(),
    crossOriginIsolation(),
    viteStaticCopy({
      targets: [
        {
          src: 'node_modules/z3-solver/build/browser.js',
          dest: 'z3-solver'
        },
        {
          src: 'node_modules/z3-solver/build/high-level',
          dest: 'z3-solver'
        },
        {
          src: 'node_modules/z3-solver/build/low-level',
          dest: 'z3-solver'
        }
      ]
    }),
  ],

});