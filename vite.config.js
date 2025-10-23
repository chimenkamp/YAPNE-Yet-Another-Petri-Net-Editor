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
    }
  },
  define: { 
    global: 'globalThis',
    'process.env': {},
  },
  optimizeDeps: {
    include: ['z3-solver', 'mathjs'],
    esbuildOptions: {
      define: {
        global: 'globalThis'
      },
      plugins: []
    }
  },
  resolve: {
    alias: {
      util: 'rollup-plugin-node-polyfills/polyfills/util',
      buffer: 'rollup-plugin-node-polyfills/polyfills/buffer-es6'
    }
  },
  plugins: [
    nodePolyfills({
      include: ['util', 'buffer', 'process', 'path'],
      globals: {
        Buffer: true,
        global: true,
        process: true,
      },
      protocolImports: true,
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