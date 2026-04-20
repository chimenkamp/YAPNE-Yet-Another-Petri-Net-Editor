#!/usr/bin/env node
/**
 * One-time migration script: update example JSON files from legacy JS guard syntax
 * to the new guard language syntax.
 * 
 * Usage: node scripts/migrate-examples.mjs
 */

import { readFileSync, writeFileSync, readdirSync } from 'fs';
import { join } from 'path';

const EXAMPLES_DIR = new URL('../public/examples', import.meta.url).pathname;

// --- Simple text-level migration (same logic as guard-migrator.js) ---

function migrateExpr(expr, isPost) {
  if (!expr || typeof expr !== 'string') return expr;
  let s = expr.trim();
  if (!s) return s;

  // Replace JS operators
  s = s.replace(/===/g, '=');
  s = s.replace(/!==/g, 'distinct');
  s = s.replace(/!=/g, 'distinct');
  s = s.replace(/==/g, '=');
  s = s.replace(/&&/g, 'and');
  s = s.replace(/\|\|/g, 'or');

  if (isPost) {
    // Replace semicolons with 'and', handling trailing ones
    // Remove trailing semicolons first
    s = s.replace(/;\s*$/, '');
    // Replace remaining semicolons with 'and'
    s = s.replace(/\s*;\s*/g, ' and ');
  }

  return s.trim();
}

function normalizeType(type) {
  const t = (type || 'real').toLowerCase().trim();
  switch (t) {
    case 'int': case 'integer': return 'int';
    case 'bool': case 'boolean': return 'bool';
    case 'real': case 'float': case 'number': case 'string': return 'real';
    default: return 'real';
  }
}

// --- Process all JSON files ---

const files = readdirSync(EXAMPLES_DIR).filter(f => f.endsWith('.json'));
let totalChanges = 0;

for (const file of files) {
  const filePath = join(EXAMPLES_DIR, file);
  let content;
  try {
    content = JSON.parse(readFileSync(filePath, 'utf-8'));
  } catch (e) {
    console.warn(`  Skipping ${file}: ${e.message}`);
    continue;
  }

  let changed = false;

  // Process transitions
  const transitions = content.transitions || [];
  for (const t of transitions) {
    if (t.precondition) {
      const migrated = migrateExpr(t.precondition, false);
      if (migrated !== t.precondition) {
        console.log(`  ${file}: ${t.label || t.id} pre: "${t.precondition}" → "${migrated}"`);
        t.precondition = migrated;
        changed = true;
      }
    }
    if (t.postcondition) {
      const migrated = migrateExpr(t.postcondition, true);
      if (migrated !== t.postcondition) {
        console.log(`  ${file}: ${t.label || t.id} post: "${t.postcondition}" → "${migrated}"`);
        t.postcondition = migrated;
        changed = true;
      }
    }
  }

  // Process data variables
  const dataVars = content.dataVariables || [];
  for (const v of dataVars) {
    if (v.type) {
      const norm = normalizeType(v.type);
      if (norm !== v.type) {
        console.log(`  ${file}: var ${v.name}: type "${v.type}" → "${norm}"`);
        v.type = norm;
        changed = true;
      }
    }
  }

  // Process final marking constraints
  if (content.finalMarkingConstraints) {
    for (const c of content.finalMarkingConstraints) {
      if (c.expression) {
        const migrated = migrateExpr(c.expression, false);
        if (migrated !== c.expression) {
          console.log(`  ${file}: final marking: "${c.expression}" → "${migrated}"`);
          c.expression = migrated;
          changed = true;
        }
      }
    }
  }

  if (changed) {
    writeFileSync(filePath, JSON.stringify(content, null, 2) + '\n', 'utf-8');
    totalChanges++;
    console.log(`  ✓ Updated ${file}`);
  }
}

console.log(`\nDone. ${totalChanges} file(s) updated out of ${files.length} total.`);
