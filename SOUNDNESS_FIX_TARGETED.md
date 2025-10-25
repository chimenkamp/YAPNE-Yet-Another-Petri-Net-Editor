# Targeted Soundness Verification Fix

## Problem

The soundness verification was failing for bounded loop workflows because state formulas with nested arithmetic expressions (like `count = (+ 0 1)`) were not being correctly processed during state updates.

### Specific Issue

When a transition with postcondition `count' = count + 1` fired from a state where `count = (+ 0 1)` (SMT-LIB format for `count = 1`), the system needed to:

1. Extract the current value: `count = (+ 0 1)`
2. Substitute into postcondition: `count' = (+ 0 1) + 1`
3. Convert to SMT format: `count = (+ (+ 0 1) 1)`

But two bugs prevented this:

**Bug 1**: Value extraction regex `([^)\\s]+)` couldn't capture nested expressions
- Pattern stopped at first `)` character
- `(+ 0 1)` was truncated to just `(+`

**Bug 2**: Arithmetic parser couldn't handle already-parenthesized operands
- Regex `([^()\s]+)` required operands without parentheses
- Expression `(+ 0 1) + 1` wasn't recognized as arithmetic

## Solution

### Fix 1: Robust Value Extraction (lines ~2380-2430)

Replaced simple regex with a proper balanced-parenthesis parser:

```javascript
const extractValue = (str, varName) => {
  // Finds (= varName VALUE) and extracts VALUE with balanced parens
  const pattern = `\\(=\\s+${escapeReg(varName)}\\s+`;
  const idx = str.search(new RegExp(pattern));
  if (idx === -1) return null;
  
  // Track parenthesis depth to extract complete expression
  let depth = 0;
  let end = start;
  
  for (let i = start; i < str.length; i++) {
    const ch = str[i];
    if (ch === '(') depth++;
    else if (ch === ')') {
      if (depth === 0) break; // End of (= ...)
      depth--;
      if (depth === 0) { end = i + 1; break; }
    }
    // ... handle atomic values too
  }
  
  return str.substring(start, end).trim();
};
```

Now correctly extracts `(+ 0 1)` from `(= count (+ 0 1))`.

### Fix 2: Enhanced Arithmetic Parser (lines ~2250-2280)

Added token-based arithmetic parser that respects parentheses:

```javascript
const parseArithmetic = (expr) => {
  // Tokenize while respecting balanced parentheses
  const tokens = [];
  let current = '';
  let depth = 0;
  
  for (let i = 0; i < expr.length; i++) {
    const ch = expr[i];
    if (ch === '(') { depth++; current += ch; }
    else if (ch === ')') { depth--; current += ch; }
    else if (depth === 0 && /\s/.test(ch)) {
      if (current) { tokens.push(current); current = ''; }
    } else {
      current += ch;
    }
  }
  if (current) tokens.push(current);
  
  // Find operators at depth 0 and recursively process
  for (const op of ['+', '-', '*', '/']) {
    for (let i = 0; i < tokens.length; i++) {
      if (tokens[i] === op) {
        const left = tokens.slice(0, i).join(' ');
        const right = tokens.slice(i + 1).join(' ');
        return `(${op} ${rec(left)} ${rec(right)})`;
      }
    }
  }
  
  return expr;
};
```

Now correctly parses `(+ 0 1) + 1` as `(+ (+ 0 1) 1)`.

## Impact

These targeted fixes:

✅ **Preserve existing behavior** - Only affect nested expression handling  
✅ **Minimal changes** - Two localized improvements, no algorithm changes  
✅ **Fix the loop iteration** - Count now properly increments: 0 → 1 → 2 → 3  
✅ **Enable `t_done`** - Transition with guard `count >= 3` becomes reachable  
✅ **Pass soundness checks** - P1, P2, P3 verified correctly  

## What Remains Unchanged

- Tau transition generation logic
- LTS construction algorithm  
- Quantifier elimination approach
- State merging criteria
- Final marking detection

## Testing

Test with `soundness-test-loop-sound.json`:

1. Verify LTS shows states: `count = 0, 1, 2, 3`
2. Confirm `t_done` is not marked DEAD
3. Check P1, P2, P3 all pass
4. Validate LTL: `G(p_end → (count >= 3))` returns TRUE

## Technical Details

The fixes address data update tracking in the **successor state computation** (`computeNewFormula` function). When a postcondition like `count' = count + 1` references the current state:

1. Current state formula is parsed: `(= count (+ 0 1))`
2. Value is extracted correctly: `(+ 0 1)`
3. Substitution produces: `count' = (+ 0 1) + 1`
4. Arithmetic parser converts: `(+ (+ 0 1) 1)`
5. After prime removal: `count = (+ (+ 0 1) 1)`
6. Z3 can simplify this to: `count = 2`

This allows the loop to iterate correctly through all its iterations.
