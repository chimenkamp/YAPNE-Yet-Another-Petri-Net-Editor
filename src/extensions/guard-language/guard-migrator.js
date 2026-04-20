/**
 * Guard Language Migrator
 * Converts old JavaScript-style guard expressions to the new guard language syntax.
 * Applied automatically when loading DPN JSON files with legacy expressions.
 */

/**
 * Migrate a precondition expression from old JavaScript syntax to the new guard language.
 *
 * Conversions:
 * - `===` → `=`
 * - `==` → `=`
 * - `!==` → `distinct`  (but != is also accepted by lexer)
 * - `&&` → `and`
 * - `||` → `or`
 * - `!expr` → `not expr`
 * - `%` → removed (not in grammar) — will cause a parse error if present
 * - String literals in comparisons → integer codes (logged as warning)
 *
 * @param {string} expression - Legacy precondition expression
 * @returns {string} Migrated expression
 */
export function migratePrecondition(expression) {
  if (!expression || !expression.trim()) return '';
  return migrateExpression(expression);
}

/**
 * Migrate a postcondition expression from old JavaScript syntax to the new guard language.
 *
 * Additional conversions for postconditions:
 * - `;` separators → `and` conjunction
 * - Remove trailing semicolons
 *
 * @param {string} expression - Legacy postcondition expression
 * @returns {string} Migrated expression
 */
export function migratePostcondition(expression) {
  if (!expression || !expression.trim()) return '';

  // Split on semicolons, filter empty parts, migrate each, join with 'and'
  const parts = expression.split(';')
    .map(s => s.trim())
    .filter(s => s.length > 0)
    .map(s => migrateExpression(s));

  if (parts.length === 0) return '';
  if (parts.length === 1) return parts[0];
  return parts.join(' and ');
}

/**
 * Core migration: convert a single expression fragment.
 */
function migrateExpression(expr) {
  let s = expr.trim();

  // Replace === with = (must come before == replacement)
  s = s.replace(/===/g, '=');
  // Replace == with =
  s = s.replace(/==/g, '=');
  // Replace !== with distinct (must come before != replacement)
  s = s.replace(/!==/g, 'distinct');

  // Replace && with and (word-boundary safe)
  s = s.replace(/&&/g, ' and ');
  // Replace || with or
  s = s.replace(/\|\|/g, ' or ');

  // Replace prefix ! (not followed by =) with not
  s = s.replace(/!\s*(?!=)/g, 'not ');

  // Replace string literals with a warning comment
  // "string" or 'string' → warn but keep as-is (will fail validation)
  // Common pattern: status === "ready" → status = "ready"
  // The user will need to manually convert string values to integer codes

  // Clean up double spaces
  s = s.replace(/\s{2,}/g, ' ').trim();

  return s;
}

/**
 * Check if an expression appears to use legacy JavaScript syntax.
 *
 * @param {string} expression
 * @returns {boolean} True if the expression contains legacy syntax markers
 */
export function isLegacySyntax(expression) {
  if (!expression || !expression.trim()) return false;
  const s = expression.trim();
  return /===|!==|&&|\|\||[^!]==[^>]/.test(s) ||  // JS operators
         /;\s*\S/.test(s) ||                       // semicolons as separators
         /%/.test(s) ||                             // modulo operator
         /"[^"]*"|'[^']*'/.test(s);                // string literals
}

/**
 * Migrate a full DPN configuration's transitions in-place.
 * Converts all preconditions and postconditions to the new syntax.
 *
 * @param {Object} dpnConfig - DPN configuration object with a transitions array
 * @returns {{ migratedCount: number, warnings: string[] }}
 */
export function migrateDpnConfig(dpnConfig) {
  let migratedCount = 0;
  const warnings = [];

  if (!dpnConfig || !dpnConfig.transitions) {
    return { migratedCount, warnings };
  }

  for (const transition of dpnConfig.transitions) {
    if (transition.precondition && isLegacySyntax(transition.precondition)) {
      const original = transition.precondition;
      transition.precondition = migratePrecondition(original);
      migratedCount++;

      // Check for string literals that couldn't be auto-migrated
      if (/"[^"]*"|'[^']*'/.test(transition.precondition)) {
        warnings.push(
          `Transition '${transition.label || transition.id}': precondition contains string literals ` +
          `that should be converted to integer codes: ${transition.precondition}`
        );
      }
    }

    if (transition.postcondition && isLegacySyntax(transition.postcondition)) {
      const original = transition.postcondition;
      transition.postcondition = migratePostcondition(original);
      migratedCount++;

      if (/"[^"]*"|'[^']*'/.test(transition.postcondition)) {
        warnings.push(
          `Transition '${transition.label || transition.id}': postcondition contains string literals ` +
          `that should be converted to integer codes: ${transition.postcondition}`
        );
      }
    }
  }

  // Migrate data variable types
  if (dpnConfig.dataVariables) {
    for (const dv of dpnConfig.dataVariables) {
      if (dv.type === 'float' || dv.type === 'number') {
        dv.type = dv.type === 'float' ? 'real' : 'int';
        migratedCount++;
      }
      if (dv.type === 'string') {
        warnings.push(
          `Variable '${dv.name}': type 'string' is not supported in the new guard language. ` +
          `Please convert to integer codes.`
        );
      }
    }
  }

  return { migratedCount, warnings };
}
