/**
 * Class to parse and solve expressions involving "primed" (new) and unprimed (old) variable values.
 * Given an object of existing variable values, it evaluates constraints on primed variables,
 * determines integer bounds, and returns a random integer within those bounds.
 */
class ExpressionSolver {
  /**
   * @param {Record<string, number>} oldValues
   *   An object mapping variable names (unprimed) to their current numeric values.
   */
  constructor(oldValues) {
    this.oldValues = { ...oldValues };
    /** @type {Record<string, { min: number, max: number }>} */
    this.bounds = {};
  }

  /**
   * Evaluate a numeric expression string by substituting unprimed variable names
   * with their values from oldValues.
   *
   * @param {string} expr
   *   A string expression (e.g., "x + 5", "y * 2 - z", etc.).
   * @returns {number}
   *   The numeric result after substitution.
   * @throws {Error}
   *   If any referenced (unprimed) variable is not in oldValues, or if evaluation fails.
   */
  evaluateExpression(expr) {
    // Replace each variable name (word boundary) with its numeric value
    let replaced = expr.trim();
    for (const [varName, varValue] of Object.entries(this.oldValues)) {
      // Use word boundaries to avoid partial replacements
      const pattern = new RegExp(`\\b${varName}\\b`, "g");
      replaced = replaced.replace(pattern, String(varValue));
    }

    // After replacement, check if any letters remain (undefined variable)
    if (/[a-zA-Z]/.test(replaced)) {
      throw new Error(`Undefined variable in expression: "${expr}"`);
    }

    // Evaluate the numeric expression
    // eslint-disable-next-line no-eval
    const result = eval(replaced);
    if (typeof result !== "number" || Number.isNaN(result)) {
      throw new Error(`Failed to evaluate expression: "${expr}"`);
    }
    return result;
  }

  /**
   * Parse a set of semicolon-separated constraints on primed variables (e.g., "x' > x + 5; x' < x + 100;"),
   * compute integer bounds for each primed variable, and return a random integer satisfying all constraints.
   *
   * @param {string} constraintString
   *   A string containing one or more constraints, separated by semicolons. 
   *   Each constraint must be of the form:
   *     "<varName>' <operator> <expression>"
   *   where <operator> ∈ {<, <=, >, >=, ==}.
   *   Example: "x' > x + 5; x' < x + 100"
   *
   * @returns {Record<string, number>}
   *   An object mapping each primed variable (without the apostrophe) to its computed new integer value.
   *   The returned value is a random integer within the feasible range.
   *
   * @throws {Error}
   *   If a primed variable references an undefined base variable, if bounds are infinite, if constraints conflict, or if parsing fails.
   */
  solve(constraintString) {
    this.bounds = {};

    // Remove surrounding parentheses if present, then split on semicolons
    const trimmed = constraintString.trim().replace(/^\(+/, "").replace(/\)+$/, "");
    const clauses = trimmed
      .split(";")
      .map((c) => c.trim())
      .filter((c) => c.length > 0);

    for (const clause of clauses) {
      // Match patterns like: var' <expr> or var' <= expr, etc.
      const match = clause.match(/^([a-zA-Z_]\w*)'\s*(<=|<|>=|>|==)\s*(.+)$/);
      if (!match) {
        throw new Error(`Invalid constraint format: "${clause}"`);
      }

      const [, primedName, operator, rightExpr] = match;
      // Ensure the unprimed variable exists
      if (!(primedName in this.oldValues)) {
        throw new Error(`Variable "${primedName}" is not defined in the oldValues object.`);
      }

      // Evaluate the right-hand expression in terms of oldValues
      const rhsValue = this.evaluateExpression(rightExpr);

      // Initialize min/max if first time encountering this primed variable
      if (!(primedName in this.bounds)) {
        this.bounds[primedName] = { min: Number.NEGATIVE_INFINITY, max: Number.POSITIVE_INFINITY };
      }

      const b = this.bounds[primedName];
      // Adjust integer bounds based on operator
      switch (operator) {
        case "<":
          // primed < rhsValue  ⇒ max ≤ rhsValue - 1
          b.max = Math.min(b.max, Math.floor(rhsValue) - 1);
          break;
        case "<=":
          // primed ≤ rhsValue
          b.max = Math.min(b.max, Math.floor(rhsValue));
          break;
        case ">":
          // primed > rhsValue  ⇒ min ≥ rhsValue + 1
          b.min = Math.max(b.min, Math.ceil(rhsValue) + 1);
          break;
        case ">=":
          // primed ≥ rhsValue
          b.min = Math.max(b.min, Math.ceil(rhsValue));
          break;
        case "==":
          // primed == rhsValue
          const exact = Math.round(rhsValue);
          b.min = Math.max(b.min, exact);
          b.max = Math.min(b.max, exact);
          break;
        default:
          throw new Error(`Unsupported operator "${operator}" in clause: "${clause}"`);
      }

      // After updating, check for conflict
      if (b.min > b.max) {
        throw new Error(
          `No integer ${primedName}' can satisfy all constraints (min=${b.min}, max=${b.max}).`
        );
      }
    }

    // Build result: choose a random integer between min and max for each primed variable
    const result = {};
    for (const [varName, { min, max }] of Object.entries(this.bounds)) {
      if (!Number.isFinite(min) || !Number.isFinite(max)) {
        throw new Error(
          `Bounds for ${varName}' are not both finite (min=${min}, max=${max}).`
        );
      }
      const lower = Math.ceil(min);
      const upper = Math.floor(max);
      if (lower > upper) {
        throw new Error(
          `No integer ${varName}' in [${min}, ${max}] exists.`
        );
      }
      // Random integer in [lower, upper]
      const randomValue = Math.floor(Math.random() * (upper - lower + 1)) + lower;
      result[varName] = randomValue;
    }

    return result;
  }
}
