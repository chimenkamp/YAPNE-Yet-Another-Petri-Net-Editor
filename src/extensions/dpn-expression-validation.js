class ExpressionParser {
  constructor() {
    this.variables = new Set();
  }

  /**
   * Parse and evaluate the given expression with the provided variable values
   * @param {string} expression - The expression to evaluate
   * @param {Object} values - Object containing variable values
   * @returns {boolean} - Result of the evaluation
   */
  evaluate(expression, values) {
    const tokens = this.tokenize(expression);
    const ast = this.parse(tokens);
    return this.evaluateNode(ast, values);
  }

  /**
   * Tokenize the expression into tokens
   * @param {string} expression - The expression to tokenize
   * @returns {Array} - Array of tokens
   */
  tokenize(expression) {
    this.variables.clear();
    
    const tokens = [];
    let position = 0;
    
    const skipWhitespace = () => {
      while (position < expression.length && /\s/.test(expression[position])) {
        position++;
      }
    };
    
    while (position < expression.length) {
      skipWhitespace();
      
      if (position >= expression.length) break;
      
      const char = expression[position];
      
      if (/[0-9]/.test(char) || (char === '.' && /[0-9]/.test(expression[position + 1]))) {
        const start = position;
        
        if (char === '.') {
          position++;
        }
        
        while (
          position < expression.length && 
          (/[0-9]/.test(expression[position]) || 
           (expression[position] === '.' && !/\./.test(expression.substring(start, position))))
        ) {
          position++;
        }
        
        const value = parseFloat(expression.substring(start, position));
        tokens.push({ type: 'number', value });
        continue;
      }
      
      if (/[a-zA-Z_]/.test(char)) {
        const start = position;
        
        // Modified to allow apostrophes in variable names
        while (position < expression.length && /[a-zA-Z0-9_']/.test(expression[position])) {
          position++;
        }
        
        const name = expression.substring(start, position);
        
        if (name === 'true') {
          tokens.push({ type: 'boolean', value: true });
        } else if (name === 'false') {
          tokens.push({ type: 'boolean', value: false });
        } else {
          tokens.push({ type: 'variable', name });
          this.variables.add(name);
        }
        
        continue;
      }
      
      if (['=', '!', '>', '<'].includes(char)) {
        if (position + 1 < expression.length && expression[position + 1] === '=') {
          tokens.push({ type: 'operator', value: char + '=' });
          position += 2;
        } else {
          tokens.push({ type: 'operator', value: char });
          position++;
        }
        continue;
      }
      
      if (char === '&' || char === '|') {
        if (position + 1 < expression.length && expression[position + 1] === char) {
          tokens.push({ type: 'logical', value: char + char });
          position += 2;
        } else {
          throw new Error(`Unexpected character at position ${position}: ${char}`);
        }
        continue;
      }
      
      if (char === '(' || char === ')') {
        tokens.push({ type: 'paren', value: char });
        position++;
        continue;
      }
      
      throw new Error(`Unexpected character at position ${position}: ${char}`);
    }
    
    return tokens;
  }

  /**
   * Parse tokens into an Abstract Syntax Tree (AST)
   * @param {Array} tokens - Array of tokens
   * @returns {Object} - AST root node
   */
  parse(tokens) {
    let position = 0;
    
    const parseExpression = () => {
      return parseLogical();
    };
    
    const parseLogical = () => {
      let left = parseComparison();
      
      while (position < tokens.length && tokens[position].type === 'logical') {
        const operator = tokens[position].value;
        position++;
        
        const right = parseComparison();
        
        left = { 
          type: 'logical', 
          operator, 
          left, 
          right 
        };
      }
      
      return left;
    };
    
    const parseComparison = () => {
      let left = parsePrimary();
      
      if (position < tokens.length && tokens[position].type === 'operator') {
        const operator = tokens[position].value;
        position++;
        
        const right = parsePrimary();
        
        return { 
          type: 'comparison', 
          operator, 
          left, 
          right 
        };
      }
      
      return left;
    };
    
    const parsePrimary = () => {
      const token = tokens[position];
      
      if (token.type === 'variable') {
        position++;
        return { type: 'variable', name: token.name };
      }
      
      if (token.type === 'number') {
        position++;
        return { type: 'number', value: token.value };
      }
      
      if (token.type === 'boolean') {
        position++;
        return { type: 'boolean', value: token.value };
      }
      
      if (token.type === 'paren' && token.value === '(') {
        position++;
        const expr = parseExpression();
        
        if (position >= tokens.length || tokens[position].type !== 'paren' || tokens[position].value !== ')') {
          throw new Error('Expected closing parenthesis');
        }
        
        position++;
        return expr;
      }
      
      throw new Error(`Unexpected token at position ${position}: ${JSON.stringify(token)}`);
    };
    
    const ast = parseExpression();
    
    if (position < tokens.length) {
      throw new Error(`Unexpected tokens at end: ${JSON.stringify(tokens.slice(position))}`);
    }
    
    return ast;
  }

  /**
   * Evaluate an AST node with the given variable values
   * @param {Object} node - AST node
   * @param {Object} values - Object containing variable values
   * @returns {boolean|number} - Result of the evaluation
   */
  evaluateNode(node, values) {
    switch (node.type) {
      case 'number':
        return node.value;
        
      case 'boolean':
        return node.value;
        
      case 'variable':
        if (!(node.name in values)) {
          throw new Error(`Variable "${node.name}" is not defined in the provided values`);
        }
        return values[node.name];
        
      case 'comparison':
        const left = this.evaluateNode(node.left, values);
        const right = this.evaluateNode(node.right, values);
        
        switch (node.operator) {
          case '<': return left < right;
          case '>': return left > right;
          case '<=': return left <= right;
          case '>=': return left >= right;
          case '==': return left === right;
          case '!=': return left !== right;
          default:
            throw new Error(`Unknown comparison operator: ${node.operator}`);
        }
        
      case 'logical':
        if (node.operator === '&&') {
          return this.evaluateNode(node.left, values) && this.evaluateNode(node.right, values);
        } else if (node.operator === '||') {
          return this.evaluateNode(node.left, values) || this.evaluateNode(node.right, values);
        } else {
          throw new Error(`Unknown logical operator: ${node.operator}`);
        }
        
      default:
        throw new Error(`Unknown node type: ${node.type}`);
    }
  }

  /**
   * Get the bounds for a variable in the expression
   * @param {string} expression - The expression
   * @param {string} variable - The variable to find bounds for
   * @returns {Object} - Bounds for the variable
   */
  getVariableBounds(expression, variable) {
    const bounds = {
      min: -Infinity,
      max: Infinity,
      minInclusive: false,
      maxInclusive: false
    };
    
    try {
      const tokens = this.tokenize(expression);
      const ast = this.parse(tokens);
      
      this.extractBounds(ast, variable, bounds, true);
      
      return bounds;
    } catch (error) {
      console.error('Error determining bounds:', error);
      return bounds;
    }
  }
  
  /**
   * Extract bounds for a variable from an AST node
   * @param {Object} node - AST node
   * @param {string} variable - Variable name
   * @param {Object} bounds - Bounds object to update
   * @param {boolean} isPositive - Whether the condition is positive (not negated)
   */
  extractBounds(node, variable, bounds, isPositive = true) {
    if (!node) return;
    
    switch (node.type) {
      case 'comparison':
        const isVarOnLeft = node.left.type === 'variable' && node.left.name === variable;
        const isVarOnRight = node.right.type === 'variable' && node.right.name === variable;
        
        if (isVarOnLeft || isVarOnRight) {
          const otherSide = isVarOnLeft ? node.right : node.left;
          
          if (otherSide.type !== 'number') return;
          
          const value = otherSide.value;
          let operator = node.operator;
          
          if (isVarOnRight) {
            operator = this.invertOperator(operator);
          }
          
          this.updateBoundsFromComparison(bounds, operator, value, isPositive);
        }
        break;
        
      case 'logical':
        if (node.operator === '&&' && isPositive) {
          this.extractBounds(node.left, variable, bounds, isPositive);
          this.extractBounds(node.right, variable, bounds, isPositive);
        } else if (node.operator === '||' && isPositive) {
          const leftBounds = { min: -Infinity, max: Infinity, minInclusive: false, maxInclusive: false };
          const rightBounds = { min: -Infinity, max: Infinity, minInclusive: false, maxInclusive: false };
          
          this.extractBounds(node.left, variable, leftBounds, isPositive);
          this.extractBounds(node.right, variable, rightBounds, isPositive);
          
          bounds.min = Math.min(leftBounds.min, rightBounds.min);
          bounds.max = Math.max(leftBounds.max, rightBounds.max);
          bounds.minInclusive = leftBounds.min < rightBounds.min ? leftBounds.minInclusive : rightBounds.minInclusive;
          bounds.maxInclusive = leftBounds.max > rightBounds.max ? leftBounds.maxInclusive : rightBounds.maxInclusive;
        }
        break;
    }
  }
  
  /**
   * Update bounds based on a comparison
   * @param {Object} bounds - Bounds to update
   * @param {string} operator - Comparison operator
   * @param {number} value - Value in the comparison
   * @param {boolean} isPositive - Whether the condition is positive (not negated)
   */
  updateBoundsFromComparison(bounds, operator, value, isPositive) {
    switch (operator) {
      case '>':
        if (isPositive && (value > bounds.min || bounds.min === -Infinity)) {
          bounds.min = value;
          bounds.minInclusive = false;
        }
        break;
        
      case '>=':
        if (isPositive && (value > bounds.min || (value === bounds.min && !bounds.minInclusive) || bounds.min === -Infinity)) {
          bounds.min = value;
          bounds.minInclusive = true;
        }
        break;
        
      case '<':
        if (isPositive && (value < bounds.max || bounds.max === Infinity)) {
          bounds.max = value;
          bounds.maxInclusive = false;
        }
        break;
        
      case '<=':
        if (isPositive && (value < bounds.max || (value === bounds.max && !bounds.maxInclusive) || bounds.max === Infinity)) {
          bounds.max = value;
          bounds.maxInclusive = true;
        }
        break;
        
      case '==':
        if (isPositive) {
          bounds.min = value;
          bounds.max = value;
          bounds.minInclusive = true;
          bounds.maxInclusive = true;
        }
        break;
    }
  }

  /**
   * Invert a comparison operator
   * @param {string} operator - The operator to invert
   * @returns {string} - The inverted operator
   */
  invertOperator(operator) {
    switch (operator) {
      case '<': return '>';
      case '>': return '<';
      case '<=': return '>=';
      case '>=': return '<=';
      default: return operator; // == and != stay the same
    }
  }
  
  /**
   * Generate a random number that satisfies the expression for a specific variable
   * @param {string} expression - The expression to satisfy
   * @param {string} variable - The variable to generate a value for
   * @param {Object} fixedValues - Fixed values for other variables (optional)
   * @param {number} attempts - Maximum number of attempts
   * @returns {number|null} - A random valid number or null if not found
   */
  getRandomValidNumber(expression, variable, fixedValues = {}, attempts = 100) {
    if (!variable && this.variables.size > 0) {
      variable = Array.from(this.variables)[0];
    }
    
    if (this.variables.size === 0) {
      this.tokenize(expression);
    }
    
    if (!this.variables.has(variable)) {
      return null;
    }
    
    const bounds = this.getVariableBounds(expression, variable);
    
    if (bounds.min === bounds.max && bounds.minInclusive && bounds.maxInclusive) {
      return bounds.min;
    }
    
    const hasLowerBound = isFinite(bounds.min);
    const hasUpperBound = isFinite(bounds.max);
    
    if (hasLowerBound && hasUpperBound && bounds.min > bounds.max) {
      return null;
    }
    
    if (this.variables.size === 1) {
      if (!hasLowerBound && !hasUpperBound) {
        return Math.random() * 2000 - 1000;
      }
      
      const adjustedMin = hasLowerBound 
        ? (bounds.minInclusive ? bounds.min : bounds.min + Number.EPSILON) 
        : -1000;
      const adjustedMax = hasUpperBound 
        ? (bounds.maxInclusive ? bounds.max : bounds.max - Number.EPSILON) 
        : 1000;
      
      return Math.random() * (adjustedMax - adjustedMin) + adjustedMin;
    }
    
    for (let i = 0; i < attempts; i++) {
      const values = { ...fixedValues };
      
      for (const v of this.variables) {
        if (v !== variable && !(v in values)) {
          values[v] = Math.random() * 2000 - 1000;
        }
      }
      
      const adjustedMin = hasLowerBound 
        ? (bounds.minInclusive ? bounds.min : bounds.min + Number.EPSILON) 
        : -1000;
      const adjustedMax = hasUpperBound 
        ? (bounds.maxInclusive ? bounds.max : bounds.max - Number.EPSILON) 
        : 1000;
      
      values[variable] = Math.random() * (adjustedMax - adjustedMin) + adjustedMin;
      
      if (this.evaluate(expression, values)) {
        return values[variable];
      }
    }
    
    return null;
  }
  
  /**
   * Generate random values for all variables in the expression
   * @param {string} expression - The expression to satisfy
   * @param {Object} fixedValues - Fixed values for some variables (optional)
   * @param {number} attempts - Maximum number of attempts
   * @returns {Object|null} - An object with random values or null if not found
   */
  generateRandomValidValues(expression, fixedValues = {}, attempts = 100) {
    if (this.variables.size === 0) {
      this.tokenize(expression);
    }
    
    if (this.variables.size === 0) {
      return {};
    }
    
    const allVarsFixed = Array.from(this.variables).every(v => v in fixedValues);
    if (allVarsFixed) {
      return this.evaluate(expression, fixedValues) ? fixedValues : null;
    }
    
    if (this.variables.size === 1) {
      const variable = Array.from(this.variables)[0];
      const value = this.getRandomValidNumber(expression, variable, fixedValues);
      
      if (value !== null) {
        return { ...fixedValues, [variable]: value };
      }
      
      return null;
    }
    
    for (let i = 0; i < attempts; i++) {
      const values = { ...fixedValues };
      
      for (const variable of this.variables) {
        if (!(variable in values)) {
          const bounds = this.getVariableBounds(expression, variable);
          
          const hasLowerBound = isFinite(bounds.min);
          const hasUpperBound = isFinite(bounds.max);
          
          const adjustedMin = hasLowerBound 
            ? (bounds.minInclusive ? bounds.min : bounds.min + Number.EPSILON) 
            : -1000;
          const adjustedMax = hasUpperBound 
            ? (bounds.maxInclusive ? bounds.max : bounds.max - Number.EPSILON) 
            : 1000;
          
          values[variable] = Math.random() * (adjustedMax - adjustedMin) + adjustedMin;
        }
      }
      
      if (this.evaluate(expression, values)) {
        return values;
      }
    }
    
    return null;
  }
  
  /**
   * Parse an expression and return its AST
   * @param {string} expression - The expression to parse
   * @returns {Object} - The AST for the expression
   */
  getAST(expression) {
    const tokens = this.tokenize(expression);
    return this.parse(tokens);
  }
  
  /**
   * Print the AST for debugging purposes
   * @param {string} expression - The expression to parse and print
   */
  printAST(expression) {
    try {
      const ast = this.getAST(expression);
      console.log(JSON.stringify(ast, null, 2));
    } catch (error) {
      console.error('Error parsing expression:', error);
    }
  }
}