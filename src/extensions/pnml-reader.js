import { DataPetriNet, DataVariable } from './dpn-model.js';
import { parse, NodeType, callNode, varNode, toGuardString, quoteGuardIdentifier } from './guard-language/guard-parser.js';
import { getVariableReferences } from './guard-language/guard-evaluator.js';
import { migratePrecondition, migratePostcondition } from './guard-language/guard-migrator.js';

const TYPE_ALIASES = new Map([
  ['int', 'int'], ['integer', 'int'], ['java.lang.integer', 'int'], ['java.lang.long', 'int'],
  ['real', 'real'], ['number', 'real'], ['float', 'real'], ['double', 'real'], ['java.lang.double', 'real'],
  ['bool', 'bool'], ['boolean', 'bool'], ['java.lang.boolean', 'bool'], ['data', 'data']
]);

/** Return direct XML children, independent of namespace prefixes. */
function children(element, name) {
  return [...element.children].filter(child => child.localName === name);
}

/** Return matching descendants, independent of namespace prefixes. */
function descendants(element, name) {
  return [...element.getElementsByTagName('*')].filter(child => child.localName === name);
}

/** Read one direct XML child without borrowing a nested element's metadata. */
function text(element, name) {
  return children(element, name)[0]?.textContent.trim() ?? '';
}

/** Read a nonnegative integer without truncating malformed PNML numbers. */
function count(value, label, fallback = 0) {
  if (value === '') return fallback;
  const number = Number(value);
  if (!Number.isSafeInteger(number) || number < 0) throw new Error(`${label} must be a nonnegative safe integer.`);
  return number;
}

/** Read optional graphics coordinates. */
function position(element) {
  const coordinates = descendants(element, 'position')[0];
  if (!coordinates) return null;
  const x = Number(coordinates.getAttribute('x'));
  const y = Number(coordinates.getAttribute('y'));
  if (!Number.isFinite(x) || !Number.isFinite(y)) throw new Error('Invalid PNML coordinates.');
  return { x, y };
}

/** Parse PNML into a reviewable model without inventing data or executing guards. */
export function readPNML(xmlContent) {
  const document = new DOMParser().parseFromString(xmlContent, 'text/xml');
  if (descendants(document, 'parsererror').length) throw new Error('Invalid PNML XML.');
  const nets = descendants(document, 'net');
  if (nets.length !== 1) throw new Error('Select a PNML document containing exactly one net.');
  const net = nets[0];
  const saved = children(net, 'toolspecific').find(tool => tool.getAttribute('tool') === 'YAPNE' && text(tool, 'model-json'));
  if (saved) return restoreYapneModel(text(saved, 'model-json'));
  const tools = descendants(net, 'toolspecific').filter(tool => tool.getAttribute('tool') === 'dpn-discovery');
  const hasContracts = tools.some(tool => children(tool, 'contract').length);
  const parsed = readStructure(net);
  parsed.dataVariables = readVariables(net, hasContracts);
  const names = variableNames(parsed.dataVariables);
  parsed.transitions = descendants(net, 'transition').map(element => readTransition(element, names));
  completeVariables(parsed, hasContracts);
  parsed.finalMarkings = readFinalMarkings(net, parsed.places);
  if (tools.length) parsed.discoveryMetadata = { sourceTool: 'dpn-discovery', formatVersion: hasContracts ? '2.0' : '1.0' };
  validateStructure(parsed);
  return parsed;
}

/** Restore YAPNE's complete serialized model, including absent initial values. */
function restoreYapneModel(json) {
  const saved = parseNumericJSON(json);
  validateStructure(saved);
  validateSavedNumericVariables(saved.dataVariables || []);
  const model = DataPetriNet.fromJSON(json);
  const parsed = JSON.parse(model.toJSON());
  parsed.transitions = [...model.transitions.values()].map(transition => ({ ...transition, isDataAware: true }));
  parsed.dataVariables = [...model.dataVariables.values()].map(variable => ({ ...variable, requiresInitialValue: false }));
  validateStructure(parsed);
  return parsed;
}

/** Check numeric strings before the model can coerce them into rounded numbers. */
function validateSavedNumericVariables(variables) {
  for (const variable of variables) {
    const type = DataVariable.normalizeType(variable.type);
    if (type !== 'int' && type !== 'real') continue;
    for (const field of ['initialValue', 'currentValue']) {
      const value = variable[field];
      if (value === undefined || value === null) continue;
      if (typeof value !== 'number' && typeof value !== 'string') {
        throw new Error(`Variable ${variable.name}: ${field} must be numeric.`);
      }
      parseInitialValue(String(value), type);
    }
  }
}

/** Read the control-flow structure; marking references are not place definitions. */
function readStructure(net) {
  return {
    id: net.getAttribute('id') || crypto.randomUUID(),
    name: text(net, 'name') || 'Imported Net', description: text(net, 'description'),
    places: descendants(net, 'place').filter(element => element.hasAttribute('id')).map(readPlace),
    transitions: [], arcs: descendants(net, 'arc').map(readArc), dataVariables: []
  };
}

/** Read one place and its optional final marking. */
function readPlace(element) {
  const final = text(element, 'finalMarking');
  const capacity = text(element, 'capacity');
  return {
    id: element.getAttribute('id'), label: text(element, 'name') || element.getAttribute('id'),
    tokens: count(text(element, 'initialMarking'), 'Initial marking'), position: position(element),
    capacity: capacity === '' ? null : count(capacity, 'Capacity'),
    finalMarking: final === '' ? null : count(final, 'Final marking')
  };
}

/** Read one arc with its endpoints and weight. */
function readArc(element) {
  const weight = count(text(element, 'inscription'), 'Arc weight', 1);
  if (weight === 0) throw new Error('Arc weights must be positive.');
  return { id: element.getAttribute('id') || crypto.randomUUID(), source: element.getAttribute('source'),
    target: element.getAttribute('target'), weight, type: text(element, 'arctype') || 'regular', points: [], label: '' };
}

/** Extract declared variable names/types without supplying missing initial values. */
function readVariables(net, hasContracts) {
  const elements = descendants(net, 'variable');
  const usedNames = new Set(elements.map(element => element.getAttribute('name') || text(element, 'name')));
  return elements.map((element, index) => {
    const sourceName = element.getAttribute('name') || text(element, 'name');
    if (!sourceName) throw new Error('A PNML variable has no name.');
    let name = sourceName;
    if (/[|\\]/.test(name)) {
      name = element.getAttribute('symbol') || `pnml_variable_${index}`;
      while (usedNames.has(name)) name += '_alias';
      usedNames.add(name);
    }
    const rawType = element.getAttribute('type')?.toLowerCase();
    const type = hasContracts ? 'data' : rawType ? TYPE_ALIASES.get(rawType) : 'real';
    if (!type) throw new Error(`Variable ${sourceName}: unsupported type ${rawType}. No numeric conversion was applied.`);
    const initial = text(element, 'initialValue');
    const currentValue = initial === '' ? undefined : parseInitialValue(initial, type);
    return { id: element.getAttribute('id') || `variable_${index}`, name, sourceName,
      symbol: element.getAttribute('symbol'), type, currentValue, initialValue: currentValue,
      description: text(element, 'description'), typeInferred: !rawType && !hasContracts,
      requiresInitialValue: !hasContracts && initial === '', origin: 'PNML declaration' };
  });
}

/** Validate a user-entered initial value for the selected variable type. */
export function parseInitialValue(value, type) {
  if (!value.trim()) throw new Error('An initial value is required.');
  if (type === 'bool') {
    if (!['true', 'false'].includes(value.trim())) throw new Error('Use true or false.');
    return value.trim() === 'true';
  }
  if (type === 'data') {
    const parsed = parseNumericJSON(value);
    if (!isDataValue(parsed)) throw new Error('Expected a finite number, Boolean, or string.');
    return parsed;
  }
  const parsed = validateImportedNumber(Number(value));
  if (type === 'int' && !Number.isSafeInteger(parsed)) throw new Error(`Expected a valid ${type} value.`);
  return parsed;
}

/**
 * Reject numeric data whose integral value cannot retain its identity in a Number.
 * JSON has no integer/real type distinction, so this also rejects integral decimal
 * and exponent values outside the safe range. Fractional data retains Number precision.
 * @param {number} value Parsed numeric data value.
 * @returns {number} Validated value without coercion.
 */
function validateImportedNumber(value) {
  if (!Number.isFinite(value)) throw new Error('PNML numeric data must be finite.');
  if (Number.isInteger(value) && !Number.isSafeInteger(value)) {
    throw new Error('PNML integer-valued data must be in the safe integer range -9007199254740991 to 9007199254740991; no rounded value was imported.');
  }
  return value;
}

/**
 * Validate every numeric JSON leaf before observed data or saved models are restored.
 * @param {string} value JSON text, with strings and Boolean values left unchanged.
 * @returns {*} Parsed JSON with supported numeric values.
 */
function parseNumericJSON(value) {
  return JSON.parse(value, (key, item) => typeof item === 'number' ? validateImportedNumber(item) : item);
}

/** Map explicit solver symbols and original names to executable names. */
function variableNames(variables) {
  const originals = new Map();
  const symbols = new Map();
  for (const variable of variables) {
    originals.set(variable.sourceName, variable.name);
    if (variable.symbol) {
      if (symbols.has(variable.symbol)) throw new Error(`Duplicate expression symbol ${variable.symbol}.`);
      symbols.set(variable.symbol, variable.name);
    }
  }
  return { originals, symbols };
}

/** Read transition data from Discovery, YAPNE, or ordinary PNML. */
function readTransition(element, names) {
  const tools = children(element, 'toolspecific').filter(tool => tool.getAttribute('tool') === 'dpn-discovery');
  const label = text(element, 'name') || element.getAttribute('id');
  const conditions = tools.length ? readDiscoveryConditions(tools, names) : readYapneConditions(element);
  const contract = tools.flatMap(tool => children(tool, 'contract'));
  if (contract.length > 1) throw new Error(`Transition ${label}: multiple Discovery contracts.`);
  const discoveryContract = contract.length ? readContract(contract[0], names) : undefined;
  return { id: element.getAttribute('id'), label, position: position(element), priority: 1, delay: 0,
    ...conditions, discoveryContract, isDataAware: !!(tools.length || conditions.precondition || conditions.postcondition),
    silent: element.getAttribute('silent') === 'true' || (tools.length > 0 && label === 'τ') ||
      children(element, 'toolspecific').some(tool => text(tool, 'silent') === 'true') };
}

/** Translate separate Discovery updates into a conjunction of simultaneous equalities. */
function readDiscoveryConditions(tools, names) {
  const guards = tools.flatMap(tool => children(tool, 'guard'));
  if (guards.length > 1) throw new Error('Multiple Discovery guards on one transition.');
  const pre = guards.length ? readDiscoveryExpression(guards[0], names) : null;
  const writes = new Set();
  const updates = tools.flatMap(tool => children(tool, 'update')).map(update => {
    const sourceName = update.getAttribute('variable');
    if (!sourceName || writes.has(sourceName)) throw new Error('Missing or duplicate update target.');
    writes.add(sourceName);
    const rhs = readDiscoveryExpression(update, names);
    if (!rhs) throw new Error(`Empty update for ${sourceName}.`);
    return callNode('=', [varNode(names.originals.get(sourceName) || sourceName, true), rhs]);
  });
  const post = updates.length > 1 ? callNode('and', updates) : updates[0];
  return { precondition: pre ? toGuardString(pre) : '', postcondition: post ? toGuardString(post) : '' };
}

/** Decode an expression using its declared symbol namespace, without textual guessing. */
function readDiscoveryExpression(element, names) {
  const syntax = element.getAttribute('syntax');
  if (syntax && syntax !== 'smtlib2') throw new Error(`Unsupported Discovery expression syntax ${syntax}.`);
  try {
    const expression = element.textContent.trim();
    if (!syntax) validateLegacyIdentifiers(expression, names.originals, element.localName === 'guard');
    const ast = parse(expression).ast;
    return renameReferences(ast, syntax ? names.symbols : names.originals);
  } catch (error) {
    throw new Error(`Cannot read Discovery expression: ${error.message} Re-export this model with the updated Discovery exporter.`);
  }
}

/** Refuse unescaped old names that could otherwise become literals or operators. */
function validateLegacyIdentifiers(expression, originals, isGuard) {
  if (isGuard && /^(true|false)$/i.test(expression)) return;
  const unquoted = expression.replace(/\|[^|]*\|/g, ' ');
  for (const name of originals.keys()) {
    if (!/[|\\]/.test(name) && quoteGuardIdentifier(name) === name) continue;
    const escaped = name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const occurrence = new RegExp(`(^|[^A-Za-z0-9_])${escaped}(?![A-Za-z0-9_])`);
    if (occurrence.test(unquoted)) throw new Error(`Ambiguous legacy identifier ${JSON.stringify(name)}.`);
  }
}

/** Preserve explicit guards/updates and recognize legacy YAPNE combined attributes. */
function readYapneConditions(element) {
  let pre = text(element, 'dataGuard') || element.getAttribute('guard') || text(element, 'guard');
  let post = text(element, 'dataUpdate') || text(element, 'dataAction');
  const marker = /\s*\|\s*post:\s*/.exec(pre);
  if (marker) {
    post = pre.slice(marker.index + marker[0].length).replace(/ \| /g, ' ; ');
    pre = pre.slice(0, marker.index).replace(/^pre:\s*/, '');
  } else if (pre.startsWith('post:')) {
    post = pre.slice('post:'.length).trim(); pre = '';
  } else pre = pre.replace(/^pre:\s*/, '');
  return { precondition: normalizeCondition(pre, false), postcondition: normalizeCondition(post, true) };
}

/** Prefer existing grammar; migrate legacy operators only when parsing fails. */
function normalizeCondition(expression, isPostcondition) {
  if (!expression) return '';
  try { parse(expression, { isPostcondition }); return expression.trim(); }
  catch {
    const migrated = isPostcondition ? migratePostcondition(expression) : migratePrecondition(expression);
    parse(migrated, { isPostcondition }); return migrated;
  }
}

/** Rename only variable AST nodes, never textual substrings or operators. */
function renameReferences(ast, names, bound = new Map()) {
  if (!ast) return ast;
  if (ast.type === NodeType.VAR) return { ...ast, name: bound.has(ast.name) ? bound.get(ast.name) : names.get(ast.name) || ast.name };
  if (ast.type === NodeType.QUANTIFIER || ast.type === NodeType.LET_EXPR) {
    const scoped = new Map(bound);
    const used = new Set([...names.keys(), ...names.values(), ...bound.values(), ...getVariableReferences(ast).read]);
    const bindings = ast.bindings.map(binding => {
      let name = binding.name;
      if (used.has(name)) {
        let index = 0;
        while (used.has(`pnml_bound_${index}`)) index++;
        name = `pnml_bound_${index}`;
      }
      used.add(name); scoped.set(binding.name, name);
      return { ...binding, name, ...(binding.expr ? { expr: renameReferences(binding.expr, names, bound) } : {}) };
    });
    return { ...ast, bindings, body: renameReferences(ast.body, names, scoped) };
  }
  const renamed = { ...ast };
  for (const key of ['left', 'right', 'operand']) if (ast[key]) renamed[key] = renameReferences(ast[key], names, bound);
  if (ast.args) renamed.args = ast.args.map(arg => renameReferences(arg, names, bound));
  return renamed;
}

/** Accept the primitive values defined by Discovery's event-data contract. */
function isDataValue(value) {
  return typeof value === 'string' || typeof value === 'boolean' || (typeof value === 'number' && Number.isFinite(value));
}

/** Read an exact observed payload and map variable aliases without coercion. */
function readPayload(value, names) {
  const parsed = parseNumericJSON(value);
  if (!parsed || Array.isArray(parsed) || typeof parsed !== 'object') throw new Error('Observed payload must be a JSON object.');
  const entries = Object.entries(parsed).map(([name, item]) => {
    if (!isDataValue(item)) throw new Error(`Invalid observed value for ${name}.`);
    return [names.originals.get(name) || name, item];
  });
  return Object.fromEntries(entries);
}

/** Keep the full observed-relation OR generalized-contract semantics. */
function readContract(element, names) {
  const generalized = element.getAttribute('generalized');
  if (!['true', 'false'].includes(generalized)) throw new Error('Discovery contract needs an explicit generalized flag.');
  const observedPairs = children(element, 'observedPair').map(pair => ({
    before: readPayload(text(pair, 'before'), names), after: readPayload(text(pair, 'after'), names)
  }));
  const expected = element.getAttribute('observedPairCount');
  if (expected !== null && count(expected, 'Observed pair count') !== observedPairs.length) throw new Error('Discovery observed-pair count does not match its payload.');
  return { generalized: generalized === 'true', observedPairs };
}

/** Add variables actually referenced by undeclared guards and retained data. */
function completeVariables(parsed, hasContracts) {
  const known = new Set(parsed.dataVariables.map(variable => variable.name));
  if (known.size !== parsed.dataVariables.length) throw new Error('Duplicate PNML variable names.');
  const used = new Set();
  for (const transition of parsed.transitions) {
    for (const [expression, isPostcondition] of [[transition.precondition, false], [transition.postcondition, true]]) {
      const refs = getVariableReferences(parse(expression, { isPostcondition }).ast);
      for (const name of [...refs.read, ...refs.written]) used.add(name);
    }
    for (const pair of transition.discoveryContract?.observedPairs || []) {
      for (const name of [...Object.keys(pair.before), ...Object.keys(pair.after)]) used.add(name);
    }
  }
  for (const name of used) {
    if (known.has(name)) continue;
    const ids = new Set(parsed.dataVariables.map(variable => variable.id));
    let index = parsed.dataVariables.length;
    while (ids.has(`variable_${index}`)) index++;
    parsed.dataVariables.push({ id: `variable_${index}`, name, sourceName: name,
      type: hasContracts ? 'data' : 'real', currentValue: undefined, requiresInitialValue: !hasContracts,
      typeInferred: !hasContracts, origin: 'Expression or observed relation', description: '' });
    known.add(name);
  }
}

/** Read alternative exact final markings without collapsing them into one marking. */
function readFinalMarkings(net, places) {
  const sections = descendants(net, 'finalmarkings');
  if (!sections.length) return [];
  const ids = new Set(places.map(place => place.id));
  return sections.flatMap(section => children(section, 'marking')).map(marking => {
    const entries = children(marking, 'place').map(place => {
      const id = place.getAttribute('idref');
      if (!ids.has(id)) throw new Error(`Unknown final-marking place ${id}.`);
      return [id, count(text(place, 'text'), 'Final marking')];
    });
    if (new Set(entries.map(([id]) => id)).size !== entries.length) throw new Error('Duplicate place in final marking.');
    return Object.fromEntries(entries);
  });
}

/** Reject incomplete control-flow references before the editor is replaced. */
function validateStructure(parsed) {
  for (const key of ['places', 'transitions', 'arcs', 'dataVariables']) {
    if (parsed[key] === undefined && key === 'dataVariables') continue;
    if (!Array.isArray(parsed[key])) throw new Error(`PNML ${key} must be an array.`);
    const ids = parsed[key].map(item => item.id);
    if (ids.some(id => typeof id !== 'string' || !id) || new Set(ids).size !== ids.length) {
      throw new Error(`Missing or duplicate ${key} identifiers.`);
    }
  }
  const nodes = [...parsed.places, ...parsed.transitions];
  const ids = new Set(nodes.map(node => node.id));
  if (ids.has(null) || ids.has('') || ids.size !== nodes.length) throw new Error('Missing or duplicate PNML node identifiers.');
  const places = new Set(parsed.places.map(place => place.id));
  for (const arc of parsed.arcs) {
    if (!ids.has(arc.source) || !ids.has(arc.target) || places.has(arc.source) === places.has(arc.target)) {
      throw new Error(`Arc ${arc.id} must connect an existing place and transition.`);
    }
  }
}
