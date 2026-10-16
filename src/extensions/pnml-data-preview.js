import { parseInitialValue } from './pnml-reader.js';
import { assessGuardCompatibility } from './guard-language/guard-compatibility.js';

/** Create a DOM element with text, keeping PNML content out of HTML markup. */
function element(tag, content, className = '') {
  const node = document.createElement(tag);
  if (content !== undefined) node.textContent = content;
  if (className) node.className = className;
  return node;
}

/** Show extracted variables and editable initial values alongside feature support. */
export function renderDataPreview(container, parsed, onChange) {
  container.replaceChildren(element('h3', 'Data and feature compatibility'));
  container.append(element('p', 'Conditions keep their read/write meaning: x reads the old value; x\' writes the new value. All updates on one transition use the same old state.'));
  if (parsed.discoveryMetadata?.formatVersion === '2.0') {
    container.append(element('p', 'Observed before/after relations are preserved. Data starts empty, as in Discovery. Native simulation chooses uniformly among distinct permitted successors; these are execution settings, not learned probabilities.'));
  } else if (parsed.dataVariables.some(variable => variable.requiresInitialValue)) {
    container.append(element('p', 'This file omits initial data values. Enter them below before importing. Numeric types are suggested where the file declares no type; review these choices.', 'pnml-data-warning'));
  }
  renderVariables(container, parsed, onChange);
  const status = element('div', undefined, 'pnml-feature-status');
  status.setAttribute('aria-live', 'polite');
  container.append(status);
  renderCompatibility(status, parsed);
  renderConditions(container, parsed);
  container.hidden = false;
}

/** Render a compact table of extracted declarations and values. */
function renderVariables(container, parsed, onChange) {
  if (!parsed.dataVariables.length) {
    container.append(element('p', 'No data variables found.'));
    return;
  }
  const table = element('table', undefined, 'pnml-data-table');
  const head = element('tr');
  for (const title of ['Variable', 'Type', 'Initial value']) head.append(element('th', title));
  const thead = element('thead'); thead.append(head); table.append(thead);
  const body = element('tbody');
  for (const variable of parsed.dataVariables) body.append(variableRow(variable, parsed, container, onChange));
  table.append(body); container.append(table);
}

/** Build controls for one variable; relation-backed data retains its empty initial state. */
function variableRow(variable, parsed, container, onChange) {
  const row = element('tr');
  const name = element('td', variable.sourceName || variable.name);
  if (variable.sourceName && variable.sourceName !== variable.name) name.append(element('small', `Expression name: ${variable.name}`));
  name.append(element('small', variable.origin || 'PNML declaration'));
  row.append(name);
  const typeCell = element('td');
  const valueCell = element('td');
  if (variable.type === 'data') {
    typeCell.textContent = 'Observed data (typed values)';
    valueCell.textContent = variable.currentValue === undefined ? 'Absent — supplied by the first observed event' : JSON.stringify(variable.currentValue);
  } else {
    const select = createTypeSelect(variable);
    const input = element('input');
    input.type = 'text'; input.value = variable.currentValue === undefined ? '' : String(variable.currentValue);
    input.setAttribute('aria-label', `Initial value for ${variable.sourceName || variable.name}`);
    input.placeholder = 'Required';
    const error = element('small', '', 'pnml-data-warning');
    const update = () => updateVariable(variable, select, input, error, parsed, container, onChange);
    select.addEventListener('change', update); input.addEventListener('input', update);
    typeCell.append(select); valueCell.append(input, error);
  }
  row.append(typeCell, valueCell);
  return row;
}

/** Present only the fixed scalar types YAPNE can execute. */
function createTypeSelect(variable) {
  const select = element('select');
  select.setAttribute('aria-label', `Type for ${variable.sourceName || variable.name}`);
  for (const [value, label] of [['real', 'Real'], ['int', 'Integer'], ['bool', 'Boolean']]) {
    const option = element('option', label); option.value = value; select.append(option);
  }
  select.value = variable.type;
  return select;
}

/** Apply validated initial-data choices and refresh feature eligibility. */
function updateVariable(variable, select, input, error, parsed, container, onChange) {
  variable.type = select.value;
  try {
    variable.currentValue = parseInitialValue(input.value, variable.type);
    variable.initialValue = variable.currentValue;
    variable.requiresInitialValue = false;
    input.setCustomValidity(''); error.textContent = '';
  } catch (failure) {
    variable.requiresInitialValue = true;
    input.setCustomValidity(failure.message); error.textContent = failure.message;
  }
  renderCompatibility(container.querySelector('.pnml-feature-status'), parsed);
  onChange();
}

/** Describe each feature's actual grammar boundary, separately from verification results. */
function renderCompatibility(container, parsed) {
  const compatibility = assessGuardCompatibility(parsed);
  container.replaceChildren();
  const labels = { simulation: 'Native simulation and event logs', probabilistic: 'Paper-based probabilistic inference', soundness: 'Suvorov–Lomazova soundness checker' };
  for (const [key, label] of Object.entries(labels)) {
    const feature = compatibility[key];
    const row = element('div', undefined, 'pnml-feature-row');
    row.append(element('strong', `${label}: ${feature.supported ? 'Grammar supported' : 'Restricted'}`));
    const reasons = [...new Set(feature.reasons)];
    if (reasons.length === 1) row.append(element('p', reasons[0]));
    if (reasons.length > 1) {
      const details = element('details');
      details.append(element('summary', `Why this feature is restricted (${reasons.length} findings)`));
      for (const reason of reasons) details.append(element('p', reason));
      row.append(details);
    }
    container.append(row);
  }
  if (!parsed.finalMarkings?.length && !parsed.places.some(place => place.finalMarking !== null && place.finalMarking !== undefined)) {
    container.append(element('p', 'No final marking is declared. Simulation can run, but a deadlock is not evidence of successful completion. Set a final marking before soundness analysis.', 'pnml-data-warning'));
  }
  container.append(element('small', 'Grammar support is not a soundness result or a proof of probabilistic equivalence. Native numeric execution uses JavaScript number precision, not exact rational arithmetic.'));
}

/** Show every extracted condition without treating source text as executable HTML. */
function renderConditions(container, parsed) {
  const details = element('details');
  details.append(element('summary', `Extracted conditions (${parsed.transitions.length} transitions)`));
  for (const transition of parsed.transitions) {
    const item = element('div', undefined, 'pnml-condition');
    item.append(element('strong', transition.label || transition.id));
    item.append(element('code', `Pre: ${transition.precondition || 'true'}`));
    item.append(element('code', `Post: ${transition.postcondition || 'true (no writes)'}`));
    if (transition.discoveryContract) {
      const contract = transition.discoveryContract;
      item.append(element('p', `${contract.observedPairs.length} observed pairs; generalized guard/update branch ${contract.generalized ? 'enabled' : 'disabled'}.`));
    }
    details.append(item);
  }
  container.append(details);
}

/** Require explicit values only where the imported model leaves them unspecified. */
export function isImportDataReady(parsed) {
  return !!parsed && parsed.dataVariables.every(variable => !variable.requiresInitialValue);
}
