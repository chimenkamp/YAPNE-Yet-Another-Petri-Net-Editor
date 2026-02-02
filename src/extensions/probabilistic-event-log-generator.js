/**
 * Probabilistic Event Log Generator for Data Petri Nets
 * 
 * Implements event log generation using the approach from
 * "Data Petri Nets Meet Probabilistic Programming" (Kuhn et al., BPM 2024)
 * https://doi.org/10.1007/978-3-031-70396-6_2
 * 
 * This generator uses the probabilistic execution engine for:
 * - [Definition 3] Uniform scheduler ST for transition selection
 * - [Section 5.1] Goal state detection via finalMarking
 * - [Figure 5] Csim loop structure for trace generation
 * - [Section 5.2] Proper handling of DPN expressions via WebPPL
 * 
 * Key features:
 * 1. Uses finalMarking to determine case completion (not endPlaces)
 * 2. Selects single transitions uniformly (scheduler ST)
 * 3. Validates goal state definition before generation
 * 4. Supports WebPPL mode for complex constraint postconditions
 */

import { PetriNet, Place, Transition, Arc } from '../petri-net-simulator.js';
import { DataPetriNet, DataAwareTransition, DataVariable } from './dpn-model.js';
import { ProbabilisticExecutionEngine, createSeededRandom } from './probabilistic-execution.js';
import { WebPPLCodeGenerator } from './webppl-code-generator.js';

/**
 * ProbabilisticEventLogGenerator
 * 
 * Generates event logs using probabilistic programming semantics.
 * 
 * [Definition 6] (Run Probability):
 * For a goal set G and a set Runs_G of runs ending in G,
 * P_S^N(ρ) = L_S^N(ρ) / Σ_{ρ'∈Runs_G} L_S^N(ρ')
 * 
 * This class generates N independent runs for statistical analysis.
 */
class ProbabilisticEventLogGenerator {
    /**
     * Creates a new Probabilistic Event Log Generator
     * 
     * @param {PetriNet|DataPetriNet} petriNet - The Petri net to simulate
     * @param {Object} options - Generation options
     * @param {Date|string} options.startTimestamp - Starting timestamp (default: now)
     * @param {number} options.seed - Random seed for reproducibility (default: Date.now())
     * @param {number} options.maxStepsPerCase - Max steps per case (default: 10000)
     * @param {number} options.avgTransitionDuration - Avg duration in ms (default: 60000 = 1 min)
     * @param {string} options.caseName - Prefix for case names (default: 'case')
     * @param {string} options.eventLogFormat - 'lifecycle' | 'classic' (default: 'classic')
     * @param {boolean} options.includeVariables - Include variable values (default: true)
     * @param {boolean} options.validateGoal - Validate finalMarking exists (default: true)
     * @param {boolean} options.useWebPPL - Use WebPPL for complex DPNs (default: false)
     * @param {Object} options.variableDistributions - SV distributions for variable sampling
     */
    constructor(petriNet, options = {}) {
        this.petriNet = petriNet;
        
        // Parse options
        this.options = {
            startTimestamp: options.startTimestamp ? new Date(options.startTimestamp) : new Date(),
            seed: options.seed ?? Date.now(),
            maxStepsPerCase: options.maxStepsPerCase ?? 10000,
            avgTransitionDuration: options.avgTransitionDuration ?? 60000,
            caseName: options.caseName ?? 'case',
            eventLogFormat: options.eventLogFormat ?? 'classic',
            includeVariables: options.includeVariables ?? true,
            validateGoal: options.validateGoal ?? true,
            useWebPPL: options.useWebPPL ?? false,
            variableDistributions: options.variableDistributions ?? {}
        };
        
        // [Definition 3] Initialize the probabilistic execution engine
        this.engine = new ProbabilisticExecutionEngine({
            seed: this.options.seed,
            scheduler: 'uniform',  // [Example 1] Uniform scheduler ST
            maxSteps: this.options.maxStepsPerCase,
            variableDistributions: this.options.variableDistributions,
            executionMode: this.options.useWebPPL ? 'webppl' : 'auto'
        });
        
        // Initialize WebPPL code generator for batch generation
        this.codeGenerator = new WebPPLCodeGenerator({
            schedulerType: 'uniform',
            variableDistributions: this.options.variableDistributions,
            maxSteps: this.options.maxStepsPerCase
        });
        
        // Event log storage
        this.eventLog = [];
        this.cases = [];
        this.caseCounter = 0;
        
        // Track variable changes for classic format
        this.previousVariableValues = {};
    }

    /**
     * Clone the Petri net to create a fresh instance for each case.
     * 
     * @returns {PetriNet|DataPetriNet} A fresh clone of the net
     */
    cloneNet() {
        // Export to JSON and re-import to create a clean clone
        const netData = this.exportNetToJSON(this.petriNet);
        return this.importNetFromJSON(netData);
    }

    /**
     * Export net to JSON format for cloning
     * @private
     */
    exportNetToJSON(net) {
        const data = {
            places: [],
            transitions: [],
            arcs: [],
            dataVariables: []
        };
        
        // Export places
        for (const [id, place] of net.places) {
            data.places.push({
                id: id,
                label: place.label,
                tokens: place.tokens,
                finalMarking: place.finalMarking,
                capacity: place.capacity,
                x: place.position?.x ?? place.x ?? 0,
                y: place.position?.y ?? place.y ?? 0
            });
        }
        
        // Export transitions
        for (const [id, transition] of net.transitions) {
            const transData = {
                id: id,
                label: transition.label,
                delay: transition.delay,
                priority: transition.priority,
                silent: transition.silent || false,
                x: transition.position?.x ?? transition.x ?? 0,
                y: transition.position?.y ?? transition.y ?? 0
            };
            
            // DPN fields
            if (transition.precondition !== undefined) {
                transData.precondition = transition.precondition;
            }
            if (transition.postcondition !== undefined) {
                transData.postcondition = transition.postcondition;
            }
            
            data.transitions.push(transData);
        }
        
        // Export arcs
        for (const [id, arc] of net.arcs) {
            data.arcs.push({
                id: id,
                source: arc.source,
                target: arc.target,
                weight: arc.weight,
                type: arc.type
            });
        }
        
        // Export data variables (DPN)
        if (net.dataVariables instanceof Map) {
            for (const [id, variable] of net.dataVariables) {
                data.dataVariables.push({
                    id: id,
                    name: variable.name,
                    type: variable.type,
                    currentValue: variable.currentValue
                });
            }
        }
        
        return data;
    }

    /**
     * Import net from JSON data
     * @private
     */
    importNetFromJSON(data) {
        // Determine if this is a DPN
        const isDPN = data.dataVariables && data.dataVariables.length > 0;
        
        let net;
        if (isDPN) {
            net = new DataPetriNet();
        } else {
            net = new PetriNet();
        }
        
        // Import places
        for (const placeData of data.places) {
            const place = new Place(
                placeData.id,
                { x: placeData.x || 0, y: placeData.y || 0 },  // position
                placeData.label || placeData.id,               // label
                placeData.tokens || 0,                          // tokens
                placeData.capacity ?? null,                     // capacity
                placeData.finalMarking ?? null                  // finalMarking
            );
            net.places.set(place.id, place);
        }
        
        // Import transitions
        for (const transData of data.transitions) {
            const position = { x: transData.x || 0, y: transData.y || 0 };
            let transition;
            if (isDPN) {
                transition = new DataAwareTransition(
                    transData.id,
                    position,
                    transData.label || transData.id,
                    transData.priority || 1,
                    transData.delay || 0,
                    transData.precondition || '',
                    transData.postcondition || '',
                    transData.silent || false
                );
            } else {
                transition = new Transition(
                    transData.id,
                    position,
                    transData.label || transData.id,
                    transData.priority || 1,
                    transData.delay || 0,
                    transData.silent || false
                );
            }
            net.transitions.set(transition.id, transition);
        }
        
        // Import arcs
        for (const arcData of data.arcs) {
            const arc = new Arc(
                arcData.id,
                arcData.source,
                arcData.target,
                arcData.weight || 1
            );
            arc.type = arcData.type || 'regular';
            net.arcs.set(arc.id, arc);
        }
        
        // Import data variables (DPN)
        if (isDPN && data.dataVariables) {
            for (const varData of data.dataVariables) {
                const variable = new DataVariable(
                    varData.id,
                    varData.name,
                    varData.type || 'int'
                );
                variable.currentValue = varData.currentValue ?? 0;
                net.dataVariables.set(variable.id, variable);
            }
        }
        
        return net;
    }

    /**
     * [Section 5.1] Validate that the net has finalMarking defined
     * 
     * "Goal states G must be specified via the 'finalMarking' attribute"
     * 
     * @throws {Error} If no finalMarking is defined and validateGoal is true
     */
    validateGoalStateDefinition() {
        if (!this.options.validateGoal) return;
        this.engine.validateGoalStateDefinition(this.petriNet);
    }

    /**
     * Generate WebPPL code for the Petri net.
     * 
     * [Section 5] Generates the Csim program for probabilistic simulation.
     * 
     * @param {Object} options - Generation options
     * @returns {string} Generated WebPPL code
     */
    generateWebPPLCode(options = {}) {
        return this.codeGenerator.generateCode(this.petriNet, options);
    }

    /**
     * Check if WebPPL mode is recommended for this net.
     * 
     * @returns {boolean} True if WebPPL mode is recommended
     */
    recommendsWebPPL() {
        return this.engine.netRequiresWebPPL(this.petriNet);
    }

    /**
     * Generate N cases using probabilistic execution
     * 
     * [Definition 6] Generates N independent runs for statistical analysis
     * 
     * @param {number} numCases - Number of cases to generate
     * @param {Object} callbacks - Optional callback functions
     * @param {function} callbacks.onCaseStart - (caseNum) => void
     * @param {function} callbacks.onCaseEnd - (caseNum, result) => void
     * @param {function} callbacks.onStep - (caseNum, stepNum, transitionId) => void
     * @returns {Promise<Array>} The generated event log
     */
    async generateCases(numCases, callbacks = {}) {
        // [Section 5.1] Validate goal state definition
        this.validateGoalStateDefinition();
        
        // Reset state
        this.eventLog = [];
        this.cases = [];
        this.caseCounter = 0;
        this.previousVariableValues = {};
        
        let currentTime = new Date(this.options.startTimestamp);
        
        // Reseed engine for reproducibility
        this.engine.reseed(this.options.seed);
        
        // Helper to yield to UI thread periodically
        const yieldToUI = () => new Promise(resolve => setTimeout(resolve, 0));
        
        // Generate each case
        for (let caseNum = 1; caseNum <= numCases; caseNum++) {
            // Yield to UI at start of each case to keep UI responsive
            await yieldToUI();
            
            if (callbacks.onCaseStart) {
                callbacks.onCaseStart(caseNum);
            }
            
            // Create fresh net clone for this case
            const net = this.cloneNet();
            const caseId = `${this.options.caseName}_${caseNum}`;
            this.caseCounter++;
            
            // Reseed for this specific case
            this.engine.reseed(this.options.seed + caseNum);
            
            // Initialize variable tracking for this case
            this.previousVariableValues[caseId] = {};
            
            // Get initial variable state
            let variablesBefore = null;
            const isDPN = net.dataVariables instanceof Map;
            if (isDPN && typeof net.getDataValuation === 'function') {
                variablesBefore = net.getDataValuation();
            }
            
            // Log case start (lifecycle format only)
            if (this.options.eventLogFormat === 'lifecycle') {
                this.eventLog.push({
                    'case:concept:name': caseId,
                    'concept:name': 'Case_Start',
                    'time:timestamp': currentTime.toISOString(),
                    'lifecycle:transition': 'complete'
                });
            }
            
            // [Figure 5] Run simulation for this case
            const caseTrace = [];
            let stepNum = 0;
            let status = 'active';
            
            while (stepNum < this.options.maxStepsPerCase) {
                // [Section 5.2] Execute probabilistic step
                const stepResult = await this.engine.step(net);
                
                if (!stepResult.fired) {
                    // Simulation ended (goal or deadlock)
                    status = stepResult.status;
                    break;
                }
                
                stepNum++;
                const transitionId = stepResult.transitionId;
                const transition = net.transitions.get(transitionId);
                const transitionName = transition?.label || transitionId;
                
                // Skip silent transitions
                if (transition?.silent) {
                    continue;
                }
                
                // Get variable state after firing
                let variablesAfter = null;
                if (isDPN && typeof net.getDataValuation === 'function') {
                    variablesAfter = net.getDataValuation();
                }
                
                // Calculate timestamp
                const duration = transition?.delay || this.options.avgTransitionDuration;
                const eventTime = new Date(currentTime);
                currentTime = new Date(currentTime.getTime() + duration);
                
                // Log the event
                if (this.options.eventLogFormat === 'classic') {
                    this.logClassicEvent(caseId, transitionName, eventTime, variablesAfter);
                } else {
                    // Lifecycle format: start event
                    this.eventLog.push({
                        'case:concept:name': caseId,
                        'concept:name': transitionName,
                        'time:timestamp': eventTime.toISOString(),
                        'lifecycle:transition': 'start'
                    });
                    
                    // Complete event
                    this.eventLog.push({
                        'case:concept:name': caseId,
                        'concept:name': transitionName,
                        'time:timestamp': currentTime.toISOString(),
                        'lifecycle:transition': 'complete'
                    });
                }
                
                // Track step in case trace
                caseTrace.push({
                    step: stepNum,
                    transitionId: transitionId,
                    transition: transitionName
                });
                
                // Update variablesBefore for next iteration
                variablesBefore = variablesAfter;
                
                // Callback
                if (callbacks.onStep) {
                    callbacks.onStep(caseNum, stepNum, transitionId);
                }
            }
            
            // Log case end (lifecycle format only)
            if (this.options.eventLogFormat === 'lifecycle') {
                this.eventLog.push({
                    'case:concept:name': caseId,
                    'concept:name': 'Case_End',
                    'time:timestamp': currentTime.toISOString(),
                    'lifecycle:transition': 'complete',
                    'status': status
                });
            }
            
            // Store case result
            const caseResult = {
                caseId: caseId,
                caseNum: caseNum,
                status: status,
                trace: caseTrace,
                traceLength: caseTrace.length
            };
            this.cases.push(caseResult);
            
            if (callbacks.onCaseEnd) {
                callbacks.onCaseEnd(caseNum, caseResult);
            }
            
            // Add inter-case delay
            currentTime = new Date(currentTime.getTime() + this.options.avgTransitionDuration);
        }
        
        return this.eventLog;
    }

    /**
     * Log an event in classic format (single event with variable columns)
     * 
     * @param {string} caseId - Case identifier
     * @param {string} activity - Activity name
     * @param {Date} timestamp - Event timestamp
     * @param {Object} variablesAfter - Variable values after transition
     * @private
     */
    logClassicEvent(caseId, activity, timestamp, variablesAfter) {
        const logEntry = {
            'case:concept:name': caseId,
            'concept:name': activity,
            'time:timestamp': timestamp.toISOString()
        };
        
        // Add variable columns - only include changed values
        if (this.options.includeVariables && variablesAfter) {
            for (const [varName, currentValue] of Object.entries(variablesAfter)) {
                const previousValue = this.previousVariableValues[caseId][varName];
                
                if (previousValue !== currentValue) {
                    logEntry[varName] = currentValue;
                    this.previousVariableValues[caseId][varName] = currentValue;
                } else {
                    logEntry[varName] = '';
                }
            }
        }
        
        this.eventLog.push(logEntry);
    }

    /**
     * Export event log to CSV format
     * @returns {string} CSV formatted event log
     */
    exportToCSV() {
        if (this.eventLog.length === 0) return '';
        
        // Collect all headers
        const headers = new Set();
        this.eventLog.forEach(event => {
            Object.keys(event).forEach(key => headers.add(key));
        });
        
        // Order headers: standard XES headers first, then variables
        const standardHeaders = ['case:concept:name', 'concept:name', 'time:timestamp'];
        if (this.options.eventLogFormat === 'lifecycle') {
            standardHeaders.push('lifecycle:transition');
        }
        const variableHeaders = Array.from(headers)
            .filter(h => !standardHeaders.includes(h))
            .sort();
        const orderedHeaders = [...standardHeaders.filter(h => headers.has(h)), ...variableHeaders];
        
        const rows = [orderedHeaders.join(',')];
        
        this.eventLog.forEach(event => {
            const row = orderedHeaders.map(header => {
                const value = event[header];
                if (value === undefined || value === null) return '';
                if (typeof value === 'string' && (value.includes(',') || value.includes('"'))) {
                    return `"${value.replace(/"/g, '""')}"`;
                }
                return value;
            }).join(',');
            rows.push(row);
        });
        
        return rows.join('\n');
    }

    /**
     * Export event log to XES (XML) format
     * @returns {string} XES formatted event log
     */
    exportToXES() {
        const netName = this.petriNet.name || 'Probabilistic DPN Simulation';
        
        let xes = `<?xml version="1.0" encoding="UTF-8"?>
<log xes.version="1.0" xmlns="http://www.xes-standard.org/">
  <extension name="Concept" prefix="concept" uri="http://www.xes-standard.org/concept.xesext"/>
  <extension name="Time" prefix="time" uri="http://www.xes-standard.org/time.xesext"/>
  <extension name="Lifecycle" prefix="lifecycle" uri="http://www.xes-standard.org/lifecycle.xesext"/>
  <classifier name="Activity" keys="concept:name"/>
  <string key="concept:name" value="${this.escapeXML(netName)}"/>
  <string key="source" value="ProbabilisticEventLogGenerator"/>
  <string key="generator:paper" value="Data Petri Nets Meet Probabilistic Programming (BPM 2024)"/>`;
        
        // Group events by case
        const eventsByCase = {};
        this.eventLog.forEach(event => {
            const caseId = event['case:concept:name'];
            if (!eventsByCase[caseId]) eventsByCase[caseId] = [];
            eventsByCase[caseId].push(event);
        });
        
        // Generate traces
        for (const [caseId, events] of Object.entries(eventsByCase)) {
            xes += `\n  <trace>
    <string key="concept:name" value="${this.escapeXML(caseId)}"/>`;
            
            for (const event of events) {
                xes += `\n    <event>`;
                for (const [key, value] of Object.entries(event)) {
                    if (key === 'case:concept:name') continue; // Already in trace
                    const escapedValue = this.escapeXML(String(value));
                    
                    if (key === 'time:timestamp') {
                        xes += `\n      <date key="${key}" value="${escapedValue}"/>`;
                    } else {
                        xes += `\n      <string key="${key}" value="${escapedValue}"/>`;
                    }
                }
                xes += `\n    </event>`;
            }
            
            xes += `\n  </trace>`;
        }
        
        xes += `\n</log>`;
        return xes;
    }

    /**
     * Export event log to JSON format
     * @returns {string} JSON formatted event log
     */
    exportToJSON() {
        return JSON.stringify({
            metadata: {
                generator: 'ProbabilisticEventLogGenerator',
                paper: 'Data Petri Nets Meet Probabilistic Programming (BPM 2024)',
                seed: this.options.seed,
                numCases: this.cases.length,
                format: this.options.eventLogFormat
            },
            cases: this.cases,
            events: this.eventLog
        }, null, 2);
    }

    /**
     * Get statistics about the generated log
     * @returns {Object} Generation statistics
     */
    getStatistics() {
        const totalCases = this.cases.length;
        const totalEvents = this.eventLog.filter(e => 
            !['Case_Start', 'Case_End'].includes(e['concept:name'])
        ).length;
        
        // Trace lengths
        const traceLengths = this.cases.map(c => c.traceLength);
        const avgTraceLength = totalCases > 0 
            ? traceLengths.reduce((a, b) => a + b, 0) / totalCases 
            : 0;
        const minTraceLength = totalCases > 0 ? Math.min(...traceLengths) : 0;
        const maxTraceLength = totalCases > 0 ? Math.max(...traceLengths) : 0;
        
        // Calculate case durations from event timestamps
        const caseDurations = [];
        const caseEvents = {};
        
        // Group events by case
        this.eventLog.forEach(event => {
            const caseId = event['case:concept:name'];
            if (!caseEvents[caseId]) {
                caseEvents[caseId] = [];
            }
            caseEvents[caseId].push(new Date(event['time:timestamp']).getTime());
        });
        
        // Calculate duration for each case
        for (const caseId in caseEvents) {
            const timestamps = caseEvents[caseId];
            if (timestamps.length >= 2) {
                const duration = Math.max(...timestamps) - Math.min(...timestamps);
                caseDurations.push(duration);
            } else {
                caseDurations.push(0);
            }
        }
        
        const avgCaseDuration = caseDurations.length > 0
            ? caseDurations.reduce((a, b) => a + b, 0) / caseDurations.length
            : 0;
        const minDuration = caseDurations.length > 0 ? Math.min(...caseDurations) : 0;
        const maxDuration = caseDurations.length > 0 ? Math.max(...caseDurations) : 0;
        
        // Status distribution
        const statusCounts = {};
        this.cases.forEach(c => {
            statusCounts[c.status] = (statusCounts[c.status] || 0) + 1;
        });
        
        // Activity frequency
        const activityFrequency = {};
        this.eventLog.forEach(event => {
            const activity = event['concept:name'];
            if (!['Case_Start', 'Case_End'].includes(activity)) {
                activityFrequency[activity] = (activityFrequency[activity] || 0) + 1;
            }
        });
        
        return {
            totalCases,
            totalEvents,
            // Trace length stats
            avgTraceLength,
            minTraceLength,
            maxTraceLength,
            // Compatibility aliases for displayStatistics
            avgCaseLength: avgTraceLength,
            // Duration stats
            avgCaseDuration,
            minDuration,
            maxDuration,
            // Other stats
            statusCounts,
            activityFrequency,
            seed: this.options.seed
        };
    }

    /**
     * Escape XML special characters
     * @private
     */
    escapeXML(str) {
        return str
            .replace(/&/g, '&amp;')
            .replace(/</g, '&lt;')
            .replace(/>/g, '&gt;')
            .replace(/"/g, '&quot;')
            .replace(/'/g, '&apos;');
    }
}

export { ProbabilisticEventLogGenerator };
