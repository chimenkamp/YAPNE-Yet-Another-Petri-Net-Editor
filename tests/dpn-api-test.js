/**
 * Example: Data Petri Net Event Log Generation
 * 
 * This example demonstrates how to use the enhanced Event Log Generator
 * with Data Petri Nets, including variable tracking, preconditions, and postconditions.
 */

import { EventLogGenerator } from '../src/event-log-generator.js';
import { DataPetriNet, DataAwareTransition, DataVariable } from '../src/extensions/dpn-model.js';
import { Place, Arc } from '../src/petri-net-simulator.js';

/**
 * Example 1: Simple Order Processing with Data
 */
async function createOrderProcessingExample() {
  console.log('=== Example 1: Order Processing with Data ===\n');
  
  // Create a Data Petri Net
  const dpn = new DataPetriNet('order-dpn', 'Order Processing', 'Order processing with approval workflow');
  
  // Define data variables
  const orderCount = new DataVariable('v1', 'orderCount', 'int', 0, 'Number of processed orders');
  const totalAmount = new DataVariable('v2', 'totalAmount', 'float', 0.0, 'Total order amount');
  const approved = new DataVariable('v3', 'approved', 'boolean', false, 'Whether order is approved');
  
  dpn.addDataVariable(orderCount);
  dpn.addDataVariable(totalAmount);
  dpn.addDataVariable(approved);
  
  // Create places
  const p1 = new Place('p1', { x: 100, y: 100 }, 'Order Received', 1, -1);
  const p2 = new Place('p2', { x: 300, y: 100 }, 'Order Validated', 0, -1);
  const p3 = new Place('p3', { x: 500, y: 100 }, 'Order Approved', 0, -1);
  const p4 = new Place('p4', { x: 700, y: 100 }, 'Order Completed', 0, -1);
  
  dpn.places.set(p1.id, p1);
  dpn.places.set(p2.id, p2);
  dpn.places.set(p3.id, p3);
  dpn.places.set(p4.id, p4);
  
  // Create data-aware transitions
  // T1: Validate Order (increment order count)
  const t1 = new DataAwareTransition(
    't1',
    { x: 200, y: 100 },
    'Validate Order',
    1,
    1000,
    '', // No precondition
    'orderCount\' = orderCount + 1; totalAmount\' = totalAmount + 100.50' // Postcondition
  );
  
  // T2: Approve Order (only if order count < 10)
  const t2 = new DataAwareTransition(
    't2',
    { x: 400, y: 100 },
    'Approve Order',
    1,
    2000,
    'orderCount < 10 && !approved', // Precondition: only approve if less than 10 orders and not yet approved
    'approved\' = true' // Postcondition: mark as approved
  );
  
  // T3: Complete Order
  const t3 = new DataAwareTransition(
    't3',
    { x: 600, y: 100 },
    'Complete Order',
    1,
    500,
    'approved', // Precondition: must be approved
    '' // No postcondition
  );
  
  dpn.transitions.set(t1.id, t1);
  dpn.transitions.set(t2.id, t2);
  dpn.transitions.set(t3.id, t3);
  
  // Create arcs
  dpn.arcs.set('a1', new Arc('a1', p1.id, t1.id, 1, 'regular', [], ''));
  dpn.arcs.set('a2', new Arc('a2', t1.id, p2.id, 1, 'regular', [], ''));
  dpn.arcs.set('a3', new Arc('a3', p2.id, t2.id, 1, 'regular', [], ''));
  dpn.arcs.set('a4', new Arc('a4', t2.id, p3.id, 1, 'regular', [], ''));
  dpn.arcs.set('a5', new Arc('a5', p3.id, t3.id, 1, 'regular', [], ''));
  dpn.arcs.set('a6', new Arc('a6', t3.id, p4.id, 1, 'regular', [], ''));
  
  // Create event log generator
  const generator = new EventLogGenerator(dpn, {
    startTimestamp: new Date('2025-10-23T10:00:00Z'),
    defaultTransitionDuration: 1000,
    timeUnit: 'minutes',
    timeScale: 1,
    caseArrivalRate: 5,
    arrivalDistribution: 'exponential',
    transitionSelectionStrategy: 'priority',
    caseName: 'Order',
    seed: 42 // For reproducible results
  });
  
  // Run simulation
  console.log('Running simulation for 5 cases...');
  const eventLog = await generator.simulateCases(5, 50);
  
  console.log(`Generated ${eventLog.length} events\n`);
  
  // Display some sample events
  console.log('Sample events:');
  eventLog.slice(0, 10).forEach((event, idx) => {
    console.log(`\n[${idx + 1}] ${event['concept:name']} (${event['lifecycle:transition']})`);
    console.log(`    Case: ${event['case:concept:name']}`);
    console.log(`    Time: ${event['time:timestamp']}`);
    
    // Show DPN-specific data
    if (event.variables_before) {
      console.log(`    Variables before: ${event.variables_before}`);
    }
    if (event.precondition) {
      console.log(`    Precondition: ${event.precondition}`);
    }
    if (event.variable_changes) {
      console.log(`    Variable changes: ${event.variable_changes}`);
    }
    if (event.variables_after) {
      console.log(`    Variables after: ${event.variables_after}`);
    }
  });
  
  // Get statistics
  const stats = generator.getStatistics();
  console.log('\n\nSimulation Statistics:');
  console.log('----------------------');
  console.log(`Total Cases: ${stats.totalCases}`);
  console.log(`Total Events: ${stats.totalEvents}`);
  console.log(`Average Case Duration: ${(stats.avgCaseDuration / 1000 / 60).toFixed(2)} minutes`);
  console.log(`Average Case Length: ${stats.avgCaseLength.toFixed(2)} activities`);
  
  // Export to different formats
  console.log('\n\n=== CSV Export (first 500 chars) ===');
  const csv = generator.exportToCSV();
  console.log(csv.substring(0, 500) + '...\n');
  
  console.log('=== XES Export (first 500 chars) ===');
  const xes = generator.exportToXES();
  console.log(xes.substring(0, 500) + '...\n');
  
  return generator;
}

/**
 * Example 2: Counter with Constraints
 */
async function createCounterExample() {
  console.log('\n\n=== Example 2: Counter with Constraints ===\n');
  
  // Create a Data Petri Net with counter logic
  const dpn = new DataPetriNet('counter-dpn', 'Counter', 'Simple counter with constraints');
  
  // Define variable: counter
  const counter = new DataVariable('v1', 'x', 'int', 0, 'Counter value');
  dpn.addDataVariable(counter);
  
  // Create places
  const p1 = new Place('p1', { x: 100, y: 100 }, 'Start', 1, -1);
  const p2 = new Place('p2', { x: 300, y: 100 }, 'Counting', 0, -1);
  const p3 = new Place('p3', { x: 500, y: 100 }, 'Done', 0, -1);
  
  dpn.places.set(p1.id, p1);
  dpn.places.set(p2.id, p2);
  dpn.places.set(p3.id, p3);
  
  // Create transitions
  const t1 = new DataAwareTransition(
    't1',
    { x: 200, y: 100 },
    'Increment',
    1,
    100,
    'x < 5', // Only increment if counter < 5
    'x\' = x + 1' // Increment counter
  );
  
  const t2 = new DataAwareTransition(
    't2',
    { x: 400, y: 100 },
    'Finish',
    1,
    100,
    'x >= 5', // Only finish when counter >= 5
    '' // No change
  );
  
  dpn.transitions.set(t1.id, t1);
  dpn.transitions.set(t2.id, t2);
  
  // Create arcs (with loop for increment)
  dpn.arcs.set('a1', new Arc('a1', p1.id, t1.id, 1, 'regular', [], ''));
  dpn.arcs.set('a2', new Arc('a2', t1.id, p2.id, 1, 'regular', [], ''));
  dpn.arcs.set('a3', new Arc('a3', p2.id, t1.id, 1, 'regular', [], '')); // Loop back
  dpn.arcs.set('a4', new Arc('a4', p2.id, t2.id, 1, 'regular', [], ''));
  dpn.arcs.set('a5', new Arc('a5', t2.id, p3.id, 1, 'regular', [], ''));
  
  // Create event log generator
  const generator = new EventLogGenerator(dpn, {
    startTimestamp: new Date('2025-10-23T12:00:00Z'),
    defaultTransitionDuration: 100,
    timeUnit: 'seconds',
    caseArrivalRate: 1,
    caseName: 'Counter',
    seed: 123
  });
  
  // Run simulation
  console.log('Running counter simulation for 3 cases...');
  const eventLog = await generator.simulateCases(3, 20);
  
  console.log(`Generated ${eventLog.length} events\n`);
  
  // Show the progression of the counter
  console.log('Counter progression:');
  let lastCase = null;
  eventLog.forEach(event => {
    if (event['case:concept:name'] !== lastCase) {
      console.log(`\n--- ${event['case:concept:name']} ---`);
      lastCase = event['case:concept:name'];
    }
    
    if (event.variables_after) {
      const vars = JSON.parse(event.variables_after);
      console.log(`  ${event['concept:name']}: x = ${vars.x}`);
    }
  });
  
  return generator;
}

/**
 * Run all examples
 */
async function runExamples() {
  try {
    await createOrderProcessingExample();
    await createCounterExample();
    
    console.log('\n\n✅ All examples completed successfully!');
  } catch (error) {
    console.error('❌ Error running examples:', error);
    console.error(error.stack);
  }
}

// Export for use in browser or Node.js
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { createOrderProcessingExample, createCounterExample, runExamples };
}

// Auto-run if executed directly
if (typeof window !== 'undefined') {
  window.dpnExamples = { createOrderProcessingExample, createCounterExample, runExamples };
  console.log('DPN Event Log Examples loaded! Run window.dpnExamples.runExamples() to see them in action.');
}
