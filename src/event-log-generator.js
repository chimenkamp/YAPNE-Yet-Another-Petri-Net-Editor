/**
 * Petri Net Simulator
 * A class for simulating Petri nets and generating event logs.
 */
class EventLogGenerator {
    /**
     * Creates a new Petri Net Simulator
     * @param {PetriNet} petriNet - The Petri net to simulate
     * @param {Object} options - Simulation options
     * @param {Date|string} [options.startTimestamp=new Date()] - Starting timestamp for the simulation
     * @param {number} [options.defaultTransitionDuration=1000] - Default duration for transitions in milliseconds
     * @param {string} [options.timeUnit='minutes'] - Time unit for simulation ('seconds', 'minutes', 'hours', 'days')
     * @param {number} [options.timeScale=1] - Scale factor for time progression (e.g., 2 = twice as fast)
     * @param {number} [options.caseArrivalRate=10] - Average time between new case arrivals in timeUnit
     * @param {string} [options.arrivalDistribution='exponential'] - Distribution for case arrivals ('fixed', 'exponential', 'normal')
     * @param {Object} [options.arrivalParams={}] - Parameters for the arrival distribution
     * @param {string} [options.transitionSelectionStrategy='priority'] - Strategy for selecting transitions ('priority', 'random', 'weighted')
     * @param {Object} [options.transitionWeights={}] - Weights for transitions if using 'weighted' strategy
     * @param {string} [options.caseName='Case'] - Prefix for case names
     * @param {Object} [options.initialMarking=null] - Initial marking to use instead of the Petri net's default
     * @param {Array<string>} [options.startPlaces=[]] - Places that mark the beginning of a case
     * @param {Array<string>} [options.endPlaces=[]] - Places that mark the end of a case
     * @param {number} [options.seed=null] - Random seed for reproducible simulations
     */
    constructor(petriNet, options = {}) {
      this.petriNet = petriNet;

      // Set default options
      this.options = {
        startTimestamp: options.startTimestamp || new Date(),
        defaultTransitionDuration: options.defaultTransitionDuration || 1000,
        timeUnit: options.timeUnit || 'minutes',
        timeScale: options.timeScale || 1,
        caseArrivalRate: options.caseArrivalRate || 10,
        arrivalDistribution: options.arrivalDistribution || 'exponential',
        arrivalParams: options.arrivalParams || {},
        transitionSelectionStrategy: options.transitionSelectionStrategy || 'priority',
        transitionWeights: options.transitionWeights || {},
        caseName: options.caseName || 'Case',
        initialMarking: options.initialMarking || null,
        startPlaces: options.startPlaces || [],
        endPlaces: options.endPlaces || [],
        seed: options.seed || null
      };

      // Convert startTimestamp to Date object if it's a string
      if (typeof this.options.startTimestamp === 'string') {
        this.options.startTimestamp = new Date(this.options.startTimestamp);
      }
      
      // Initialize simulation state
      this.currentTimestamp = new Date(this.options.startTimestamp);
      this.activeCases = [];
      this.completedCases = [];
      this.eventLog = [];
      this.caseCounter = 1;
      
      // Initialize random number generator with seed if provided
      if (this.options.seed !== null) {
        this.random = this.createSeededRandom(this.options.seed);
      } else {
        this.random = Math.random;
      }
      
      // Automatically detect start and end places if not specified
      if (this.options.startPlaces.length === 0) {
        this.detectStartPlaces();
      }
      
      if (this.options.endPlaces.length === 0) {
        this.detectEndPlaces();
      }
    }
    



    /**
     * Creates a seeded random number generator
     * @param {number} seed - The random seed
     * @returns {Function} A function that returns random numbers
     * @private
     */
    createSeededRandom(seed) {
      return function() {
        seed = (seed * 9301 + 49297) % 233280;
        return seed / 233280;
      };
    }
    
    /**
     * Detects places that likely represent the start of a process
     * (places with initial tokens or places with no incoming arcs)
     * @private
     */
    detectStartPlaces() {
      this.options.startPlaces = [];
      
      for (const [id, place] of this.petriNet.places) {
        // Place has initial tokens
        if (place.tokens > 0) {
          this.options.startPlaces.push(id);
          continue;
        }
        
        // Place has no incoming arcs
        const hasIncomingArcs = Array.from(this.petriNet.arcs.values())
          .some(arc => arc.target === id);
        
        if (!hasIncomingArcs) {
          this.options.startPlaces.push(id);
        }
      }
    }
    
    /**
     * Detects places that likely represent the end of a process
     * (places with no outgoing arcs)
     * @private
     */
    detectEndPlaces() {
      this.options.endPlaces = [];
      
      for (const [id, place] of this.petriNet.places) {
        // Place has no outgoing arcs
        const hasOutgoingArcs = Array.from(this.petriNet.arcs.values())
          .some(arc => arc.source === id);
        
        if (!hasOutgoingArcs) {
          this.options.endPlaces.push(id);
        }
      }
    }
    
    /**
     * Creates a new simulation case
     * @returns {Object} The new case
     * @private
     */
    createCase() {
      const caseId = `${this.options.caseName}_${this.caseCounter++}`;
      const timestamp = new Date(this.currentTimestamp);
      
      // Create a deep copy of the Petri net for this case
      const net = this.clonePetriNet();
      
      // Apply initial marking if specified, otherwise use default
      if (this.options.initialMarking) {
        this.applyMarking(net, this.options.initialMarking);
      }
      
      // Initialize the case
      const newCase = {
        id: caseId,
        net: net,
        state: 'active',
        startTime: timestamp,
        endTime: null,
        currentTime: timestamp,
        steps: 0,
        events: []
      };
      
      // Log case creation event
      this.logEvent({
        case: caseId,
        activity: 'Case_Start',
        timestamp: timestamp,
        lifecycle: 'complete',
        resource: 'system',
        data: { startPlaces: this.options.startPlaces }
      });
      
      return newCase;
    }
    
    /**
     * Creates a deep clone of the Petri net
     * @returns {PetriNet} A cloned Petri net
     * @private
     */
    clonePetriNet() {
      // Create a new Petri net with the same ID, name, and description
      const clone = new PetriNet(
        this.petriNet.id,
        this.petriNet.name,
        this.petriNet.description
      );
      
      // Clone places
      for (const [id, place] of this.petriNet.places) {
        const placeClone = new Place(
          id,
          { x: place.position.x, y: place.position.y },
          place.label,
          place.tokens,
          place.capacity
        );
        clone.places.set(id, placeClone);
      }
      
      // Clone transitions
      for (const [id, transition] of this.petriNet.transitions) {
        const transitionClone = new Transition(
          id,
          { x: transition.position.x, y: transition.position.y },
          transition.label,
          transition.priority,
          transition.delay
        );
        clone.transitions.set(id, transitionClone);
      }
      
      // Clone arcs
      for (const [id, arc] of this.petriNet.arcs) {
        const arcClone = new Arc(
          id,
          arc.source,
          arc.target,
          arc.weight,
          arc.type,
          [...arc.points],
          arc.label
        );
        clone.arcs.set(id, arcClone);
      }
      
      return clone;
    }
    
    /**
     * Applies a marking to a Petri net
     * @param {PetriNet} net - The Petri net to apply the marking to
     * @param {Object} marking - Mapping of place IDs to token counts
     * @private
     */
    applyMarking(net, marking) {
      // Reset all places to 0 tokens
      for (const [id, place] of net.places) {
        place.tokens = 0;
      }
      
      // Apply the specified marking
      for (const [placeId, tokens] of Object.entries(marking)) {
        const place = net.places.get(placeId);
        if (place) {
          place.tokens = tokens;
        }
      }
    }
    
    /**
     * Logs an event in the event log
     * @param {Object} event - The event to log
     * @private
     */
    logEvent(event) {
      // Create a standardized event object
      const logEntry = {
        'case:concept:name': event.case,
        'concept:name': event.activity,
        'time:timestamp': event.timestamp.toISOString(),
        'lifecycle:transition': event.lifecycle || 'complete',
        'org:resource': event.resource || 'system'
      };
      
      // Add any additional data
      if (event.data) {
        for (const [key, value] of Object.entries(event.data)) {
          logEntry[key] = value;
        }
      }
      
      // Add to the event log
      this.eventLog.push(logEntry);
      
      // If the event is for a specific case, add it to the case events too
      if (event.case) {
        const activeCase = this.activeCases.find(c => c.id === event.case);
        if (activeCase) {
          activeCase.events.push({...logEntry});
        }
      }
    }
    
    /**
     * Calculates the next timestamp based on the transition delay
     * @param {Date} currentTime - The current timestamp
     * @param {number} delay - The delay in milliseconds
     * @returns {Date} The new timestamp
     * @private
     */
    calculateNextTimestamp(currentTime, delay) {
      const newTime = new Date(currentTime);
      const scaledDelay = delay * this.options.timeScale;
      
      switch (this.options.timeUnit) {
        case 'seconds':
          newTime.setSeconds(newTime.getSeconds() + scaledDelay / 1000);
          break;
        case 'minutes':
          newTime.setMinutes(newTime.getMinutes() + scaledDelay / 60000);
          break;
        case 'hours':
          newTime.setHours(newTime.getHours() + scaledDelay / 3600000);
          break;
        case 'days':
          newTime.setDate(newTime.getDate() + scaledDelay / 86400000);
          break;
        default:
          // Default to milliseconds
          newTime.setTime(newTime.getTime() + scaledDelay);
      }
      
      return newTime;
    }
    
    /**
     * Calculates the next arrival time for a new case
     * @returns {Date} The next arrival time
     * @private
     */
    calculateNextArrivalTime() {
      let interval;
      
      switch (this.options.arrivalDistribution) {
        case 'fixed':
          interval = this.options.caseArrivalRate;
          break;
        case 'exponential':
          // Exponential distribution with mean = caseArrivalRate
          interval = -Math.log(1 - this.random()) * this.options.caseArrivalRate;
          break;
        case 'normal':
          // Normal distribution with mean = caseArrivalRate and stddev = arrivalParams.stddev or caseArrivalRate/3
          const stddev = this.options.arrivalParams.stddev || this.options.caseArrivalRate / 3;
          let u1 = 1 - this.random();
          let u2 = 1 - this.random();
          let z = Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math.PI * u2);
          interval = this.options.caseArrivalRate + z * stddev;
          interval = Math.max(0.1, interval); // Ensure positive interval
          break;
        default:
          interval = this.options.caseArrivalRate;
      }
      
      return this.calculateNextTimestamp(this.currentTimestamp, interval * 60000); // Convert to milliseconds
    }
    
    /**
     * Selects the next transition to fire for a case
     * @param {Object} simulationCase - The simulation case
     * @returns {string|null} The ID of the selected transition, or null if none is enabled
     * @private
     */
    selectNextTransition(simulationCase) {
      const net = simulationCase.net;
      net.updateEnabledTransitions();
      
      // Get all enabled transitions
      const enabledTransitions = [];
      for (const [id, transition] of net.transitions) {
        if (transition.isEnabled) {
          enabledTransitions.push(id);
        }
      }
      
      if (enabledTransitions.length === 0) {
        return null;
      }
      
      // Select according to the configured strategy
      switch (this.options.transitionSelectionStrategy) {
        case 'priority':
          // Sort by priority (highest first)
          enabledTransitions.sort((a, b) => {
            const transA = net.transitions.get(a);
            const transB = net.transitions.get(b);
            return (transB?.priority || 0) - (transA?.priority || 0);
          });
          return enabledTransitions[0];
          
        case 'random':
          // Select a random transition with equal probability
          const randomIndex = Math.floor(this.random() * enabledTransitions.length);
          return enabledTransitions[randomIndex];
          
        case 'weighted':
          // Select based on weights
          const weights = this.options.transitionWeights;
          
          // Calculate total weight
          let totalWeight = 0;
          const transitionWeights = enabledTransitions.map(id => {
            const weight = weights[id] || 1;
            totalWeight += weight;
            return { id, weight };
          });
          
          // Select based on weighted probability
          let randomValue = this.random() * totalWeight;
          for (const { id, weight } of transitionWeights) {
            randomValue -= weight;
            if (randomValue <= 0) {
              return id;
            }
          }
          
          // Fallback to first transition
          return enabledTransitions[0];
          
        default:
          return enabledTransitions[0];
      }
    }
    
    /**
     * Checks if a case is complete
     * @param {Object} simulationCase - The simulation case
     * @returns {boolean} True if the case is complete, false otherwise
     * @private
     */
    isCaseComplete(simulationCase) {
      const net = simulationCase.net;
      
      // Case is complete if any of the end places has at least one token
      for (const placeId of this.options.endPlaces) {
        const place = net.places.get(placeId);
        if (place && place.tokens > 0) {
          return true;
        }
      }
      
      // Case is also complete if no transitions are enabled (deadlock)
      net.updateEnabledTransitions();
      let hasEnabledTransitions = false;
      for (const [, transition] of net.transitions) {
        if (transition.isEnabled) {
          hasEnabledTransitions = true;
          break;
        }
      }
      
      return !hasEnabledTransitions;
    }
    
    /**
     * Processes a single step for a simulation case
     * @param {Object} simulationCase - The simulation case
     * @returns {boolean} True if the case is still active, false if it's complete
     * @private
     */
    processCase(simulationCase) {
      // Check if the case is already complete
      if (simulationCase.state === 'complete') {
        return false;
      }
      
      // Select the next transition to fire
      const transitionId = this.selectNextTransition(simulationCase);
      
      if (!transitionId) {
        // No transitions can fire, check if case is complete
        if (this.isCaseComplete(simulationCase)) {
          this.completeCase(simulationCase);
          return false;
        }
        return true; // Case is not complete but stuck (deadlock)
      }
      
      // Get the transition
      const transition = simulationCase.net.transitions.get(transitionId);
      const transitionName = transition.label || transitionId;
      
      // Log transition start event
      this.logEvent({
        case: simulationCase.id,
        activity: transitionName,
        timestamp: new Date(simulationCase.currentTime),
        lifecycle: 'start',
        resource: 'system',
        data: { transitionId }
      });
      
      // Calculate duration - use transition delay or default
      const duration = transition.delay || this.options.defaultTransitionDuration;
      
      // Fire the transition
      simulationCase.net.fireTransition(transitionId);
      simulationCase.steps++;
      
      // Update timestamp
      const completionTime = this.calculateNextTimestamp(simulationCase.currentTime, duration);
      simulationCase.currentTime = completionTime;
      
      // Log transition complete event
      this.logEvent({
        case: simulationCase.id,
        activity: transitionName,
        timestamp: new Date(completionTime),
        lifecycle: 'complete',
        resource: 'system',
        data: { 
          transitionId,
          duration,
          step: simulationCase.steps 
        }
      });
      
      // Check if the case is now complete
      if (this.isCaseComplete(simulationCase)) {
        this.completeCase(simulationCase);
        return false;
      }
      
      return true;
    }
    
    /**
     * Marks a case as complete
     * @param {Object} simulationCase - The simulation case to complete
     * @private
     */
    completeCase(simulationCase) {
      simulationCase.state = 'complete';
      simulationCase.endTime = new Date(simulationCase.currentTime);
      
      // Log case completion event
      this.logEvent({
        case: simulationCase.id,
        activity: 'Case_End',
        timestamp: simulationCase.endTime,
        lifecycle: 'complete',
        resource: 'system',
        data: { 
          duration: simulationCase.endTime - simulationCase.startTime,
          steps: simulationCase.steps
        }
      });
      
      // Move from active to completed cases
      const index = this.activeCases.findIndex(c => c.id === simulationCase.id);
      if (index !== -1) {
        const [completedCase] = this.activeCases.splice(index, 1);
        this.completedCases.push(completedCase);
      }
    }
    
    /**
     * Runs the simulation for a specific number of cases
     * @param {number} numCases - Number of cases to simulate
     * @param {number} maxSteps - Maximum number of steps per case (optional)
     * @returns {Array} The generated event log
     */
    simulateCases(numCases, maxSteps = 1000) {
      // Reset simulation state
      this.activeCases = [];
      this.completedCases = [];
      this.eventLog = [];
      this.caseCounter = 1;
      this.currentTimestamp = new Date(this.options.startTimestamp);
      
      // Create initial case
      const firstCase = this.createCase();
      this.activeCases.push(firstCase);
      
      // Calculate arrival times for all cases
      const caseArrivals = [{ time: this.currentTimestamp, caseNum: 1 }];
      
      for (let i = 2; i <= numCases; i++) {
        const arrivalTime = this.calculateNextArrivalTime();
        caseArrivals.push({ time: arrivalTime, caseNum: i });
        this.currentTimestamp = arrivalTime;
      }
      
      // Sort arrivals by time
      caseArrivals.sort((a, b) => a.time - b.time);
      
      // Simulation loop
      let nextArrivalIndex = 1; // Skip the first one which we already created
      
      while (this.activeCases.length > 0 || nextArrivalIndex < caseArrivals.length) {
        // Find the next event time (either case step or new arrival)
        let nextEventTime = null;
        
        // Find the earliest active case time
        for (const activeCase of this.activeCases) {
          if (!nextEventTime || activeCase.currentTime < nextEventTime) {
            nextEventTime = activeCase.currentTime;
          }
        }
        
        // Check if next arrival is earlier
        const nextArrival = caseArrivals[nextArrivalIndex];
        if (nextArrival && (!nextEventTime || nextArrival.time < nextEventTime)) {
          // Process new case arrival
          this.currentTimestamp = nextArrival.time;
          const newCase = this.createCase();
          this.activeCases.push(newCase);
          nextArrivalIndex++;
          continue;
        }
        
        // Process the case with the earliest time
        this.currentTimestamp = nextEventTime;
        
        // Find the case with the earliest time
        const earliestCaseIndex = this.activeCases.findIndex(
          c => c.currentTime.getTime() === nextEventTime.getTime()
        );
        
        const currentCase = this.activeCases[earliestCaseIndex];
        
        // Process one step for this case
        if (currentCase.steps < maxSteps) {
          const isActive = this.processCase(currentCase);
          
          // If case is complete, it's already been moved to completedCases
          if (!isActive) {
            // No need to remove from activeCases, it's done in completeCase method
          }
        } else {
          // Max steps reached, force complete the case
          this.completeCase(currentCase);
        }
      }
      
      return this.eventLog;
    }
    
    /**
     * Exports the event log to CSV format
     * @returns {string} CSV formatted event log
     */
    exportToCSV() {
      if (this.eventLog.length === 0) {
        return '';
      }
      
      // Get all unique headers
      const headers = new Set();
      this.eventLog.forEach(event => {
        Object.keys(event).forEach(key => headers.add(key));
      });
      
      const headerRow = Array.from(headers).join(',');
      const rows = [headerRow];
      
      // Add each event
      this.eventLog.forEach(event => {
        const row = Array.from(headers).map(header => {
          const value = event[header] || '';
          // Handle commas and quotes in values
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
     * Exports the event log to XES (XML) format
     * @returns {string} XES formatted event log
     */
    exportToXES() {
      const xesHeader = `<?xml version="1.0" encoding="UTF-8" ?>
  <log xes.version="1.0" xmlns="http://www.xes-standard.org/">
    <extension name="Concept" prefix="concept" uri="http://www.xes-standard.org/concept.xesext"/>
    <extension name="Time" prefix="time" uri="http://www.xes-standard.org/time.xesext"/>
    <extension name="Organizational" prefix="org" uri="http://www.xes-standard.org/org.xesext"/>
    <extension name="Lifecycle" prefix="lifecycle" uri="http://www.xes-standard.org/lifecycle.xesext"/>
    <classifier name="Activity" keys="concept:name"/>
    <classifier name="Resource" keys="org:resource"/>
    <string key="concept:name" value="${this.petriNet.name || 'Petri Net Simulation'}"/>
    <string key="source" value="PetriNetSimulator"/>`;
      
      // Group events by case
      const eventsByCase = {};
      
      this.eventLog.forEach(event => {
        const caseId = event['case:concept:name'];
        if (!eventsByCase[caseId]) {
          eventsByCase[caseId] = [];
        }
        eventsByCase[caseId].push(event);
      });
      
      let traces = '';
      
      // Process each case as a trace
      for (const [caseId, events] of Object.entries(eventsByCase)) {
        traces += `\n  <trace>
      <string key="concept:name" value="${caseId}"/>`;
        
        // Add events to trace
        events.forEach(event => {
          traces += `\n    <event>`;
          for (const [key, value] of Object.entries(event)) {
            const escapedValue = value.toString()
              .replace(/&/g, '&amp;')
              .replace(/</g, '&lt;')
              .replace(/>/g, '&gt;')
              .replace(/"/g, '&quot;')
              .replace(/'/g, '&apos;');
            
            if (key === 'time:timestamp') {
              traces += `\n      <date key="${key}" value="${escapedValue}"/>`;
            } else {
              traces += `\n      <string key="${key}" value="${escapedValue}"/>`;
            }
          }
          traces += `\n    </event>`;
        });
        
        traces += `\n  </trace>`;
      }
      
      return xesHeader + traces + '\n</log>';
    }
    
    /**
     * Exports the event log to JSON format
     * @returns {string} JSON formatted event log
     */
    exportToJSON() {
      return JSON.stringify(this.eventLog, null, 2);
    }
    
    /**
     * Gets statistics about the simulation
     * @returns {Object} Simulation statistics
     */
    getStatistics() {
      // Calculate basic statistics
      const totalCases = this.completedCases.length;
      const totalEvents = this.eventLog.length;
      
      // Case duration statistics
      const caseDurations = this.completedCases.map(c => c.endTime - c.startTime);
      const avgCaseDuration = caseDurations.reduce((sum, d) => sum + d, 0) / totalCases;
      
      // Calculate min, max, median durations
      const sortedDurations = [...caseDurations].sort((a, b) => a - b);
      const minDuration = sortedDurations[0];
      const maxDuration = sortedDurations[sortedDurations.length - 1];
      const medianDuration = sortedDurations[Math.floor(sortedDurations.length / 2)];
      
      // Activity frequency
      const activityFrequency = {};
      this.eventLog.forEach(event => {
        const activity = event['concept:name'];
        activityFrequency[activity] = (activityFrequency[activity] || 0) + 1;
      });
      
      // Average case length (number of events)
      const caseLength = {};
      for (const event of this.eventLog) {
        const caseId = event['case:concept:name'];
        if (!event['concept:name'].startsWith('Case_')) {
          caseLength[caseId] = (caseLength[caseId] || 0) + 1;
        }
      }
      
      const caseLengths = Object.values(caseLength);
      const avgCaseLength = caseLengths.reduce((sum, len) => sum + len, 0) / Object.keys(caseLength).length;
      
      return {
        totalCases,
        totalEvents,
        avgCaseDuration,
        minDuration,
        maxDuration,
        medianDuration,
        activityFrequency,
        avgCaseLength
      };
    }
  }