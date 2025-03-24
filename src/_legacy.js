  /**
   * Creates a dining philosophers Petri net
   */
  createDiningPhilosophers() {
    const api = new PetriNetAPI();
    const numPhilosophers = 3; // Use 3 for simplicity
    
    // Create places for forks
    const forks = [];
    for (let i = 0; i < numPhilosophers; i++) {
      forks.push(api.createPlace(
        150 + 120 * Math.cos(2 * Math.PI * i / numPhilosophers),
        150 + 120 * Math.sin(2 * Math.PI * i / numPhilosophers),
        `Fork ${i + 1}`, 1
      ));
    }
    
    // Create places and transitions for philosophers
    for (let i = 0; i < numPhilosophers; i++) {
      const angle1 = 2 * Math.PI * i / numPhilosophers;
      const angle2 = 2 * Math.PI * ((i + 1) % numPhilosophers) / numPhilosophers;
      const midAngle = (angle1 + angle2) / 2;
      
      // Places
      const thinking = api.createPlace(
        300 + 180 * Math.cos(midAngle),
        300 + 180 * Math.sin(midAngle),
        `P${i + 1} Thinking`, 1
      );
      
      const eating = api.createPlace(
        300 + 120 * Math.cos(midAngle),
        300 + 120 * Math.sin(midAngle),
        `P${i + 1} Eating`, 0
      );
      
      // Transitions
      const pickUp = api.createTransition(
        300 + 150 * Math.cos(midAngle - 0.1),
        300 + 150 * Math.sin(midAngle - 0.1),
        `P${i + 1} Pick Up`
      );
      
      const putDown = api.createTransition(
        300 + 150 * Math.cos(midAngle + 0.1),
        300 + 150 * Math.sin(midAngle + 0.1),
        `P${i + 1} Put Down`
      );
      
      // Arcs
      api.createArc(thinking, pickUp);
      api.createArc(forks[i], pickUp);
      api.createArc(forks[(i + 1) % numPhilosophers], pickUp);
      api.createArc(pickUp, eating);
      
      api.createArc(eating, putDown);
      api.createArc(putDown, thinking);
      api.createArc(putDown, forks[i]);
      api.createArc(putDown, forks[(i + 1) % numPhilosophers]);
    }
    
    return api;
  }

    // Example builder methods
    static createSimpleProducerConsumer() {
      const api = new PetriNetAPI();
  
      // Create places
      const producer = api.createPlace(50, 100, "Producer", 1);
      const buffer = api.createPlace(200, 100, "Buffer", 0);
      const consumer = api.createPlace(350, 100, "Consumer", 0);
  
      // Create transitions
      const produce = api.createTransition(125, 100, "Produce");
      const consume = api.createTransition(275, 100, "Consume");
  
      // Create arcs
      api.createArc(producer, produce);
      api.createArc(produce, producer);
      api.createArc(produce, buffer);
      api.createArc(buffer, consume);
      api.createArc(consume, consumer);
  
      return api;
    }
  
    static createMutualExclusion() {
      const api = new PetriNetAPI();
  
      // Create places
      const p1Ready = api.createPlace(50, 50, "P1 Ready", 1);
      const p2Ready = api.createPlace(350, 50, "P2 Ready", 1);
      const critical = api.createPlace(200, 150, "Critical Section", 1);
      const p1CS = api.createPlace(100, 250, "P1 in CS", 0);
      const p2CS = api.createPlace(300, 250, "P2 in CS", 0);
  
      // Create transitions
      const p1Enter = api.createTransition(100, 100, "P1 Enter");
      const p1Exit = api.createTransition(100, 200, "P1 Exit");
      const p2Enter = api.createTransition(300, 100, "P2 Enter");
      const p2Exit = api.createTransition(300, 200, "P2 Exit");
  
      // Create arcs
      api.createArc(p1Ready, p1Enter);
      api.createArc(critical, p1Enter);
      api.createArc(p1Enter, p1CS);
      api.createArc(p1CS, p1Exit);
      api.createArc(p1Exit, critical);
      api.createArc(p1Exit, p1Ready);
  
      api.createArc(p2Ready, p2Enter);
      api.createArc(critical, p2Enter);
      api.createArc(p2Enter, p2CS);
      api.createArc(p2CS, p2Exit);
      api.createArc(p2Exit, critical);
      api.createArc(p2Exit, p2Ready);
  
      return api;
    }
  