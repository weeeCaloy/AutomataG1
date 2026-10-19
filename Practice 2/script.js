/* =============================================
   SMART CALCULATOR & EXPRESSION PARSER
   Core Engine: DFA Lexer → PDA Parser → TM Evaluator
   ============================================= */

// ========== STAGE 1: Deterministic Finite Automaton (Lexer) ==========

/**
 * DFA States for lexical analysis.
 * The DFA recognizes: numbers (int/decimal), operators, parentheses.
 */
const DFA_STATES = {
  START: 'START',
  INTEGER: 'INTEGER',
  DECIMAL: 'DECIMAL',
  OPERATOR: 'OPERATOR',
  LPAREN: 'LPAREN',
  RPAREN: 'RPAREN',
  ERROR: 'ERROR'
};

/**
 * Token types produced by the DFA.
 */
const TOKEN_TYPES = {
  NUMBER: 'NUMBER',
  OPERATOR: 'OPERATOR',
  LPAREN: 'LPAREN',
  RPAREN: 'RPAREN'
};

/**
 * Character classification for DFA transitions.
 */
function classifyChar(ch) {
  if (ch >= '0' && ch <= '9') return 'DIGIT';
  if (ch === '.') return 'DOT';
  if ('+-*/'.includes(ch)) return 'OPERATOR';
  if (ch === '(') return 'LPAREN';
  if (ch === ')') return 'RPAREN';
  if (ch === ' ' || ch === '\t') return 'WHITESPACE';
  return 'UNKNOWN';
}

/**
 * DFA Transition Table.
 * Maps (state, charClass) → nextState.
 */
const DFA_TRANSITIONS = {
  START: {
    DIGIT: DFA_STATES.INTEGER,
    DOT: DFA_STATES.DECIMAL,
    OPERATOR: DFA_STATES.OPERATOR,
    LPAREN: DFA_STATES.LPAREN,
    RPAREN: DFA_STATES.RPAREN,
    WHITESPACE: DFA_STATES.START,
    UNKNOWN: DFA_STATES.ERROR
  },
  INTEGER: {
    DIGIT: DFA_STATES.INTEGER,
    DOT: DFA_STATES.DECIMAL,
    OPERATOR: null,  // Emit token, restart
    LPAREN: null,
    RPAREN: null,
    WHITESPACE: null,
    UNKNOWN: DFA_STATES.ERROR
  },
  DECIMAL: {
    DIGIT: DFA_STATES.DECIMAL,
    DOT: DFA_STATES.ERROR,
    OPERATOR: null,
    LPAREN: null,
    RPAREN: null,
    WHITESPACE: null,
    UNKNOWN: DFA_STATES.ERROR
  }
};

/**
 * DFA-based Lexer.
 * Scans input character-by-character, producing tokens.
 * Returns an array of tokens with type, value, and DFA trace.
 */
function dfaLexer(input) {
  const tokens = [];
  const trace = [];  // Records state transitions for visualization
  let state = DFA_STATES.START;
  let buffer = '';
  let i = 0;

  while (i <= input.length) {
    const ch = i < input.length ? input[i] : null;
    const charClass = ch !== null ? classifyChar(ch) : 'END';

    trace.push({
      position: i,
      char: ch,
      charClass: charClass,
      stateBefore: state
    });

    if (state === DFA_STATES.START) {
      if (charClass === 'DIGIT') {
        state = DFA_STATES.INTEGER;
        buffer = ch;
      } else if (charClass === 'DOT') {
        state = DFA_STATES.DECIMAL;
        buffer = '0.';
      } else if (charClass === 'OPERATOR') {
        tokens.push({ type: TOKEN_TYPES.OPERATOR, value: ch });
        trace[trace.length - 1].stateAfter = DFA_STATES.OPERATOR;
        trace[trace.length - 1].emitted = { type: TOKEN_TYPES.OPERATOR, value: ch };
        state = DFA_STATES.START;
      } else if (charClass === 'LPAREN') {
        tokens.push({ type: TOKEN_TYPES.LPAREN, value: '(' });
        trace[trace.length - 1].stateAfter = DFA_STATES.LPAREN;
        trace[trace.length - 1].emitted = { type: TOKEN_TYPES.LPAREN, value: '(' };
        state = DFA_STATES.START;
      } else if (charClass === 'RPAREN') {
        tokens.push({ type: TOKEN_TYPES.RPAREN, value: ')' });
        trace[trace.length - 1].stateAfter = DFA_STATES.RPAREN;
        trace[trace.length - 1].emitted = { type: TOKEN_TYPES.RPAREN, value: ')' };
        state = DFA_STATES.START;
      } else if (charClass === 'WHITESPACE') {
        // Stay in START
      } else if (charClass === 'END') {
        break;
      } else {
        throw new Error(`Unexpected character '${ch}' at position ${i}`);
      }
      trace[trace.length - 1].stateAfter = state;
      i++;
      continue;
    }

    if (state === DFA_STATES.INTEGER) {
      if (charClass === 'DIGIT') {
        buffer += ch;
        trace[trace.length - 1].stateAfter = DFA_STATES.INTEGER;
        i++;
        continue;
      } else if (charClass === 'DOT') {
        buffer += ch;
        state = DFA_STATES.DECIMAL;
        trace[trace.length - 1].stateAfter = DFA_STATES.DECIMAL;
        i++;
        continue;
      } else {
        // Emit number token
        tokens.push({ type: TOKEN_TYPES.NUMBER, value: buffer });
        trace[trace.length - 1].emitted = { type: TOKEN_TYPES.NUMBER, value: buffer };
        buffer = '';
        state = DFA_STATES.START;
        trace[trace.length - 1].stateAfter = DFA_STATES.START;
        // Don't advance i — re-process this character
        continue;
      }
    }

    if (state === DFA_STATES.DECIMAL) {
      if (charClass === 'DIGIT') {
        buffer += ch;
        trace[trace.length - 1].stateAfter = DFA_STATES.DECIMAL;
        i++;
        continue;
      } else if (charClass === 'DOT') {
        throw new Error(`Unexpected second decimal point at position ${i}`);
      } else {
        // Emit decimal number token
        tokens.push({ type: TOKEN_TYPES.NUMBER, value: buffer });
        trace[trace.length - 1].emitted = { type: TOKEN_TYPES.NUMBER, value: buffer };
        buffer = '';
        state = DFA_STATES.START;
        trace[trace.length - 1].stateAfter = DFA_STATES.START;
        continue;
      }
    }

    i++;
  }

  // Handle any remaining buffer
  if (buffer.length > 0) {
    tokens.push({ type: TOKEN_TYPES.NUMBER, value: buffer });
  }

  return { tokens, trace };
}


// ========== STAGE 2: Pushdown Automaton (Parser — Shunting-Yard) ==========

/**
 * Operator precedence and associativity for the PDA.
 */
const OPERATORS = {
  '+': { precedence: 1, associativity: 'left' },
  '-': { precedence: 1, associativity: 'left' },
  '*': { precedence: 2, associativity: 'left' },
  '/': { precedence: 2, associativity: 'left' }
};

/**
 * PDA-based Shunting-Yard Parser.
 * Converts infix token stream to postfix (Reverse Polish Notation).
 * Uses a stack (pushdown memory) for operator management.
 * Returns postfix array and step-by-step trace.
 */
function pdaParser(tokens) {
  const outputQueue = [];
  const operatorStack = [];   // The PDA's pushdown stack
  const steps = [];           // Trace for visualization

  for (const token of tokens) {
    if (token.type === TOKEN_TYPES.NUMBER) {
      outputQueue.push(token);
      steps.push({
        action: 'enqueue',
        token: token,
        description: `Number ${token.value} → Output Queue`,
        stack: [...operatorStack],
        output: [...outputQueue]
      });
    }
    else if (token.type === TOKEN_TYPES.OPERATOR) {
      const op = OPERATORS[token.value];

      while (
        operatorStack.length > 0 &&
        operatorStack[operatorStack.length - 1].type !== TOKEN_TYPES.LPAREN &&
        OPERATORS[operatorStack[operatorStack.length - 1].value] &&
        (
          OPERATORS[operatorStack[operatorStack.length - 1].value].precedence > op.precedence ||
          (OPERATORS[operatorStack[operatorStack.length - 1].value].precedence === op.precedence &&
           op.associativity === 'left')
        )
      ) {
        const popped = operatorStack.pop();
        outputQueue.push(popped);
        steps.push({
          action: 'pop-to-output',
          token: popped,
          description: `Pop ${popped.value} from Stack → Output (higher precedence)`,
          stack: [...operatorStack],
          output: [...outputQueue]
        });
      }

      operatorStack.push(token);
      steps.push({
        action: 'push',
        token: token,
        description: `Push ${token.value} → Operator Stack`,
        stack: [...operatorStack],
        output: [...outputQueue]
      });
    }
    else if (token.type === TOKEN_TYPES.LPAREN) {
      operatorStack.push(token);
      steps.push({
        action: 'push',
        token: token,
        description: `Push ( → Operator Stack`,
        stack: [...operatorStack],
        output: [...outputQueue]
      });
    }
    else if (token.type === TOKEN_TYPES.RPAREN) {
      let foundLParen = false;
      while (operatorStack.length > 0) {
        if (operatorStack[operatorStack.length - 1].type === TOKEN_TYPES.LPAREN) {
          operatorStack.pop();
          foundLParen = true;
          steps.push({
            action: 'discard-paren',
            token: token,
            description: `Matched parentheses — discard ( from Stack`,
            stack: [...operatorStack],
            output: [...outputQueue]
          });
          break;
        }
        const popped = operatorStack.pop();
        outputQueue.push(popped);
        steps.push({
          action: 'pop-to-output',
          token: popped,
          description: `Pop ${popped.value} from Stack → Output (closing paren)`,
          stack: [...operatorStack],
          output: [...outputQueue]
        });
      }
      if (!foundLParen) {
        throw new Error('Mismatched parentheses: extra closing parenthesis');
      }
    }
  }

  // Pop remaining operators from stack
  while (operatorStack.length > 0) {
    const top = operatorStack[operatorStack.length - 1];
    if (top.type === TOKEN_TYPES.LPAREN) {
      throw new Error('Mismatched parentheses: unclosed opening parenthesis');
    }
    const popped = operatorStack.pop();
    outputQueue.push(popped);
    steps.push({
      action: 'pop-remaining',
      token: popped,
      description: `Pop remaining ${popped.value} → Output`,
      stack: [...operatorStack],
      output: [...outputQueue]
    });
  }

  return { postfix: outputQueue, steps };
}


// ========== STAGE 3: Turing Machine (Evaluator) ==========

/**
 * Turing Machine Evaluator.
 * Reads postfix tokens from the tape, evaluates using a value stack.
 * The TM head moves right across the tape, processing one cell at a time.
 * Returns the final result and computation trace.
 */
function tmEvaluator(postfix) {
  // Initialize the TM tape with postfix tokens
  const tape = postfix.map(t => ({ ...t, processed: false }));

  // Add blank cells at the end
  tape.push({ type: 'BLANK', value: '□', processed: false });
  tape.push({ type: 'BLANK', value: '□', processed: false });

  const valueStack = [];     // Evaluation stack
  const computationSteps = [];
  let headPosition = 0;      // TM head position
  let stepCount = 0;
  let tmState = 'q_read';    // TM states: q_read, q_eval, q_accept

  while (headPosition < tape.length) {
    const cell = tape[headPosition];
    stepCount++;

    if (cell.type === 'BLANK') {
      // Reached blank — enter accept state
      tmState = 'q_accept';
      computationSteps.push({
        step: stepCount,
        state: tmState,
        headPosition: headPosition,
        action: `HALT — Read blank cell`,
        stack: [...valueStack],
        description: `Tape exhausted. Final result on stack.`
      });
      break;
    }

    if (cell.type === TOKEN_TYPES.NUMBER) {
      tmState = 'q_read';
      const num = parseFloat(cell.value);
      valueStack.push(num);
      cell.processed = true;

      computationSteps.push({
        step: stepCount,
        state: tmState,
        headPosition: headPosition,
        action: `READ ${cell.value}`,
        stack: [...valueStack],
        description: `Push ${cell.value} onto value stack`
      });
    }
    else if (cell.type === TOKEN_TYPES.OPERATOR) {
      tmState = 'q_eval';

      if (valueStack.length < 2) {
        throw new Error(`Insufficient operands for operator '${cell.value}'`);
      }

      const b = valueStack.pop();
      const a = valueStack.pop();
      let result;

      switch (cell.value) {
        case '+': result = a + b; break;
        case '-': result = a - b; break;
        case '*': result = a * b; break;
        case '/':
          if (b === 0) throw new Error('Division by zero');
          result = a / b;
          break;
        default:
          throw new Error(`Unknown operator '${cell.value}'`);
      }

      // Round to avoid floating-point artifacts
      result = Math.round(result * 1e10) / 1e10;

      valueStack.push(result);
      cell.processed = true;

      computationSteps.push({
        step: stepCount,
        state: tmState,
        headPosition: headPosition,
        action: `EVAL ${a} ${cell.value} ${b}`,
        stack: [...valueStack],
        description: `${a} ${cell.value} ${b} = ${result}`
      });
    }

    // Move head right
    headPosition++;
  }

  if (valueStack.length !== 1) {
    throw new Error('Invalid expression: multiple values remaining after evaluation');
  }

  const finalResult = valueStack[0];

  return { result: finalResult, tape, computationSteps };
}


// ========== UI CONTROLLER ==========

class CalculatorUI {
  constructor() {
    this.input = document.getElementById('expressionInput');
    this.parseBtn = document.getElementById('parseBtn');
    this.tokenStream = document.getElementById('tokenStream');
    this.postfixOutput = document.getElementById('postfixOutput');
    this.resultDisplay = document.getElementById('resultDisplay');
    this.errorCard = document.getElementById('errorCard');
    this.errorMessage = document.getElementById('errorMessage');
    this.progressBar = document.getElementById('progressBar');

    // PDA elements
    this.pdaVisual = document.getElementById('pdaVisual');
    this.pdaInputQueue = document.getElementById('pdaInputQueue');
    this.pdaStack = document.getElementById('pdaStack');
    this.pdaOutputQueue = document.getElementById('pdaOutputQueue');

    // TM elements
    this.tmVisual = document.getElementById('tmVisual');
    this.tmTape = document.getElementById('tmTape');
    this.tmSteps = document.getElementById('tmSteps');

    // Stage cards
    this.stage1Card = document.getElementById('stage1Card');
    this.stage2Card = document.getElementById('stage2Card');
    this.stage3Card = document.getElementById('stage3Card');

    // Step indicators
    this.step1 = document.getElementById('step1Indicator');
    this.step2 = document.getElementById('step2Indicator');
    this.step3 = document.getElementById('step3Indicator');

    this.bindEvents();
    this.initSections();
  }

  bindEvents() {
    this.parseBtn.addEventListener('click', () => this.processExpression());
    this.input.addEventListener('keydown', (e) => {
      if (e.key === 'Enter') this.processExpression();
    });

    // Quick example buttons
    document.querySelectorAll('.quick-btn').forEach(btn => {
      btn.addEventListener('click', () => {
        this.input.value = btn.dataset.expr;
        this.input.focus();
        this.processExpression();
      });
    });

    // Example cards
    document.querySelectorAll('.example-card').forEach(card => {
      card.addEventListener('click', () => {
        const expr = card.dataset.expr;
        this.input.value = expr;

        // Switch to calculator view
        this.switchSection('calculator');
        document.querySelectorAll('.nav-pill').forEach(p => p.classList.remove('active'));
        document.querySelector('[data-section="calculator"]').classList.add('active');

        setTimeout(() => this.processExpression(), 300);
      });
    });

    // Nav pills
    document.querySelectorAll('.nav-pill').forEach(pill => {
      pill.addEventListener('click', () => {
        document.querySelectorAll('.nav-pill').forEach(p => p.classList.remove('active'));
        pill.classList.add('active');
        this.switchSection(pill.dataset.section);
      });
    });
  }

  initSections() {
    // Show calculator by default
    this.switchSection('calculator');
  }

  switchSection(section) {
    const calcSections = document.querySelectorAll('.hero, .pipeline-section');
    const theorySection = document.getElementById('theory');
    const examplesSection = document.getElementById('examples');

    calcSections.forEach(el => el.style.display = section === 'calculator' ? '' : 'none');
    theorySection.style.display = section === 'theory' ? '' : 'none';
    examplesSection.style.display = section === 'examples' ? '' : 'none';
  }

  resetUI() {
    this.tokenStream.innerHTML = '<div class="token-placeholder">Processing...</div>';
    this.postfixOutput.innerHTML = '<div class="token-placeholder">Processing...</div>';
    this.resultDisplay.innerHTML = '<div class="token-placeholder">Processing...</div>';
    this.errorCard.style.display = 'none';
    this.progressBar.style.width = '0%';

    // Reset PDA
    this.pdaInputQueue.innerHTML = '';
    this.pdaStack.innerHTML = '<div class="stack-bottom">⊥</div>';
    this.pdaOutputQueue.innerHTML = '';
    this.pdaVisual.querySelector('.pda-placeholder').style.display = 'block';
    this.pdaVisual.querySelector('.pda-columns').classList.remove('visible');

    // Reset TM
    this.tmTape.innerHTML = '';
    this.tmSteps.innerHTML = '';
    this.tmVisual.querySelector('.tm-placeholder').style.display = 'block';
    this.tmVisual.querySelector('.tm-tape-container').classList.remove('visible');
    this.tmSteps.classList.remove('visible');

    // Reset stage cards
    [this.stage1Card, this.stage2Card, this.stage3Card].forEach(card => {
      card.classList.remove('active', 'done');
    });

    // Reset step indicators
    [this.step1, this.step2, this.step3].forEach(step => {
      step.classList.remove('active', 'done');
    });

    // Reset DFA highlights
    document.querySelectorAll('.dfa-state.highlight, .dfa-transition.highlight').forEach(el => {
      el.classList.remove('highlight');
    });
  }

  showError(message) {
    this.errorCard.style.display = 'flex';
    this.errorMessage.textContent = message;
  }

  async processExpression() {
    const expression = this.input.value.trim();
    if (!expression) {
      this.input.focus();
      return;
    }

    this.resetUI();

    try {
      // ---- STAGE 1: DFA Lexer ----
      await this.animateStage1(expression);

      const { tokens, trace } = dfaLexer(expression);
      await this.renderTokens(tokens, trace);
      this.markStageDone(1);

      // ---- STAGE 2: PDA Parser ----
      await this.animateStage2(tokens);

      const { postfix, steps } = pdaParser(tokens);
      await this.renderPDA(tokens, steps, postfix);
      this.markStageDone(2);

      // ---- STAGE 3: TM Evaluator ----
      await this.animateStage3(postfix);

      const { result, tape, computationSteps } = tmEvaluator(postfix);
      await this.renderTM(tape, computationSteps, result, expression);
      this.markStageDone(3);

    } catch (error) {
      this.showError(error.message);
    }
  }

  // ---------- Stage Animation Helpers ----------

  activateStage(num) {
    const card = [this.stage1Card, this.stage2Card, this.stage3Card][num - 1];
    const step = [this.step1, this.step2, this.step3][num - 1];
    card.classList.add('active');
    step.classList.add('active');
  }

  markStageDone(num) {
    const card = [this.stage1Card, this.stage2Card, this.stage3Card][num - 1];
    const step = [this.step1, this.step2, this.step3][num - 1];
    card.classList.remove('active');
    card.classList.add('done');
    step.classList.remove('active');
    step.classList.add('done');
    this.progressBar.style.width = `${(num / 3) * 100}%`;
  }

  sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  // ---------- Stage 1: DFA Visualization ----------

  async animateStage1(expression) {
    this.activateStage(1);
    await this.sleep(200);

    // Animate DFA state transitions
    const stateMap = {
      START: 'dfaStateStart',
      INTEGER: 'dfaStateInt',
      DECIMAL: 'dfaStateDec',
      OPERATOR: 'dfaStateOp',
      LPAREN: 'dfaStateLP',
      RPAREN: 'dfaStateRP'
    };

    // Brief highlight of START state
    const startEl = document.getElementById('dfaStateStart');
    if (startEl) {
      startEl.classList.add('highlight');
      await this.sleep(300);
      startEl.classList.remove('highlight');
    }
  }

  async renderTokens(tokens, trace) {
    this.tokenStream.innerHTML = '';

    for (let i = 0; i < tokens.length; i++) {
      const token = tokens[i];
      const chip = document.createElement('div');

      let cssClass = 'number';
      let typeLabel = 'NUM';

      if (token.type === TOKEN_TYPES.OPERATOR) {
        cssClass = 'operator';
        typeLabel = 'OP';
      } else if (token.type === TOKEN_TYPES.LPAREN) {
        cssClass = 'lparen';
        typeLabel = 'LP';
      } else if (token.type === TOKEN_TYPES.RPAREN) {
        cssClass = 'rparen';
        typeLabel = 'RP';
      }

      chip.className = `token-chip ${cssClass}`;
      chip.style.animationDelay = `${i * 80}ms`;
      chip.innerHTML = `
        <span class="token-type">${typeLabel}</span>
        <span>${token.value}</span>
      `;

      this.tokenStream.appendChild(chip);

      // Highlight corresponding DFA state
      const stateId = {
        NUMBER: 'dfaStateInt',
        OPERATOR: 'dfaStateOp',
        LPAREN: 'dfaStateLP',
        RPAREN: 'dfaStateRP'
      }[token.type];

      if (stateId) {
        const stateEl = document.getElementById(stateId);
        if (stateEl) {
          stateEl.classList.add('highlight');
          await this.sleep(120);
          stateEl.classList.remove('highlight');
        }
      }
    }

    await this.sleep(200);
  }

  // ---------- Stage 2: PDA Visualization ----------

  async animateStage2(tokens) {
    this.activateStage(2);
    await this.sleep(200);
  }

  async renderPDA(tokens, steps, postfix) {
    const placeholder = this.pdaVisual.querySelector('.pda-placeholder');
    const columns = this.pdaVisual.querySelector('.pda-columns');
    placeholder.style.display = 'none';
    columns.classList.add('visible');

    // Animate each step
    for (let i = 0; i < steps.length; i++) {
      const step = steps[i];

      // Rebuild stack
      this.pdaStack.innerHTML = '<div class="stack-bottom">⊥</div>';
      for (const item of step.stack) {
        const el = document.createElement('div');
        el.className = `pda-item ${item.type === TOKEN_TYPES.OPERATOR ? 'op-item' : item.type === TOKEN_TYPES.LPAREN ? 'paren-item' : 'number-item'}`;
        el.textContent = item.value;
        this.pdaStack.appendChild(el);
      }

      // Rebuild output queue
      this.pdaOutputQueue.innerHTML = '';
      for (const item of step.output) {
        const el = document.createElement('div');
        el.className = `pda-item ${item.type === TOKEN_TYPES.OPERATOR ? 'op-item' : 'number-item'}`;
        el.textContent = item.value;
        this.pdaOutputQueue.appendChild(el);
      }

      await this.sleep(150);
    }

    // Render postfix output
    this.postfixOutput.innerHTML = '';
    for (let i = 0; i < postfix.length; i++) {
      const token = postfix[i];
      const chip = document.createElement('div');
      const cssClass = token.type === TOKEN_TYPES.OPERATOR ? 'operator' : 'number';
      const typeLabel = token.type === TOKEN_TYPES.OPERATOR ? 'OP' : 'NUM';

      chip.className = `token-chip ${cssClass}`;
      chip.style.animationDelay = `${i * 60}ms`;
      chip.innerHTML = `
        <span class="token-type">${typeLabel}</span>
        <span>${token.value}</span>
      `;
      this.postfixOutput.appendChild(chip);
    }

    await this.sleep(300);
  }

  // ---------- Stage 3: TM Visualization ----------

  async animateStage3(postfix) {
    this.activateStage(3);
    await this.sleep(200);
  }

  async renderTM(tape, computationSteps, result, expression) {
    const placeholder = this.tmVisual.querySelector('.tm-placeholder');
    const tapeContainer = this.tmVisual.querySelector('.tm-tape-container');
    placeholder.style.display = 'none';
    tapeContainer.classList.add('visible');
    this.tmSteps.classList.add('visible');

    // Render tape cells
    this.tmTape.innerHTML = '';
    const cells = [];
    for (const cell of tape) {
      const el = document.createElement('div');
      el.className = `tm-cell ${cell.type === 'BLANK' ? 'blank' : ''}`;
      el.textContent = cell.value;
      this.tmTape.appendChild(el);
      cells.push(el);
    }

    // Animate computation steps
    for (const step of computationSteps) {
      // Highlight current head position
      cells.forEach((c, idx) => {
        c.classList.remove('active');
        if (tape[idx].processed) c.classList.add('processed');
      });

      if (step.headPosition < cells.length) {
        cells[step.headPosition].classList.add('active');

        // Scroll tape to show current cell
        cells[step.headPosition].scrollIntoView({ behavior: 'smooth', inline: 'center', block: 'nearest' });
      }

      // Add step log
      const stepEl = document.createElement('div');
      stepEl.className = 'tm-step';
      stepEl.innerHTML = `
        <span class="tm-step-num">${step.state}</span>
        <span class="tm-step-action">${step.action}</span>
        <span class="tm-step-result">Stack: [${step.stack.join(', ')}]</span>
      `;
      this.tmSteps.appendChild(stepEl);
      this.tmSteps.scrollTop = this.tmSteps.scrollHeight;

      await this.sleep(250);
    }

    // Show final result
    this.resultDisplay.innerHTML = `
      <div>
        <div class="result-value">${result}</div>
        <div class="result-expression">${expression} = ${result}</div>
      </div>
    `;

    await this.sleep(100);
  }
}


// ========== Initialize ==========
document.addEventListener('DOMContentLoaded', () => {
  new CalculatorUI();
});
