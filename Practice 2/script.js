/* =============================================
   SMART CALCULATOR & EXPRESSION PARSER
   Core Engine: DFA Lexer → PDA Parser → TM Evaluator
   + Interactive Automata Simulators
   ============================================= */

// ========== STAGE 1: Deterministic Finite Automaton (Lexer) ==========

/**
 * DFA States for lexical analysis.
 * Formal 5-tuple: M = (Q, Σ, δ, q0, F)
 */
const DFA_STATES = {
  START: 'START',
  INTEGER: 'INTEGER',
  DOT: 'DOT',
  DECIMAL: 'DECIMAL',
  OPERATOR: 'OPERATOR',
  LPAREN: 'LPAREN',
  RPAREN: 'RPAREN',
  ERROR: 'ERROR'
};

const DFA_START_STATE = DFA_STATES.START;
const DFA_ACCEPTING_STATES = [
  DFA_STATES.INTEGER,
  DFA_STATES.DECIMAL,
  DFA_STATES.OPERATOR,
  DFA_STATES.LPAREN,
  DFA_STATES.RPAREN
];

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
  if (ch === null || ch === undefined) return 'EOF';
  if (ch >= '0' && ch <= '9') return 'DIGIT';
  if (ch === '.') return 'DOT';
  if ('+-*/'.includes(ch)) return 'OPERATOR';
  if (ch === '(') return 'LPAREN';
  if (ch === ')') return 'RPAREN';
  if (ch === ' ' || ch === '\t') return 'WHITESPACE';
  return 'UNKNOWN';
}

/**
 * Deterministic Transition Table for the DFA Lexer.
 * Maps (State, CharClass) → { next, action, transId, emit, error }
 */
const DFA_TRANSITION_TABLE = {
  START: {
    DIGIT: { next: DFA_STATES.INTEGER, action: "Read digit → start integer buffer", transId: 'dfaTrans_START_INTEGER' },
    DOT: { next: DFA_STATES.DOT, action: "Read '.' → start decimal with '0.'", transId: 'dfaTrans_START_DOT' },
    OPERATOR: { next: DFA_STATES.OPERATOR, action: "Read operator symbol", transId: 'dfaTrans_START_OPERATOR' },
    LPAREN: { next: DFA_STATES.LPAREN, action: "Read left parenthesis '('", transId: 'dfaTrans_START_LPAREN' },
    RPAREN: { next: DFA_STATES.RPAREN, action: "Read right parenthesis ')'", transId: 'dfaTrans_START_RPAREN' },
    WHITESPACE: { next: DFA_STATES.START, action: "Skip whitespace → remain in START", transId: 'dfaTrans_START_START' },
    EOF: { next: DFA_STATES.START, action: "End of input → complete", transId: null },
    UNKNOWN: { next: DFA_STATES.ERROR, action: "Unsupported character", transId: 'dfaTrans_START_ERROR', error: "Unsupported character" }
  },
  INTEGER: {
    DIGIT: { next: DFA_STATES.INTEGER, action: "Append digit to integer buffer", transId: 'dfaTrans_INTEGER_INTEGER' },
    DOT: { next: DFA_STATES.DOT, action: "Read '.' → transition to DOT state", transId: 'dfaTrans_INTEGER_DOT' },
    OPERATOR: { next: DFA_STATES.START, action: "Emit NUMBER token → reset to START", transId: 'dfaTrans_INTEGER_START', emit: 'NUMBER', reprocess: true },
    LPAREN: { next: DFA_STATES.START, action: "Emit NUMBER token → reset to START", transId: 'dfaTrans_INTEGER_START', emit: 'NUMBER', reprocess: true },
    RPAREN: { next: DFA_STATES.START, action: "Emit NUMBER token → reset to START", transId: 'dfaTrans_INTEGER_START', emit: 'NUMBER', reprocess: true },
    WHITESPACE: { next: DFA_STATES.START, action: "Emit NUMBER token → reset to START", transId: 'dfaTrans_INTEGER_START', emit: 'NUMBER' },
    EOF: { next: DFA_STATES.START, action: "Emit final NUMBER token → reset to START", transId: 'dfaTrans_INTEGER_START', emit: 'NUMBER' },
    UNKNOWN: { next: DFA_STATES.ERROR, action: "Invalid character following number", transId: 'dfaTrans_START_ERROR', error: "Unexpected character" }
  },
  DOT: {
    DIGIT: { next: DFA_STATES.DECIMAL, action: "Append fraction digit → enter DECIMAL state", transId: 'dfaTrans_DOT_DECIMAL' },
    DOT: { next: DFA_STATES.ERROR, action: "Malformed decimal: consecutive decimal points '..'", transId: 'dfaTrans_DOT_ERROR', error: "Malformed decimal: consecutive decimal points '..'" },
    OPERATOR: { next: DFA_STATES.ERROR, action: "Malformed decimal: missing digits after decimal point", transId: 'dfaTrans_DOT_ERROR', error: "Malformed decimal: missing digits after decimal point" },
    LPAREN: { next: DFA_STATES.ERROR, action: "Malformed decimal: missing digits after decimal point", transId: 'dfaTrans_DOT_ERROR', error: "Malformed decimal: missing digits after decimal point" },
    RPAREN: { next: DFA_STATES.ERROR, action: "Malformed decimal: missing digits after decimal point", transId: 'dfaTrans_DOT_ERROR', error: "Malformed decimal: missing digits after decimal point" },
    WHITESPACE: { next: DFA_STATES.ERROR, action: "Malformed decimal: trailing decimal point", transId: 'dfaTrans_DOT_ERROR', error: "Malformed decimal: trailing decimal point" },
    EOF: { next: DFA_STATES.ERROR, action: "Malformed decimal: expression ends with a trailing decimal point", transId: 'dfaTrans_DOT_ERROR', error: "Malformed decimal: expression ends with a trailing decimal point" },
    UNKNOWN: { next: DFA_STATES.ERROR, action: "Invalid character following decimal point", transId: 'dfaTrans_DOT_ERROR', error: "Invalid character following decimal point" }
  },
  DECIMAL: {
    DIGIT: { next: DFA_STATES.DECIMAL, action: "Append fraction digit to decimal buffer", transId: 'dfaTrans_DECIMAL_DECIMAL' },
    DOT: { next: DFA_STATES.ERROR, action: "Malformed decimal: multiple decimal points", transId: 'dfaTrans_DECIMAL_ERROR', error: "Malformed decimal: unexpected multiple decimal points" },
    OPERATOR: { next: DFA_STATES.START, action: "Emit decimal NUMBER token → reset to START", transId: 'dfaTrans_DECIMAL_START', emit: 'NUMBER', reprocess: true },
    LPAREN: { next: DFA_STATES.START, action: "Emit decimal NUMBER token → reset to START", transId: 'dfaTrans_DECIMAL_START', emit: 'NUMBER', reprocess: true },
    RPAREN: { next: DFA_STATES.START, action: "Emit decimal NUMBER token → reset to START", transId: 'dfaTrans_DECIMAL_START', emit: 'NUMBER', reprocess: true },
    WHITESPACE: { next: DFA_STATES.START, action: "Emit decimal NUMBER token → reset to START", transId: 'dfaTrans_DECIMAL_START', emit: 'NUMBER' },
    EOF: { next: DFA_STATES.START, action: "Emit final decimal NUMBER token → reset to START", transId: 'dfaTrans_DECIMAL_START', emit: 'NUMBER' },
    UNKNOWN: { next: DFA_STATES.ERROR, action: "Invalid character in decimal number", transId: 'dfaTrans_START_ERROR', error: "Unexpected character in decimal number" }
  }
};

/**
 * DFA-based Lexer.
 * Scans input character-by-character, strictly driving transitions via the transition table.
 * Returns { tokens, trace, isValid, errorMessage }.
 */
function dfaLexer(input) {
  const tokens = [];
  const trace = [];
  let state = DFA_STATES.START;
  let buffer = '';
  let i = 0;
  let isValid = true;
  let errorMessage = null;

  while (i <= input.length) {
    const isEof = i >= input.length;
    const ch = isEof ? null : input[i];
    const charClass = classifyChar(ch);
    const displayChar = isEof ? 'EOF' : (ch === ' ' ? '␣' : (ch === '\t' ? '\\t' : ch));

    if (state === DFA_STATES.START) {
      if (isEof) {
        trace.push({
          step: trace.length + 1,
          charIndex: i,
          char: 'EOF',
          charClass: 'EOF',
          stateBefore: DFA_STATES.START,
          stateAfter: DFA_STATES.START,
          action: 'End of input reached: lexical analysis complete',
          buffer: '',
          tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
          emittedToken: null,
          transId: null,
          isError: false,
          errorMessage: null
        });
        break;
      }

      if (charClass === 'WHITESPACE') {
        trace.push({
          step: trace.length + 1,
          charIndex: i,
          char: displayChar,
          charClass: 'WHITESPACE',
          stateBefore: DFA_STATES.START,
          stateAfter: DFA_STATES.START,
          action: 'Skip whitespace character',
          buffer: '',
          tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
          emittedToken: null,
          transId: 'dfaTrans_START_START',
          isError: false,
          errorMessage: null
        });
        i++;
        continue;
      }

      if (charClass === 'DIGIT') {
        buffer = ch;
        state = DFA_STATES.INTEGER;
        trace.push({
          step: trace.length + 1,
          charIndex: i,
          char: displayChar,
          charClass: 'DIGIT',
          stateBefore: DFA_STATES.START,
          stateAfter: DFA_STATES.INTEGER,
          action: `Read digit '${ch}' → start integer buffer [${buffer}]`,
          buffer: buffer,
          tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
          emittedToken: null,
          transId: 'dfaTrans_START_INTEGER',
          isError: false,
          errorMessage: null
        });
        i++;
        continue;
      }

      if (charClass === 'DOT') {
        buffer = '0.';
        state = DFA_STATES.DOT;
        trace.push({
          step: trace.length + 1,
          charIndex: i,
          char: displayChar,
          charClass: 'DOT',
          stateBefore: DFA_STATES.START,
          stateAfter: DFA_STATES.DOT,
          action: `Read leading '.' → start decimal buffer [${buffer}]`,
          buffer: buffer,
          tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
          emittedToken: null,
          transId: 'dfaTrans_START_DOT',
          isError: false,
          errorMessage: null
        });
        i++;
        continue;
      }

      if (charClass === 'OPERATOR') {
        state = DFA_STATES.OPERATOR;
        const opToken = { type: TOKEN_TYPES.OPERATOR, value: ch };
        tokens.push(opToken);
        trace.push({
          step: trace.length + 1,
          charIndex: i,
          char: displayChar,
          charClass: 'OPERATOR',
          stateBefore: DFA_STATES.START,
          stateAfter: DFA_STATES.OPERATOR,
          action: `Read operator '${ch}' → emit OPERATOR token and reset to START`,
          buffer: ch,
          tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
          emittedToken: opToken,
          transId: 'dfaTrans_START_OPERATOR',
          isError: false,
          errorMessage: null
        });
        state = DFA_STATES.START;
        i++;
        continue;
      }

      if (charClass === 'LPAREN') {
        state = DFA_STATES.LPAREN;
        const lpToken = { type: TOKEN_TYPES.LPAREN, value: '(' };
        tokens.push(lpToken);
        trace.push({
          step: trace.length + 1,
          charIndex: i,
          char: displayChar,
          charClass: 'LPAREN',
          stateBefore: DFA_STATES.START,
          stateAfter: DFA_STATES.LPAREN,
          action: `Read left parenthesis '(' → emit LPAREN token and reset to START`,
          buffer: '(',
          tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
          emittedToken: lpToken,
          transId: 'dfaTrans_START_LPAREN',
          isError: false,
          errorMessage: null
        });
        state = DFA_STATES.START;
        i++;
        continue;
      }

      if (charClass === 'RPAREN') {
        state = DFA_STATES.RPAREN;
        const rpToken = { type: TOKEN_TYPES.RPAREN, value: ')' };
        tokens.push(rpToken);
        trace.push({
          step: trace.length + 1,
          charIndex: i,
          char: displayChar,
          charClass: 'RPAREN',
          stateBefore: DFA_STATES.START,
          stateAfter: DFA_STATES.RPAREN,
          action: `Read right parenthesis ')' → emit RPAREN token and reset to START`,
          buffer: ')',
          tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
          emittedToken: rpToken,
          transId: 'dfaTrans_START_RPAREN',
          isError: false,
          errorMessage: null
        });
        state = DFA_STATES.START;
        i++;
        continue;
      }

      // UNKNOWN character error
      state = DFA_STATES.ERROR;
      isValid = false;
      errorMessage = `Unsupported character '${ch}' at position ${i}`;
      trace.push({
        step: trace.length + 1,
        charIndex: i,
        char: displayChar,
        charClass: 'UNKNOWN',
        stateBefore: DFA_STATES.START,
        stateAfter: DFA_STATES.ERROR,
        action: `Trap to ERROR: Unsupported character '${ch}' at index ${i}`,
        buffer: buffer,
        tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
        emittedToken: null,
        transId: 'dfaTrans_START_ERROR',
        isError: true,
        errorMessage: errorMessage
      });
      break;
    }

    if (state === DFA_STATES.INTEGER) {
      if (charClass === 'DIGIT') {
        buffer += ch;
        trace.push({
          step: trace.length + 1,
          charIndex: i,
          char: displayChar,
          charClass: 'DIGIT',
          stateBefore: DFA_STATES.INTEGER,
          stateAfter: DFA_STATES.INTEGER,
          action: `Append digit '${ch}' to integer buffer [${buffer}]`,
          buffer: buffer,
          tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
          emittedToken: null,
          transId: 'dfaTrans_INTEGER_INTEGER',
          isError: false,
          errorMessage: null
        });
        i++;
        continue;
      }

      if (charClass === 'DOT') {
        buffer += ch;
        state = DFA_STATES.DOT;
        trace.push({
          step: trace.length + 1,
          charIndex: i,
          char: displayChar,
          charClass: 'DOT',
          stateBefore: DFA_STATES.INTEGER,
          stateAfter: DFA_STATES.DOT,
          action: `Read '.' → transition from INTEGER to DOT state [${buffer}]`,
          buffer: buffer,
          tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
          emittedToken: null,
          transId: 'dfaTrans_INTEGER_DOT',
          isError: false,
          errorMessage: null
        });
        i++;
        continue;
      }

      if (charClass === 'UNKNOWN') {
        state = DFA_STATES.ERROR;
        isValid = false;
        errorMessage = `Unexpected character '${ch}' following integer at position ${i}`;
        trace.push({
          step: trace.length + 1,
          charIndex: i,
          char: displayChar,
          charClass: 'UNKNOWN',
          stateBefore: DFA_STATES.INTEGER,
          stateAfter: DFA_STATES.ERROR,
          action: `Trap to ERROR: Unexpected character '${ch}' at position ${i}`,
          buffer: buffer,
          tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
          emittedToken: null,
          transId: 'dfaTrans_START_ERROR',
          isError: true,
          errorMessage: errorMessage
        });
        break;
      }

      // Delimiter encountered: emit integer token and reset to START
      const numToken = { type: TOKEN_TYPES.NUMBER, value: buffer };
      tokens.push(numToken);
      const emittedVal = buffer;
      buffer = '';
      state = DFA_STATES.START;

      trace.push({
        step: trace.length + 1,
        charIndex: i,
        char: displayChar,
        charClass: charClass,
        stateBefore: DFA_STATES.INTEGER,
        stateAfter: DFA_STATES.START,
        action: `Delimiter '${displayChar}' encountered → emit NUMBER token "${emittedVal}", reset to START`,
        buffer: '',
        tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
        emittedToken: numToken,
        transId: 'dfaTrans_INTEGER_START',
        isError: false,
        errorMessage: null
      });

      // Do NOT increment i: re-process delimiter character from START
      continue;
    }

    if (state === DFA_STATES.DOT) {
      if (charClass === 'DIGIT') {
        buffer += ch;
        state = DFA_STATES.DECIMAL;
        trace.push({
          step: trace.length + 1,
          charIndex: i,
          char: displayChar,
          charClass: 'DIGIT',
          stateBefore: DFA_STATES.DOT,
          stateAfter: DFA_STATES.DECIMAL,
          action: `Read first fraction digit '${ch}' → enter DECIMAL state [${buffer}]`,
          buffer: buffer,
          tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
          emittedToken: null,
          transId: 'dfaTrans_DOT_DECIMAL',
          isError: false,
          errorMessage: null
        });
        i++;
        continue;
      }

      if (charClass === 'DOT') {
        state = DFA_STATES.ERROR;
        isValid = false;
        errorMessage = `Malformed decimal: consecutive decimal points '..' at position ${i}`;
        trace.push({
          step: trace.length + 1,
          charIndex: i,
          char: displayChar,
          charClass: 'DOT',
          stateBefore: DFA_STATES.DOT,
          stateAfter: DFA_STATES.ERROR,
          action: `Trap to ERROR: Consecutive decimal points '..' at position ${i}`,
          buffer: buffer,
          tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
          emittedToken: null,
          transId: 'dfaTrans_DOT_ERROR',
          isError: true,
          errorMessage: errorMessage
        });
        break;
      }

      // Missing digits after dot
      state = DFA_STATES.ERROR;
      isValid = false;
      errorMessage = isEof
        ? `Malformed decimal: expression ends with a trailing decimal point at position ${i - 1}`
        : `Malformed decimal: expected fraction digits after decimal point, found '${ch}' at position ${i}`;
      trace.push({
        step: trace.length + 1,
        charIndex: i,
        char: displayChar,
        charClass: charClass,
        stateBefore: DFA_STATES.DOT,
        stateAfter: DFA_STATES.ERROR,
        action: `Trap to ERROR: Missing digits after decimal point at position ${i}`,
        buffer: buffer,
        tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
        emittedToken: null,
        transId: 'dfaTrans_DOT_ERROR',
        isError: true,
        errorMessage: errorMessage
      });
      break;
    }

    if (state === DFA_STATES.DECIMAL) {
      if (charClass === 'DIGIT') {
        buffer += ch;
        trace.push({
          step: trace.length + 1,
          charIndex: i,
          char: displayChar,
          charClass: 'DIGIT',
          stateBefore: DFA_STATES.DECIMAL,
          stateAfter: DFA_STATES.DECIMAL,
          action: `Append fraction digit '${ch}' to decimal buffer [${buffer}]`,
          buffer: buffer,
          tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
          emittedToken: null,
          transId: 'dfaTrans_DECIMAL_DECIMAL',
          isError: false,
          errorMessage: null
        });
        i++;
        continue;
      }

      if (charClass === 'DOT') {
        state = DFA_STATES.ERROR;
        isValid = false;
        errorMessage = `Malformed decimal: unexpected multiple decimal points at position ${i}`;
        trace.push({
          step: trace.length + 1,
          charIndex: i,
          char: displayChar,
          charClass: 'DOT',
          stateBefore: DFA_STATES.DECIMAL,
          stateAfter: DFA_STATES.ERROR,
          action: `Trap to ERROR: Unexpected second decimal point in number [${buffer}]`,
          buffer: buffer,
          tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
          emittedToken: null,
          transId: 'dfaTrans_DECIMAL_ERROR',
          isError: true,
          errorMessage: errorMessage
        });
        break;
      }

      if (charClass === 'UNKNOWN') {
        state = DFA_STATES.ERROR;
        isValid = false;
        errorMessage = `Unexpected character '${ch}' in decimal number at position ${i}`;
        trace.push({
          step: trace.length + 1,
          charIndex: i,
          char: displayChar,
          charClass: 'UNKNOWN',
          stateBefore: DFA_STATES.DECIMAL,
          stateAfter: DFA_STATES.ERROR,
          action: `Trap to ERROR: Unexpected character '${ch}' at position ${i}`,
          buffer: buffer,
          tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
          emittedToken: null,
          transId: 'dfaTrans_START_ERROR',
          isError: true,
          errorMessage: errorMessage
        });
        break;
      }

      // Delimiter encountered: emit decimal token and reset to START
      const numToken = { type: TOKEN_TYPES.NUMBER, value: buffer };
      tokens.push(numToken);
      const emittedVal = buffer;
      buffer = '';
      state = DFA_STATES.START;

      trace.push({
        step: trace.length + 1,
        charIndex: i,
        char: displayChar,
        charClass: charClass,
        stateBefore: DFA_STATES.DECIMAL,
        stateAfter: DFA_STATES.START,
        action: `Delimiter '${displayChar}' encountered → emit decimal NUMBER token "${emittedVal}", reset to START`,
        buffer: '',
        tokensSnapshot: JSON.parse(JSON.stringify(tokens)),
        emittedToken: numToken,
        transId: 'dfaTrans_DECIMAL_START',
        isError: false,
        errorMessage: null
      });

      // Do NOT increment i: re-process delimiter character from START
      continue;
    }

    i++;
  }

  return { tokens, trace, isValid, errorMessage };
}

/**
 * Controller class for Stage 1 DFA Lexer interactive visualizer.
 * Supports Step Forward, Step Back, Play, Pause, Reset, speed control,
 * HUD metric updates, token stream, active transition highlight, and history table inspection.
 */
class DFALexerVisualizer {
  constructor() {
    this.trace = [];
    this.tokens = [];
    this.currentStepIdx = 0;
    this.isPlaying = false;
    this.playTimer = null;
    this.isValid = true;
    this.errorMessage = null;

    this.bindElements();
    this.bindEvents();
  }

  bindElements() {
    this.stepBackBtn = document.getElementById('stage1StepBack');
    this.playPauseBtn = document.getElementById('stage1PlayPause');
    this.playIcon = document.getElementById('stage1PlayIcon');
    this.playText = document.getElementById('stage1PlayText');
    this.stepForwardBtn = document.getElementById('stage1StepForward');
    this.resetBtn = document.getElementById('stage1Reset');
    this.speedSlider = document.getElementById('stage1Speed');
    this.stepCounter = document.getElementById('stage1StepCounter');

    this.curChar = document.getElementById('stage1CurChar');
    this.charClass = document.getElementById('stage1CharClass');
    this.prevState = document.getElementById('stage1PrevState');
    this.nextState = document.getElementById('stage1NextState');
    this.buffer = document.getElementById('stage1Buffer');
    this.action = document.getElementById('stage1Action');

    this.tokenStream = document.getElementById('tokenStream');
    this.traceBody = document.getElementById('stage1TraceBody');
    this.traceContainer = document.getElementById('stage1TraceContainer');
    this.verdict = document.getElementById('stage1Verdict');
  }

  bindEvents() {
    if (this.stepBackBtn) {
      this.stepBackBtn.addEventListener('click', () => {
        this.pause();
        this.stepBackward();
      });
    }

    if (this.stepForwardBtn) {
      this.stepForwardBtn.addEventListener('click', () => {
        this.pause();
        this.stepForward();
      });
    }

    if (this.playPauseBtn) {
      this.playPauseBtn.addEventListener('click', () => {
        this.togglePlay();
      });
    }

    if (this.resetBtn) {
      this.resetBtn.addEventListener('click', () => {
        this.reset();
      });
    }
  }

  load(trace, tokens, isValid, errorMessage) {
    this.pause();
    this.trace = trace || [];
    this.tokens = tokens || [];
    this.isValid = isValid !== false;
    this.errorMessage = errorMessage || null;
    this.currentStepIdx = 0;

    this.renderTraceTable();
    this.renderCurrentStep();
  }

  renderTraceTable() {
    if (!this.traceBody) return;
    if (this.trace.length === 0) {
      this.traceBody.innerHTML = '<tr><td colspan="7" class="stage1-trace-empty">Run expression to inspect transition log</td></tr>';
      return;
    }

    let html = '';
    this.trace.forEach((step, idx) => {
      const charDisplay = step.char === ' ' ? '␣' : step.char;
      html += `
        <tr data-step="${idx}" class="${idx === this.currentStepIdx ? 'active-step' : ''}">
          <td><strong>${step.step}</strong></td>
          <td><code>${charDisplay}</code></td>
          <td><span class="stage1-class-pill">${step.charClass}</span></td>
          <td>${step.stateBefore}</td>
          <td><strong>${step.stateAfter}</strong></td>
          <td><code>${step.buffer || '—'}</code></td>
          <td>${step.action}</td>
        </tr>
      `;
    });
    this.traceBody.innerHTML = html;

    // Row click inspection
    this.traceBody.querySelectorAll('tr').forEach(row => {
      row.addEventListener('click', () => {
        const stepNum = parseInt(row.dataset.step);
        if (!isNaN(stepNum)) {
          this.pause();
          this.currentStepIdx = stepNum;
          this.renderCurrentStep();
        }
      });
    });
  }

  renderCurrentStep() {
    if (this.trace.length === 0) {
      if (this.stepCounter) this.stepCounter.textContent = 'Step 0 / 0';
      if (this.curChar) this.curChar.textContent = '—';
      if (this.charClass) this.charClass.textContent = '—';
      if (this.prevState) this.prevState.textContent = 'START';
      if (this.nextState) this.nextState.textContent = 'START';
      if (this.buffer) this.buffer.textContent = '[ empty ]';
      if (this.action) this.action.textContent = 'Enter an expression and parse to begin DFA lexing.';
      this.clearHighlights();
      return;
    }

    const step = this.trace[this.currentStepIdx];
    if (!step) return;

    if (this.stepCounter) {
      this.stepCounter.textContent = `Step ${this.currentStepIdx + 1} / ${this.trace.length}`;
    }
    if (this.curChar) {
      this.curChar.textContent = step.char;
    }
    if (this.charClass) {
      this.charClass.textContent = step.charClass;
    }
    if (this.prevState) {
      this.prevState.textContent = step.stateBefore;
    }
    if (this.nextState) {
      this.nextState.textContent = step.stateAfter;
    }
    if (this.buffer) {
      this.buffer.textContent = step.buffer ? `"${step.buffer}"` : '[ empty ]';
    }
    if (this.action) {
      this.action.textContent = step.action;
    }

    // Highlight state and transition in SVG
    this.clearHighlights();
    const stateEl = document.getElementById(`dfaState_${step.stateAfter}`);
    if (stateEl) {
      stateEl.classList.add('highlight');
    }

    if (step.transId) {
      const transEl = document.getElementById(step.transId);
      if (transEl) {
        transEl.classList.add('highlight');
      }
    }

    // Update tokens stream up to this step
    this.renderTokenStream(step.tokensSnapshot, step.isError ? step.char : null);

    // Update active row in table
    if (this.traceBody) {
      this.traceBody.querySelectorAll('tr').forEach(r => r.classList.remove('active-step'));
      const activeRow = this.traceBody.querySelector(`tr[data-step="${this.currentStepIdx}"]`);
      if (activeRow) {
        activeRow.classList.add('active-step');
        if (this.traceContainer) {
          activeRow.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
        }
      }
    }

    // Update Verdict
    if (this.verdict) {
      const isLastStep = this.currentStepIdx === this.trace.length - 1;
      if (step.isError || (!this.isValid && isLastStep)) {
        this.verdict.textContent = `✗ DFA LEXICAL REJECTION — ${this.errorMessage || step.action}`;
        this.verdict.className = 'sim-verdict rejected';
        this.verdict.style.display = 'block';
      } else if (this.isValid && isLastStep) {
        this.verdict.textContent = `✓ DFA LEXICAL ANALYSIS ACCEPTED — ${this.tokens.length} token(s) recognized successfully`;
        this.verdict.className = 'sim-verdict accepted';
        this.verdict.style.display = 'block';
      } else {
        this.verdict.style.display = 'none';
      }
    }
  }

  renderTokenStream(tokens, errorChar = null) {
    if (!this.tokenStream) return;
    if ((!tokens || tokens.length === 0) && !errorChar) {
      this.tokenStream.innerHTML = '<div class="token-placeholder">Recognized tokens will accumulate here...</div>';
      return;
    }

    this.tokenStream.innerHTML = '';
    tokens.forEach(token => {
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
      chip.innerHTML = `
        <span class="token-type">${typeLabel}</span>
        <span>${token.value}</span>
      `;
      this.tokenStream.appendChild(chip);
    });

    if (errorChar) {
      const errChip = document.createElement('div');
      errChip.className = 'token-chip error';
      errChip.innerHTML = `
        <span class="token-type">ERR</span>
        <span>${errorChar}</span>
      `;
      this.tokenStream.appendChild(errChip);
    }
  }

  clearHighlights() {
    document.querySelectorAll('#dfaDiagram .dfa-state.highlight, #dfaDiagram .dfa-transition.highlight').forEach(el => {
      el.classList.remove('highlight');
    });
  }

  stepForward() {
    if (this.currentStepIdx < this.trace.length - 1) {
      this.currentStepIdx++;
      this.renderCurrentStep();
    }
  }

  stepBackward() {
    if (this.currentStepIdx > 0) {
      this.currentStepIdx--;
      this.renderCurrentStep();
    }
  }

  reset() {
    this.pause();
    this.currentStepIdx = 0;
    this.renderCurrentStep();
  }

  togglePlay() {
    if (this.isPlaying) {
      this.pause();
    } else {
      if (this.currentStepIdx >= this.trace.length - 1) {
        this.currentStepIdx = 0;
      }
      this.play();
    }
  }

  play() {
    if (this.isPlaying || this.trace.length === 0) return;
    this.isPlaying = true;
    this.updatePlayBtn(true);

    const stepInterval = () => {
      if (!this.isPlaying) return;
      if (this.currentStepIdx < this.trace.length - 1) {
        this.stepForward();
        const speed = this.getSpeed();
        this.playTimer = setTimeout(stepInterval, speed);
      } else {
        this.pause();
      }
    };

    const speed = this.getSpeed();
    this.playTimer = setTimeout(stepInterval, speed);
  }

  pause() {
    this.isPlaying = false;
    if (this.playTimer) {
      clearTimeout(this.playTimer);
      this.playTimer = null;
    }
    this.updatePlayBtn(false);
  }

  updatePlayBtn(isPlaying) {
    if (this.playText) {
      this.playText.textContent = isPlaying ? 'Pause' : 'Play';
    }
    if (this.playIcon) {
      this.playIcon.innerHTML = isPlaying 
        ? '<path d="M6 4h4v16H6zM14 4h4v16h-4z"/>'
        : '<path d="M5 3l14 9-14 9z"/>';
    }
  }

  getSpeed() {
    if (!this.speedSlider) return 400;
    return 1300 - parseInt(this.speedSlider.value);
  }

  async playAll() {
    if (this.trace.length === 0) return;
    this.isPlaying = true;
    this.updatePlayBtn(true);

    let speed = this.getSpeed();
    await new Promise(r => setTimeout(r, speed));

    while (this.isPlaying && this.currentStepIdx < this.trace.length - 1) {
      this.stepForward();
      speed = this.getSpeed();
      await new Promise(r => setTimeout(r, speed));
    }

    this.pause();
  }
}


// ==========================================================================
// STAGE 2: Pushdown Automaton (PDA Syntax Analyzer)
// ==========================================================================

const OPERATORS = {
  '+': { precedence: 1, associativity: 'left' },
  '-': { precedence: 1, associativity: 'left' },
  '*': { precedence: 2, associativity: 'left' },
  '/': { precedence: 2, associativity: 'left' }
};

const PDA_STATES = {
  START: 'q_start',
  READ: 'q_read',
  OPERAND: 'q_operand',
  OP: 'q_op',
  POP: 'q_pop',
  PUSH_OP: 'q_push_op',
  LPAREN: 'q_lparen',
  RPAREN: 'q_rparen',
  DISCARD_PAREN: 'q_discard_paren',
  DRAIN: 'q_drain',
  ACCEPT: 'q_accept',
  REJECT: 'q_reject'
};

const PDA_FORMAL_DEF = {
  states: ['q_start', 'q_read', 'q_operand', 'q_op', 'q_pop', 'q_push_op', 'q_lparen', 'q_rparen', 'q_discard_paren', 'q_drain', 'q_accept', 'q_reject'],
  inputAlphabet: ['NUMBER', '+', '-', '*', '/', '(', ')', '$'],
  stackAlphabet: ['⊥', '+', '-', '*', '/', '('],
  startState: 'q_start',
  initialStack: '⊥',
  acceptStates: ['q_accept']
};

/**
 * Formal PDA Syntax Analyzer & Shunting-Yard Parser.
 * Converts infix token stream to postfix (RPN) while verifying grammar rules:
 * - Balanced parentheses
 * - No consecutive operators
 * - No missing or trailing operands
 * - No adjacent numbers without operator
 * - No empty parentheses
 * Returns { postfix, trace, isValid, errorMessage }.
 */
function pdaParser(tokens) {
  const trace = [];
  const outputQueue = [];
  const operatorStack = ['⊥'];
  let isValid = true;
  let errorMessage = null;

  if (!tokens || tokens.length === 0) {
    isValid = false;
    errorMessage = 'Empty token stream: no mathematical expression provided';
    trace.push({
      step: 1,
      stateBefore: PDA_STATES.START,
      stateAfter: PDA_STATES.REJECT,
      token: { type: 'EOF', value: '$' },
      stackTop: '⊥',
      stackOp: 'NONE',
      stack: ['⊥'],
      output: [],
      remainingTokens: [],
      action: 'Syntax Error: Empty input expression',
      reason: errorMessage,
      isError: true,
      errorMessage: errorMessage
    });
    return { postfix: [], trace, isValid, errorMessage };
  }

  // Pre-scan syntax validation rules
  for (let k = 0; k < tokens.length; k++) {
    const cur = tokens[k];
    const next = tokens[k + 1];

    if (cur.type === TOKEN_TYPES.LPAREN && next && next.type === TOKEN_TYPES.RPAREN) {
      isValid = false;
      errorMessage = 'Malformed syntax: empty parentheses "()" contain no expression';
      break;
    }
    if (k === 0 && cur.type === TOKEN_TYPES.OPERATOR) {
      isValid = false;
      errorMessage = `Malformed syntax: leading binary operator '${cur.value}' is missing left operand`;
      break;
    }
    if (cur.type === TOKEN_TYPES.OPERATOR && next && next.type === TOKEN_TYPES.OPERATOR) {
      isValid = false;
      errorMessage = `Malformed syntax: consecutive operators '${cur.value}' and '${next.value}' with no operand between them`;
      break;
    }
    if (cur.type === TOKEN_TYPES.NUMBER && next && next.type === TOKEN_TYPES.NUMBER) {
      isValid = false;
      errorMessage = `Malformed syntax: adjacent numbers '${cur.value}' and '${next.value}' without an intervening operator`;
      break;
    }
    if (cur.type === TOKEN_TYPES.LPAREN && next && next.type === TOKEN_TYPES.OPERATOR) {
      isValid = false;
      errorMessage = `Malformed syntax: operator '${next.value}' immediately follows opening parenthesis '(' without left operand`;
      break;
    }
    if (cur.type === TOKEN_TYPES.OPERATOR && next && next.type === TOKEN_TYPES.RPAREN) {
      isValid = false;
      errorMessage = `Malformed syntax: operator '${cur.value}' immediately precedes closing parenthesis ')' without right operand`;
      break;
    }
  }

  if (isValid && tokens[tokens.length - 1].type === TOKEN_TYPES.OPERATOR) {
    isValid = false;
    errorMessage = `Malformed syntax: expression ends with trailing operator '${tokens[tokens.length - 1].value}' without right operand`;
  }

  if (!isValid) {
    trace.push({
      step: 1,
      stateBefore: PDA_STATES.START,
      stateAfter: PDA_STATES.REJECT,
      token: tokens[0] || { type: 'EOF', value: '$' },
      stackTop: '⊥',
      stackOp: 'NONE',
      stack: ['⊥'],
      output: [],
      remainingTokens: tokens.map(t => t.value),
      action: 'Trap to REJECT state: Syntax violation detected',
      reason: errorMessage,
      isError: true,
      errorMessage: errorMessage
    });
    return { postfix: [], trace, isValid, errorMessage };
  }

  // Step 1: Initial configuration
  trace.push({
    step: 1,
    stateBefore: PDA_STATES.START,
    stateAfter: PDA_STATES.READ,
    token: tokens[0],
    stackTop: '⊥',
    stackOp: 'PEEK',
    stack: [...operatorStack],
    output: [...outputQueue],
    remainingTokens: tokens.map(t => t.value),
    action: `Initialize pushdown automaton with bottom marker Z₀ = ⊥`,
    reason: `Initial PDA configuration: (q_start, w, ⊥) ⊢ (q_read, w, ⊥)`,
    isError: false,
    errorMessage: null
  });

  let state = PDA_STATES.READ;

  for (let i = 0; i < tokens.length; i++) {
    const token = tokens[i];
    const remaining = tokens.slice(i + 1).map(t => t.value);

    if (token.type === TOKEN_TYPES.NUMBER) {
      state = PDA_STATES.OPERAND;
      outputQueue.push(token);

      trace.push({
        step: trace.length + 1,
        stateBefore: PDA_STATES.READ,
        stateAfter: PDA_STATES.OPERAND,
        token: token,
        stackTop: operatorStack[operatorStack.length - 1],
        stackOp: 'NONE',
        stack: [...operatorStack],
        output: [...outputQueue],
        remainingTokens: remaining,
        action: `Enqueue operand '${token.value}' to Output Queue`,
        reason: `δ(q_read, NUMBER, X) → (q_operand, X): Numerical operands bypass stack directly to postfix output`,
        isError: false,
        errorMessage: null
      });

      state = PDA_STATES.READ;
    }
    else if (token.type === TOKEN_TYPES.LPAREN) {
      state = PDA_STATES.LPAREN;
      operatorStack.push('(');

      trace.push({
        step: trace.length + 1,
        stateBefore: PDA_STATES.READ,
        stateAfter: PDA_STATES.LPAREN,
        token: token,
        stackTop: '(',
        stackOp: 'PUSH',
        stack: [...operatorStack],
        output: [...outputQueue],
        remainingTokens: remaining,
        action: `Push left parenthesis '(' onto Operator Stack`,
        reason: `δ(q_read, '(', X) → (q_lparen, '(' X): Sub-expression precedence scope opened`,
        isError: false,
        errorMessage: null
      });

      state = PDA_STATES.READ;
    }
    else if (token.type === TOKEN_TYPES.OPERATOR) {
      state = PDA_STATES.OP;
      const curOp = OPERATORS[token.value];

      while (operatorStack.length > 1) {
        const topSym = operatorStack[operatorStack.length - 1];
        if (topSym === '(') break;

        const topOp = OPERATORS[topSym];
        if (!topOp) break;

        const shouldPop = (topOp.precedence > curOp.precedence) ||
                          (topOp.precedence === curOp.precedence && curOp.associativity === 'left');

        if (!shouldPop) break;

        operatorStack.pop();
        outputQueue.push({ type: TOKEN_TYPES.OPERATOR, value: topSym });

        trace.push({
          step: trace.length + 1,
          stateBefore: PDA_STATES.OP,
          stateAfter: PDA_STATES.POP,
          token: token,
          stackTop: topSym,
          stackOp: 'POP',
          stack: [...operatorStack],
          output: [...outputQueue],
          remainingTokens: remaining,
          action: `Pop '${topSym}' from stack → Output Queue`,
          reason: `precedence('${topSym}')=${topOp.precedence} ≥ precedence('${token.value}')=${curOp.precedence}: stack operator has priority`,
          isError: false,
          errorMessage: null
        });
      }

      operatorStack.push(token.value);
      trace.push({
        step: trace.length + 1,
        stateBefore: PDA_STATES.OP,
        stateAfter: PDA_STATES.PUSH_OP,
        token: token,
        stackTop: token.value,
        stackOp: 'PUSH',
        stack: [...operatorStack],
        output: [...outputQueue],
        remainingTokens: remaining,
        action: `Push operator '${token.value}' onto Operator Stack`,
        reason: `δ(q_op, '${token.value}', X) → (q_push_op, '${token.value}' X): Buffered until lower precedence operator arrives`,
        isError: false,
        errorMessage: null
      });

      state = PDA_STATES.READ;
    }
    else if (token.type === TOKEN_TYPES.RPAREN) {
      state = PDA_STATES.RPAREN;
      let matchedLParen = false;

      while (operatorStack.length > 1) {
        const topSym = operatorStack[operatorStack.length - 1];
        if (topSym === '(') {
          operatorStack.pop();
          matchedLParen = true;

          trace.push({
            step: trace.length + 1,
            stateBefore: PDA_STATES.RPAREN,
            stateAfter: PDA_STATES.DISCARD_PAREN,
            token: token,
            stackTop: '(',
            stackOp: 'DISCARD',
            stack: [...operatorStack],
            output: [...outputQueue],
            remainingTokens: remaining,
            action: `Matched parenthesis pair — discard '(' from Stack`,
            reason: `δ(q_rparen, ')', '(') → (q_discard_paren, ε): Sub-expression scope successfully closed`,
            isError: false,
            errorMessage: null
          });
          break;
        }

        const popped = operatorStack.pop();
        outputQueue.push({ type: TOKEN_TYPES.OPERATOR, value: popped });

        trace.push({
          step: trace.length + 1,
          stateBefore: PDA_STATES.RPAREN,
          stateAfter: PDA_STATES.POP,
          token: token,
          stackTop: popped,
          stackOp: 'POP',
          stack: [...operatorStack],
          output: [...outputQueue],
          remainingTokens: remaining,
          action: `Pop '${popped}' from stack → Output Queue (unwinding parenthesis scope)`,
          reason: `Encountered closing ')': Unwind all buffered operators until '('`,
          isError: false,
          errorMessage: null
        });
      }

      if (!matchedLParen) {
        isValid = false;
        errorMessage = 'Unbalanced parentheses: closing ")" has no matching "(" on stack';
        trace.push({
          step: trace.length + 1,
          stateBefore: PDA_STATES.RPAREN,
          stateAfter: PDA_STATES.REJECT,
          token: token,
          stackTop: operatorStack[operatorStack.length - 1],
          stackOp: 'NONE',
          stack: [...operatorStack],
          output: [...outputQueue],
          remainingTokens: remaining,
          action: 'Trap to REJECT state: Unbalanced closing parenthesis',
          reason: errorMessage,
          isError: true,
          errorMessage: errorMessage
        });
        return { postfix: [], trace, isValid, errorMessage };
      }

      state = PDA_STATES.READ;
    }
  }

  // Drain stack at EOF
  state = PDA_STATES.DRAIN;
  while (operatorStack.length > 1) {
    const topSym = operatorStack[operatorStack.length - 1];
    if (topSym === '(') {
      isValid = false;
      errorMessage = 'Unbalanced parentheses: unclosed opening parenthesis "(" without matching ")"';
      trace.push({
        step: trace.length + 1,
        stateBefore: PDA_STATES.DRAIN,
        stateAfter: PDA_STATES.REJECT,
        token: { type: 'EOF', value: '$' },
        stackTop: '(',
        stackOp: 'NONE',
        stack: [...operatorStack],
        output: [...outputQueue],
        remainingTokens: [],
        action: 'Trap to REJECT state: Unclosed parenthesis at end of input',
        reason: errorMessage,
        isError: true,
        errorMessage: errorMessage
      });
      return { postfix: [], trace, isValid, errorMessage };
    }

    const popped = operatorStack.pop();
    outputQueue.push({ type: TOKEN_TYPES.OPERATOR, value: popped });

    trace.push({
      step: trace.length + 1,
      stateBefore: PDA_STATES.DRAIN,
      stateAfter: PDA_STATES.POP,
      token: { type: 'EOF', value: '$' },
      stackTop: popped,
      stackOp: 'POP',
      stack: [...operatorStack],
      output: [...outputQueue],
      remainingTokens: [],
      action: `Pop remaining '${popped}' from stack → Output Queue`,
      reason: `End of input ($) reached: Emptying pushdown stack to finalize postfix stream`,
      isError: false,
      errorMessage: null
    });
  }

  // Final Accept Configuration
  trace.push({
    step: trace.length + 1,
    stateBefore: PDA_STATES.DRAIN,
    stateAfter: PDA_STATES.ACCEPT,
    token: { type: 'EOF', value: '$' },
    stackTop: '⊥',
    stackOp: 'PEEK',
    stack: ['⊥'],
    output: [...outputQueue],
    remainingTokens: [],
    action: `Accept: Input exhausted, stack reduced to Z₀ = ⊥, postfix stream complete`,
    reason: `δ(q_drain, $, ⊥) → (q_accept, ⊥): Expression syntax is formally valid and accepted`,
    isError: false,
    errorMessage: null
  });

  return { postfix: outputQueue, trace, isValid, errorMessage };
}

/**
 * Controller class for Stage 2 PDA Syntax Analyzer interactive visualizer.
 */
class PDAParserVisualizer {
  constructor() {
    this.trace = [];
    this.postfix = [];
    this.currentStepIdx = 0;
    this.isPlaying = false;
    this.playTimer = null;
    this.isValid = true;
    this.errorMessage = null;

    this.bindElements();
    this.bindEvents();
  }

  bindElements() {
    this.stepBackBtn = document.getElementById('stage2StepBack');
    this.playPauseBtn = document.getElementById('stage2PlayPause');
    this.playIcon = document.getElementById('stage2PlayIcon');
    this.playText = document.getElementById('stage2PlayText');
    this.stepForwardBtn = document.getElementById('stage2StepForward');
    this.resetBtn = document.getElementById('stage2Reset');
    this.speedSlider = document.getElementById('stage2Speed');
    this.stepCounter = document.getElementById('stage2StepCounter');

    this.curToken = document.getElementById('stage2CurToken');
    this.curState = document.getElementById('stage2CurState');
    this.stackTop = document.getElementById('stage2StackTop');
    this.stackOp = document.getElementById('stage2StackOp');
    this.actionReason = document.getElementById('stage2ActionReason');

    this.inputQueue = document.getElementById('pdaInputQueue');
    this.stackVisual = document.getElementById('pdaStack');
    this.outputQueue = document.getElementById('pdaOutputQueue');
    this.postfixOutput = document.getElementById('postfixOutput');
    this.traceBody = document.getElementById('stage2TraceBody');
    this.traceContainer = document.getElementById('stage2TraceContainer');
    this.verdict = document.getElementById('stage2Verdict');
  }

  bindEvents() {
    if (this.stepBackBtn) {
      this.stepBackBtn.addEventListener('click', () => {
        this.pause();
        this.stepBackward();
      });
    }
    if (this.stepForwardBtn) {
      this.stepForwardBtn.addEventListener('click', () => {
        this.pause();
        this.stepForward();
      });
    }
    if (this.playPauseBtn) {
      this.playPauseBtn.addEventListener('click', () => {
        this.togglePlay();
      });
    }
    if (this.resetBtn) {
      this.resetBtn.addEventListener('click', () => {
        this.reset();
      });
    }
  }

  load(trace, postfix, isValid, errorMessage) {
    this.pause();
    this.trace = trace || [];
    this.postfix = postfix || [];
    this.isValid = isValid !== false;
    this.errorMessage = errorMessage || null;
    this.currentStepIdx = 0;

    this.renderTraceTable();
    this.renderCurrentStep();
  }

  renderTraceTable() {
    if (!this.traceBody) return;
    if (this.trace.length === 0) {
      this.traceBody.innerHTML = '<tr><td colspan="8" class="stage1-trace-empty">Parse expression to inspect PDA transitions</td></tr>';
      return;
    }

    let html = '';
    this.trace.forEach((step, idx) => {
      const tokVal = step.token ? (step.token.value || step.token.type) : '—';
      const stackStr = step.stack ? step.stack.join(' ') : '⊥';
      const outStr = step.output ? step.output.map(t => t.value).join(' ') : '—';

      html += `
        <tr data-step="${idx}" class="${idx === this.currentStepIdx ? 'active-step' : ''}">
          <td><strong>${step.step}</strong></td>
          <td><span class="stage1-state-pill">${step.stateAfter}</span></td>
          <td><code>${tokVal}</code></td>
          <td><strong>${step.stackTop || '—'}</strong></td>
          <td><span class="stage2-op-pill">${step.stackOp}</span></td>
          <td><code>[${stackStr}]</code></td>
          <td><code>${outStr || '—'}</code></td>
          <td><small>${step.reason}</small></td>
        </tr>
      `;
    });
    this.traceBody.innerHTML = html;

    this.traceBody.querySelectorAll('tr').forEach(row => {
      row.addEventListener('click', () => {
        const stepNum = parseInt(row.dataset.step);
        if (!isNaN(stepNum)) {
          this.pause();
          this.currentStepIdx = stepNum;
          this.renderCurrentStep();
        }
      });
    });
  }

  renderCurrentStep() {
    if (this.trace.length === 0) {
      if (this.stepCounter) this.stepCounter.textContent = 'Step 0 / 0';
      if (this.curToken) this.curToken.textContent = '—';
      if (this.curState) this.curState.textContent = 'q_start';
      if (this.stackTop) this.stackTop.textContent = '⊥';
      if (this.stackOp) this.stackOp.textContent = 'NONE';
      if (this.actionReason) this.actionReason.textContent = 'Awaiting tokens from DFA lexer...';
      return;
    }

    const step = this.trace[this.currentStepIdx];
    if (!step) return;

    if (this.stepCounter) {
      this.stepCounter.textContent = `Step ${this.currentStepIdx + 1} / ${this.trace.length}`;
    }
    if (this.curToken) {
      this.curToken.textContent = step.token ? (step.token.value || step.token.type) : '—';
    }
    if (this.curState) {
      this.curState.textContent = step.stateAfter;
    }
    if (this.stackTop) {
      this.stackTop.textContent = step.stackTop || '⊥';
    }
    if (this.stackOp) {
      this.stackOp.textContent = step.stackOp || 'NONE';
    }
    if (this.actionReason) {
      this.actionReason.innerHTML = `<strong>${step.action}</strong><br><span style="opacity:0.8">${step.reason}</span>`;
    }

    // Render Input Queue (remaining tokens)
    if (this.inputQueue) {
      this.inputQueue.innerHTML = '';
      if (step.remainingTokens && step.remainingTokens.length > 0) {
        step.remainingTokens.forEach((sym, idx) => {
          const item = document.createElement('div');
          item.className = 'pda-item number-item';
          if (idx === 0) item.classList.add('top-item');
          item.textContent = sym;
          this.inputQueue.appendChild(item);
        });
      } else {
        this.inputQueue.innerHTML = '<span class="pda-col-hint">[ empty ]</span>';
      }
    }

    // Render Stack (pushdown memory)
    if (this.stackVisual) {
      this.stackVisual.innerHTML = '';
      if (step.stack && step.stack.length > 0) {
        // Render top-down
        for (let i = step.stack.length - 1; i >= 0; i--) {
          const sym = step.stack[i];
          const item = document.createElement('div');
          item.className = 'pda-item';
          if (sym === '⊥') {
            item.className += ' stack-bottom';
          } else if (OPERATORS[sym]) {
            item.className += ' op-item';
          } else if (sym === '(') {
            item.className += ' paren-item';
          } else {
            item.className += ' number-item';
          }
          if (i === step.stack.length - 1) {
            item.classList.add('top-item');
          }
          item.textContent = sym;
          this.stackVisual.appendChild(item);
        }
      } else {
        this.stackVisual.innerHTML = '<div class="stack-bottom">⊥</div>';
      }
    }

    // Render Output Queue up to this step
    if (this.outputQueue) {
      this.outputQueue.innerHTML = '';
      if (step.output && step.output.length > 0) {
        step.output.forEach(tok => {
          const item = document.createElement('div');
          item.className = `pda-item ${tok.type === TOKEN_TYPES.OPERATOR ? 'op-item' : 'number-item'}`;
          item.textContent = tok.value;
          this.outputQueue.appendChild(item);
        });
      } else {
        this.outputQueue.innerHTML = '<span class="pda-col-hint">[ empty ]</span>';
      }
    }

    // Render Postfix Output
    if (this.postfixOutput) {
      if (step.output && step.output.length > 0) {
        this.postfixOutput.innerHTML = '';
        step.output.forEach((tok, idx) => {
          const chip = document.createElement('div');
          const isOp = tok.type === TOKEN_TYPES.OPERATOR;
          chip.className = `token-chip ${isOp ? 'operator' : 'number'}`;
          chip.innerHTML = `
            <span class="token-type">${isOp ? 'OP' : 'NUM'}</span>
            <span>${tok.value}</span>
          `;
          this.postfixOutput.appendChild(chip);
        });
      } else {
        this.postfixOutput.innerHTML = '<div class="token-placeholder">Postfix notation will appear here...</div>';
      }
    }

    // Highlight row in table
    if (this.traceBody) {
      this.traceBody.querySelectorAll('tr').forEach(r => r.classList.remove('active-step'));
      const activeRow = this.traceBody.querySelector(`tr[data-step="${this.currentStepIdx}"]`);
      if (activeRow) {
        activeRow.classList.add('active-step');
        if (this.traceContainer) {
          activeRow.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
        }
      }
    }

    // Update Verdict
    if (this.verdict) {
      const isLastStep = this.currentStepIdx === this.trace.length - 1;
      if (step.isError || (!this.isValid && isLastStep)) {
        this.verdict.textContent = `✗ PDA SYNTAX REJECTED — ${this.errorMessage || step.action}`;
        this.verdict.className = 'sim-verdict rejected';
        this.verdict.style.display = 'block';
      } else if (this.isValid && isLastStep) {
        this.verdict.textContent = `✓ PDA SYNTAX ACCEPTED — ${this.postfix.length} postfix token(s) produced, stack cleanly reduced to ⊥`;
        this.verdict.className = 'sim-verdict accepted';
        this.verdict.style.display = 'block';
      } else {
        this.verdict.style.display = 'none';
      }
    }
  }

  stepForward() {
    if (this.currentStepIdx < this.trace.length - 1) {
      this.currentStepIdx++;
      this.renderCurrentStep();
    }
  }

  stepBackward() {
    if (this.currentStepIdx > 0) {
      this.currentStepIdx--;
      this.renderCurrentStep();
    }
  }

  reset() {
    this.pause();
    this.currentStepIdx = 0;
    this.renderCurrentStep();
  }

  togglePlay() {
    if (this.isPlaying) {
      this.pause();
    } else {
      if (this.currentStepIdx >= this.trace.length - 1) {
        this.currentStepIdx = 0;
        this.renderCurrentStep();
      }
      this.play();
    }
  }

  play() {
    if (this.isPlaying || this.trace.length === 0) return;
    this.isPlaying = true;
    this.updatePlayBtn(true);

    const stepInterval = () => {
      if (!this.isPlaying) return;
      if (this.currentStepIdx < this.trace.length - 1) {
        this.stepForward();
        const speed = this.getSpeed();
        this.playTimer = setTimeout(stepInterval, speed);
      } else {
        this.pause();
      }
    };

    const speed = this.getSpeed();
    this.playTimer = setTimeout(stepInterval, speed);
  }

  pause() {
    this.isPlaying = false;
    if (this.playTimer) {
      clearTimeout(this.playTimer);
      this.playTimer = null;
    }
    this.updatePlayBtn(false);
  }

  updatePlayBtn(isPlaying) {
    if (this.playText) {
      this.playText.textContent = isPlaying ? 'Pause' : 'Play';
    }
    if (this.playIcon) {
      this.playIcon.innerHTML = isPlaying
        ? '<path d="M6 4h4v16H6zM14 4h4v16h-4z"/>'
        : '<path d="M5 3l14 9-14 9z"/>';
    }
  }

  getSpeed() {
    if (!this.speedSlider) return 400;
    return 1300 - parseInt(this.speedSlider.value);
  }

  async playAll() {
    if (this.trace.length === 0) return;
    this.isPlaying = true;
    this.updatePlayBtn(true);

    let speed = this.getSpeed();
    await new Promise(r => setTimeout(r, speed));

    while (this.isPlaying && this.currentStepIdx < this.trace.length - 1) {
      this.stepForward();
      speed = this.getSpeed();
      await new Promise(r => setTimeout(r, speed));
    }

    this.pause();
  }
}


// ==========================================================================
// STAGE 3: Turing Machine & Arithmetic Evaluator
// ==========================================================================

/**
 * High-precision step-by-step arithmetic evaluator for postfix tokens.
 * Evaluates mathematical expressions without JavaScript eval().
 * Catches division by zero.
 */
function arithmeticEvaluator(postfix) {
  const steps = [];
  const valStack = [];
  let isValid = true;
  let errorMessage = null;

  for (let i = 0; i < postfix.length; i++) {
    const token = postfix[i];
    if (token.type === TOKEN_TYPES.NUMBER) {
      const num = parseFloat(token.value);
      valStack.push(num);
      steps.push({
        step: steps.length + 1,
        state: 'q_push',
        head: i,
        read: token.value,
        write: token.value,
        move: 'R',
        nextState: 'q_scan',
        tape: postfix.map(t => t.value),
        action: `Operand ${token.value}: Push onto evaluation stack`,
        stack: [...valStack]
      });
    } else if (token.type === TOKEN_TYPES.OPERATOR) {
      if (valStack.length < 2) {
        isValid = false;
        errorMessage = `Insufficient operands for operator '${token.value}'`;
        steps.push({
          step: steps.length + 1,
          state: 'q_eval',
          head: i,
          read: token.value,
          write: token.value,
          move: 'N',
          nextState: 'q_reject',
          tape: postfix.map(t => t.value),
          action: `Trap to REJECT: ${errorMessage}`,
          stack: [...valStack]
        });
        break;
      }

      const b = valStack.pop();
      const a = valStack.pop();
      let res;

      if (token.value === '+') res = a + b;
      else if (token.value === '-') res = a - b;
      else if (token.value === '*') res = a * b;
      else if (token.value === '/') {
        if (b === 0) {
          isValid = false;
          errorMessage = 'Division-by-zero error: denominator evaluates to 0';
          steps.push({
            step: steps.length + 1,
            state: 'q_eval',
            head: i,
            read: token.value,
            write: token.value,
            move: 'N',
            nextState: 'q_reject',
            tape: postfix.map(t => t.value),
            action: `Trap to REJECT: ${errorMessage}`,
            stack: [...valStack]
          });
          break;
        }
        res = a / b;
      }

      res = Math.round(res * 1e10) / 1e10;
      valStack.push(res);

      steps.push({
        step: steps.length + 1,
        state: 'q_eval',
        head: i,
        read: token.value,
        write: String(res),
        move: 'R',
        nextState: 'q_scan',
        tape: postfix.map(t => t.value),
        action: `Arithmetic Reduction: ${a} ${token.value} ${b} = ${res}`,
        stack: [...valStack]
      });
    }
  }

  if (isValid && valStack.length !== 1) {
    isValid = false;
    errorMessage = 'Malformed expression: evaluation did not reduce to a single scalar';
  }

  const finalResult = isValid ? valStack[0] : null;

  if (isValid) {
    steps.push({
      step: steps.length + 1,
      state: 'q_halt',
      head: postfix.length,
      read: '□',
      write: '□',
      move: 'N',
      nextState: 'q_accept',
      tape: [...postfix.map(t => t.value), '□'],
      action: `Evaluation Complete: Final Result = ${finalResult}`,
      stack: [finalResult]
    });
  }

  return { result: finalResult, steps, isValid, errorMessage };
}

/**
 * Genuine Formal Single-Tape Turing Machine executing Unary Addition:
 * 1ᵐ + 1ⁿ = 1ᵐ⁺ⁿ
 */
function runUnaryAdditionTM(tapeStr = '111+11') {
  const cleanInput = tapeStr.trim() || '111+11';
  const tape = cleanInput.split('');
  tape.push('□', '□', '□');

  let head = 0;
  let state = 'q0';
  const steps = [];

  const transitions = {
    'q0,1': { write: '1', move: 'R', next: 'q0', desc: 'Scan right over first unary operand (1s)' },
    'q0,+': { write: '1', move: 'R', next: 'q1', desc: 'Replace "+" with "1" and enter second operand scan' },
    'q1,1': { write: '1', move: 'R', next: 'q1', desc: 'Scan right over second unary operand (1s)' },
    'q1,□': { write: '□', move: 'L', next: 'q2', desc: 'End of input reached: Move left to erase the compensatory 1' },
    'q2,1': { write: '□', move: 'N', next: 'q_accept', desc: 'Erase extra 1 to blank "□" and halt: Unary addition verified' }
  };

  while (state !== 'q_accept' && state !== 'q_reject' && steps.length < 200) {
    const sym = tape[head] || '□';
    const key = `${state},${sym}`;
    const rule = transitions[key];

    if (!rule) {
      state = 'q_reject';
      steps.push({
        step: steps.length + 1,
        state,
        head,
        read: sym,
        write: sym,
        move: 'N',
        nextState: state,
        tape: [...tape],
        action: `Trap to REJECT: No transition defined for (${state}, ${sym})`
      });
      break;
    }

    tape[head] = rule.write;
    const prevHead = head;
    const prevState = state;
    state = rule.next;

    if (rule.move === 'R') head++;
    else if (rule.move === 'L') head--;

    steps.push({
      step: steps.length + 1,
      state: prevState,
      head: prevHead,
      read: sym,
      write: rule.write,
      move: rule.move,
      nextState: state,
      tape: [...tape],
      action: rule.desc
    });
  }

  const result1s = tape.filter(c => c === '1').length;
  return {
    steps,
    finalTape: tape,
    finalState: state,
    result: `${result1s} (unary: ${'1'.repeat(result1s)})`,
    isValid: state === 'q_accept'
  };
}

/**
 * Genuine Formal Single-Tape Turing Machine executing Binary Incrementer:
 * w + 1
 */
function runBinaryIncrementerTM(binaryStr = '1011') {
  const tape = binaryStr.split('');
  tape.unshift('□');
  tape.push('□');

  let head = 1;
  let state = 'q0';
  const steps = [];

  const transitions = {
    'q0,0': { write: '0', move: 'R', next: 'q0', desc: 'Scan right to find least-significant bit' },
    'q0,1': { write: '1', move: 'R', next: 'q0', desc: 'Scan right to find least-significant bit' },
    'q0,□': { write: '□', move: 'L', next: 'q_carry', desc: 'Blank cell reached: Move left to perform binary addition' },
    'q_carry,0': { write: '1', move: 'L', next: 'q_done', desc: '0 + 1 = 1 (no carry): Move left to rewind' },
    'q_carry,1': { write: '0', move: 'L', next: 'q_carry', desc: '1 + 1 = 0 with carry: Propagate carry bit left' },
    'q_carry,□': { write: '1', move: 'N', next: 'q_accept', desc: 'Carry overflow: Write 1 at MSB and halt' },
    'q_done,0': { write: '0', move: 'L', next: 'q_done', desc: 'Rewind head to tape start' },
    'q_done,1': { write: '1', move: 'L', next: 'q_done', desc: 'Rewind head to tape start' },
    'q_done,□': { write: '□', move: 'R', next: 'q_accept', desc: 'Head repositioned at start: Increment accepted' }
  };

  while (state !== 'q_accept' && state !== 'q_reject' && steps.length < 200) {
    const sym = tape[head] || '□';
    const key = `${state},${sym}`;
    const rule = transitions[key];

    if (!rule) {
      state = 'q_reject';
      steps.push({
        step: steps.length + 1,
        state,
        head,
        read: sym,
        write: sym,
        move: 'N',
        nextState: state,
        tape: [...tape],
        action: `Trap to REJECT: No rule for (${state}, ${sym})`
      });
      break;
    }

    tape[head] = rule.write;
    const prevHead = head;
    const prevState = state;
    state = rule.next;

    if (rule.move === 'R') head++;
    else if (rule.move === 'L') head--;

    steps.push({
      step: steps.length + 1,
      state: prevState,
      head: prevHead,
      read: sym,
      write: rule.write,
      move: rule.move,
      nextState: state,
      tape: [...tape],
      action: rule.desc
    });
  }

  const cleanTape = tape.filter(c => c !== '□').join('');
  return {
    steps,
    finalTape: tape,
    finalState: state,
    result: `${cleanTape}₂ (${parseInt(cleanTape, 2)})`,
    isValid: state === 'q_accept'
  };
}

/**
 * Controller class for Stage 3 Turing Machine & Evaluator.
 */
class TMVisualizer {
  constructor() {
    this.steps = [];
    this.currentStepIdx = 0;
    this.isPlaying = false;
    this.playTimer = null;
    this.isValid = true;
    this.errorMessage = null;
    this.mode = 'evaluator'; // 'evaluator', 'unary_tm', 'binary_tm'
    this.result = null;

    this.bindElements();
    this.bindEvents();
  }

  bindElements() {
    this.modeEvaluatorBtn = document.getElementById('stage3ModeEvaluator');
    this.modeUnaryBtn = document.getElementById('stage3ModeUnary');
    this.modeBinaryBtn = document.getElementById('stage3ModeBinary');

    this.stepBackBtn = document.getElementById('stage3StepBack');
    this.playPauseBtn = document.getElementById('stage3PlayPause');
    this.playIcon = document.getElementById('stage3PlayIcon');
    this.playText = document.getElementById('stage3PlayText');
    this.stepForwardBtn = document.getElementById('stage3StepForward');
    this.resetBtn = document.getElementById('stage3Reset');
    this.speedSlider = document.getElementById('stage3Speed');
    this.stepCounter = document.getElementById('stage3StepCounter');

    this.curState = document.getElementById('stage3CurState');
    this.headIdx = document.getElementById('stage3HeadIdx');
    this.readSym = document.getElementById('stage3ReadSym');
    this.writeSym = document.getElementById('stage3WriteSym');
    this.headMove = document.getElementById('stage3HeadMove');
    this.action = document.getElementById('stage3Action');

    this.tapeVisual = document.getElementById('tmTape');
    this.headPointer = document.getElementById('stage3HeadPointer');
    this.stepsVisual = document.getElementById('tmSteps');
    this.resultDisplay = document.getElementById('resultDisplay');
    this.traceBody = document.getElementById('stage3TraceBody');
    this.traceContainer = document.getElementById('stage3TraceContainer');
    this.verdict = document.getElementById('stage3Verdict');
  }

  bindEvents() {
    if (this.modeEvaluatorBtn) {
      this.modeEvaluatorBtn.addEventListener('click', () => this.switchMode('evaluator'));
    }
    if (this.modeUnaryBtn) {
      this.modeUnaryBtn.addEventListener('click', () => this.switchMode('unary_tm'));
    }
    if (this.modeBinaryBtn) {
      this.modeBinaryBtn.addEventListener('click', () => this.switchMode('binary_tm'));
    }

    if (this.stepBackBtn) {
      this.stepBackBtn.addEventListener('click', () => {
        this.pause();
        this.stepBackward();
      });
    }
    if (this.stepForwardBtn) {
      this.stepForwardBtn.addEventListener('click', () => {
        this.pause();
        this.stepForward();
      });
    }
    if (this.playPauseBtn) {
      this.playPauseBtn.addEventListener('click', () => {
        this.togglePlay();
      });
    }
    if (this.resetBtn) {
      this.resetBtn.addEventListener('click', () => {
        this.reset();
      });
    }
  }

  switchMode(newMode) {
    this.mode = newMode;
    [this.modeEvaluatorBtn, this.modeUnaryBtn, this.modeBinaryBtn].forEach(btn => {
      if (btn) btn.classList.remove('active');
    });

    if (newMode === 'evaluator') {
      if (this.modeEvaluatorBtn) this.modeEvaluatorBtn.classList.add('active');
    } else if (newMode === 'unary_tm') {
      if (this.modeUnaryBtn) this.modeUnaryBtn.classList.add('active');
      const tmRes = runUnaryAdditionTM('111+11');
      this.load(tmRes.steps, tmRes.result, tmRes.isValid, null);
    } else if (newMode === 'binary_tm') {
      if (this.modeBinaryBtn) this.modeBinaryBtn.classList.add('active');
      const binRes = runBinaryIncrementerTM('1011');
      this.load(binRes.steps, binRes.result, binRes.isValid, null);
    }
  }

  loadEvaluator(steps, result, isValid, errorMessage, postfix) {
    this.mode = 'evaluator';
    if (this.modeEvaluatorBtn) this.modeEvaluatorBtn.classList.add('active');
    [this.modeUnaryBtn, this.modeBinaryBtn].forEach(b => b && b.classList.remove('active'));
    this.load(steps, result, isValid, errorMessage);
  }

  load(steps, result, isValid, errorMessage) {
    this.pause();
    this.steps = steps || [];
    this.result = result;
    this.isValid = isValid !== false;
    this.errorMessage = errorMessage || null;
    this.currentStepIdx = 0;

    this.renderTraceTable();
    this.renderCurrentStep();
  }

  renderTraceTable() {
    if (!this.traceBody) return;
    if (this.steps.length === 0) {
      this.traceBody.innerHTML = '<tr><td colspan="9" class="stage1-trace-empty">Run evaluation to inspect TM transitions</td></tr>';
      return;
    }

    let html = '';
    this.steps.forEach((step, idx) => {
      const tapeStr = step.tape ? step.tape.join(' ') : '—';
      html += `
        <tr data-step="${idx}" class="${idx === this.currentStepIdx ? 'active-step' : ''}">
          <td><strong>${step.step}</strong></td>
          <td><span class="stage1-state-pill">${step.state}</span></td>
          <td>Cell ${step.head}</td>
          <td><code>${step.read}</code></td>
          <td><code>${step.write}</code></td>
          <td><strong>${step.move}</strong></td>
          <td><span class="stage1-state-pill">${step.nextState}</span></td>
          <td><code>[${tapeStr}]</code></td>
          <td><small>${step.action}</small></td>
        </tr>
      `;
    });
    this.traceBody.innerHTML = html;

    this.traceBody.querySelectorAll('tr').forEach(row => {
      row.addEventListener('click', () => {
        const stepNum = parseInt(row.dataset.step);
        if (!isNaN(stepNum)) {
          this.pause();
          this.currentStepIdx = stepNum;
          this.renderCurrentStep();
        }
      });
    });
  }

  renderCurrentStep() {
    if (this.steps.length === 0) {
      if (this.stepCounter) this.stepCounter.textContent = 'Step 0 / 0';
      if (this.curState) this.curState.textContent = 'q0';
      if (this.headIdx) this.headIdx.textContent = 'Cell 0';
      if (this.readSym) this.readSym.textContent = '—';
      if (this.writeSym) this.writeSym.textContent = '—';
      if (this.headMove) this.headMove.textContent = 'NONE';
      if (this.action) this.action.textContent = 'Awaiting evaluation...';
      if (this.tapeVisual) this.tapeVisual.innerHTML = '<div class="sim-tape-cell blank">□</div>';
      return;
    }

    const step = this.steps[this.currentStepIdx];
    if (!step) return;

    if (this.stepCounter) {
      this.stepCounter.textContent = `Step ${this.currentStepIdx + 1} / ${this.steps.length}`;
    }
    if (this.curState) {
      this.curState.textContent = step.state;
    }
    if (this.headIdx) {
      this.headIdx.textContent = `Cell ${step.head}`;
    }
    if (this.readSym) {
      this.readSym.textContent = step.read || '—';
    }
    if (this.writeSym) {
      this.writeSym.textContent = step.write || '—';
    }
    if (this.headMove) {
      this.headMove.textContent = step.move || 'NONE';
    }
    if (this.action) {
      this.action.textContent = step.action || '—';
    }

    // Render Tape Cells & Head
    if (this.tapeVisual && step.tape) {
      this.tapeVisual.innerHTML = '';
      step.tape.forEach((cellVal, idx) => {
        const cell = document.createElement('div');
        cell.className = 'tm-cell';
        if (cellVal === '□') cell.classList.add('blank');
        if (idx === step.head) cell.classList.add('head-active');

        cell.innerHTML = `
          <span class="tm-cell-idx">${idx}</span>
          <span class="tm-cell-val">${cellVal}</span>
        `;
        this.tapeVisual.appendChild(cell);
      });

      // Align Head Pointer above active cell
      if (this.headPointer) {
        const targetCell = this.tapeVisual.children[step.head];
        if (targetCell) {
          const offsetLeft = targetCell.offsetLeft + (targetCell.offsetWidth / 2) - 15;
          this.headPointer.style.transform = `translateX(${Math.max(0, offsetLeft)}px)`;
        }
      }
    }

    // Render steps list
    if (this.stepsVisual) {
      this.stepsVisual.innerHTML = '';
      for (let s = 0; s <= this.currentStepIdx; s++) {
        const item = document.createElement('div');
        item.className = 'tm-step-item';
        item.textContent = `Step ${this.steps[s].step}: ${this.steps[s].action}`;
        this.stepsVisual.appendChild(item);
      }
      this.stepsVisual.scrollTop = this.stepsVisual.scrollHeight;
    }

    // Render Final Result if at last step
    if (this.resultDisplay) {
      const isLastStep = this.currentStepIdx === this.steps.length - 1;
      if (isLastStep && this.isValid && this.result !== null) {
        this.resultDisplay.innerHTML = `
          <div class="result-number">${this.result}</div>
          <div class="result-expression">Automata computation finished successfully</div>
        `;
      } else if (!this.isValid && isLastStep) {
        this.resultDisplay.innerHTML = `
          <div class="result-number error" style="color:#f43f5e">ERROR</div>
          <div class="result-expression">${this.errorMessage}</div>
        `;
      } else {
        this.resultDisplay.innerHTML = '<div class="token-placeholder">Result will appear after full evaluation...</div>';
      }
    }

    // Highlight active row in history table
    if (this.traceBody) {
      this.traceBody.querySelectorAll('tr').forEach(r => r.classList.remove('active-step'));
      const activeRow = this.traceBody.querySelector(`tr[data-step="${this.currentStepIdx}"]`);
      if (activeRow) {
        activeRow.classList.add('active-step');
        if (this.traceContainer) {
          activeRow.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
        }
      }
    }

    // Update Verdict
    if (this.verdict) {
      const isLastStep = this.currentStepIdx === this.steps.length - 1;
      if (!this.isValid && isLastStep) {
        this.verdict.textContent = `✗ COMPUTATION REJECTED — ${this.errorMessage || step.action}`;
        this.verdict.className = 'sim-verdict rejected';
        this.verdict.style.display = 'block';
      } else if (this.isValid && isLastStep) {
        const modeLabel = this.mode === 'unary_tm' ? 'Unary Addition TM' : this.mode === 'binary_tm' ? 'Binary Incrementer TM' : 'Arithmetic Pipeline';
        this.verdict.textContent = `✓ ${modeLabel} HALTED & ACCEPTED — Computation completed (${this.result})`;
        this.verdict.className = 'sim-verdict accepted';
        this.verdict.style.display = 'block';
      } else {
        this.verdict.style.display = 'none';
      }
    }
  }

  stepForward() {
    if (this.currentStepIdx < this.steps.length - 1) {
      this.currentStepIdx++;
      this.renderCurrentStep();
    }
  }

  stepBackward() {
    if (this.currentStepIdx > 0) {
      this.currentStepIdx--;
      this.renderCurrentStep();
    }
  }

  reset() {
    this.pause();
    this.currentStepIdx = 0;
    this.renderCurrentStep();
  }

  togglePlay() {
    if (this.isPlaying) {
      this.pause();
    } else {
      if (this.currentStepIdx >= this.steps.length - 1) {
        this.currentStepIdx = 0;
        this.renderCurrentStep();
      }
      this.play();
    }
  }

  play() {
    if (this.isPlaying || this.steps.length === 0) return;
    this.isPlaying = true;
    this.updatePlayBtn(true);

    const stepInterval = () => {
      if (!this.isPlaying) return;
      if (this.currentStepIdx < this.steps.length - 1) {
        this.stepForward();
        const speed = this.getSpeed();
        this.playTimer = setTimeout(stepInterval, speed);
      } else {
        this.pause();
      }
    };

    const speed = this.getSpeed();
    this.playTimer = setTimeout(stepInterval, speed);
  }

  pause() {
    this.isPlaying = false;
    if (this.playTimer) {
      clearTimeout(this.playTimer);
      this.playTimer = null;
    }
    this.updatePlayBtn(false);
  }

  updatePlayBtn(isPlaying) {
    if (this.playText) {
      this.playText.textContent = isPlaying ? 'Pause' : 'Play';
    }
    if (this.playIcon) {
      this.playIcon.innerHTML = isPlaying
        ? '<path d="M6 4h4v16H6zM14 4h4v16h-4z"/>'
        : '<path d="M5 3l14 9-14 9z"/>';
    }
  }

  getSpeed() {
    if (!this.speedSlider) return 400;
    return 1300 - parseInt(this.speedSlider.value);
  }

  async playAll() {
    if (this.steps.length === 0) return;
    this.isPlaying = true;
    this.updatePlayBtn(true);

    let speed = this.getSpeed();
    await new Promise(r => setTimeout(r, speed));

    while (this.isPlaying && this.currentStepIdx < this.steps.length - 1) {
      this.stepForward();
      speed = this.getSpeed();
      await new Promise(r => setTimeout(r, speed));
    }

    this.pause();
  }
}


// ==========================================================================
// AUTOMATA WORKBENCH CONTROLLER
// ==========================================================================

class WorkbenchController {
  constructor() {
    this.currentTab = 'dfa';
    this.bindElements();
    this.bindEvents();
    this.renderInitialTables();
  }

  bindElements() {
    this.tabs = document.querySelectorAll('.wb-tabs .sim-tab');
    this.dfaPanel = document.getElementById('wbDfa');
    this.pdaPanel = document.getElementById('wbPda');
    this.tmPanel = document.getElementById('wbTm');

    // DFA Live elements
    this.dfaCurState = document.getElementById('wbDfaCurState');
    this.dfaRemainingInput = document.getElementById('wbDfaRemainingInput');
    this.dfaBuffer = document.getElementById('wbDfaBuffer');
    this.dfaStatus = document.getElementById('wbDfaStatus');
    this.dfaTransTable = document.getElementById('wbDfaTransTable');
    this.dfaTrace = document.getElementById('wbDfaTrace');

    // PDA Live elements
    this.pdaCurState = document.getElementById('wbPdaCurState');
    this.pdaRemainingInput = document.getElementById('wbPdaRemainingInput');
    this.pdaStackContents = document.getElementById('wbPdaStackContents');
    this.pdaStackTop = document.getElementById('wbPdaStackTop');
    this.pdaOutputQueue = document.getElementById('wbPdaOutputQueue');
    this.pdaStatus = document.getElementById('wbPdaStatus');
    this.pdaTransTable = document.getElementById('wbPdaTransTable');
    this.pdaTrace = document.getElementById('wbPdaTrace');

    // TM Live elements
    this.tmCurState = document.getElementById('wbTmCurState');
    this.tmHeadPos = document.getElementById('wbTmHeadPos');
    this.tmTapeDisplay = document.getElementById('wbTmTapeDisplay');
    this.tmReadSym = document.getElementById('wbTmReadSym');
    this.tmStatus = document.getElementById('wbTmStatus');
    this.tmTransTable = document.getElementById('wbTmTransTable');
    this.tmTrace = document.getElementById('wbTmTrace');
  }

  bindEvents() {
    this.tabs.forEach(tab => {
      tab.addEventListener('click', () => {
        this.tabs.forEach(t => t.classList.remove('active'));
        tab.classList.add('active');
        this.switchTab(tab.dataset.wbTab);
      });
    });
  }

  switchTab(tabName) {
    this.currentTab = tabName;
    if (this.dfaPanel) this.dfaPanel.style.display = tabName === 'dfa' ? '' : 'none';
    if (this.pdaPanel) this.pdaPanel.style.display = tabName === 'pda' ? '' : 'none';
    if (this.tmPanel) this.tmPanel.style.display = tabName === 'tm' ? '' : 'none';
  }

  renderInitialTables() {
    // DFA transition table
    if (this.dfaTransTable) {
      let html = '<table><thead><tr><th>State</th><th>DIGIT (0-9)</th><th>DOT (.)</th><th>OPERATOR (+-*/)</th><th>LPAREN (()</th><th>RPAREN ())</th><th>SPACE</th></tr></thead><tbody>';
      const states = ['START', 'INTEGER', 'DOT', 'DECIMAL', 'OPERATOR', 'LPAREN', 'RPAREN', 'ERROR'];
      const tableData = {
        START: ['INTEGER', 'DOT', 'OPERATOR', 'LPAREN', 'RPAREN', 'START'],
        INTEGER: ['INTEGER', 'DOT', 'START (emit)', 'START (emit)', 'START (emit)', 'START (emit)'],
        DOT: ['DECIMAL', 'ERROR', 'ERROR', 'ERROR', 'ERROR', 'ERROR'],
        DECIMAL: ['DECIMAL', 'ERROR', 'START (emit)', 'START (emit)', 'START (emit)', 'START (emit)'],
        OPERATOR: ['INTEGER', 'DOT', 'START (emit)', 'START (emit)', 'START (emit)', 'START (emit)'],
        LPAREN: ['INTEGER', 'DOT', 'START (emit)', 'START (emit)', 'START (emit)', 'START (emit)'],
        RPAREN: ['INTEGER', 'DOT', 'START (emit)', 'START (emit)', 'START (emit)', 'START (emit)'],
        ERROR: ['ERROR', 'ERROR', 'ERROR', 'ERROR', 'ERROR', 'ERROR']
      };
      states.forEach(s => {
        const row = tableData[s] || [];
        html += `<tr><td><strong>${s}</strong></td><td>${row[0]}</td><td>${row[1]}</td><td>${row[2]}</td><td>${row[3]}</td><td>${row[4]}</td><td>${row[5]}</td></tr>`;
      });
      html += '</tbody></table>';
      this.dfaTransTable.innerHTML = html;
    }

    // PDA transition table
    if (this.pdaTransTable) {
      let html = '<table><thead><tr><th>Current State</th><th>Input Symbol (a)</th><th>Stack Top (X)</th><th>→ Next State</th><th>Stack Action (γ)</th></tr></thead><tbody>';
      const pdaRules = [
        ['q_start', 'ε', 'ε', 'q_read', 'Push ⊥ (initial marker)'],
        ['q_read', 'NUMBER', 'X', 'q_operand', 'No change to stack (Enqueue to Output)'],
        ['q_read', '(', 'X', 'q_lparen', 'Push ( onto stack'],
        ['q_read', 'op (+,-,*,/)', 'X', 'q_op', 'Compare precedence with X'],
        ['q_op', 'ε', 'X (prec(X) ≥ prec(op))', 'q_pop', 'Pop X to Output'],
        ['q_op', 'ε', 'X (prec(X) < prec(op))', 'q_push_op', 'Push op onto stack'],
        ['q_read', ')', 'X ≠ (', 'q_rparen', 'Pop X to Output'],
        ['q_rparen', 'ε', '(', 'q_discard_paren', 'Discard ( and )'],
        ['q_read', '$ (EOF)', 'X ≠ ⊥', 'q_drain', 'Pop remaining X to Output'],
        ['q_drain', '$ (EOF)', '⊥', 'q_accept', 'Accept expression']
      ];
      pdaRules.forEach(r => {
        html += `<tr><td><strong>${r[0]}</strong></td><td><code>${r[1]}</code></td><td>${r[2]}</td><td><strong>${r[3]}</strong></td><td>${r[4]}</td></tr>`;
      });
      html += '</tbody></table>';
      this.pdaTransTable.innerHTML = html;
    }

    // TM transition table
    if (this.tmTransTable) {
      let html = '<table><thead><tr><th>Current State</th><th>Tape Symbol (σ)</th><th>→ Next State</th><th>Write Symbol (σ\')</th><th>Head Move (D)</th></tr></thead><tbody>';
      const tmRules = [
        ['q0', '1', 'q0', '1', 'R (Right)'],
        ['q0', '+', 'q1', '1', 'R (Right)'],
        ['q1', '1', 'q1', '1', 'R (Right)'],
        ['q1', '□ (blank)', 'q2', '□', 'L (Left)'],
        ['q2', '1', 'q_accept', '□', 'N (No move / Halt)']
      ];
      tmRules.forEach(r => {
        html += `<tr><td><strong>${r[0]}</strong></td><td><code>${r[1]}</code></td><td><strong>${r[2]}</strong></td><td><code>${r[3]}</code></td><td>${r[4]}</td></tr>`;
      });
      html += '</tbody></table>';
      this.tmTransTable.innerHTML = html;
    }
  }

  updateFromSimulation(lexResult, pdaResult, evalResult, expression) {
    // Update DFA live configuration
    if (lexResult) {
      const lastStep = lexResult.trace && lexResult.trace.length > 0 ? lexResult.trace[lexResult.trace.length - 1] : null;
      if (this.dfaCurState && lastStep) this.dfaCurState.textContent = lastStep.stateAfter;
      if (this.dfaRemainingInput) this.dfaRemainingInput.textContent = 'ε (consumed)';
      if (this.dfaBuffer) this.dfaBuffer.textContent = lastStep ? (lastStep.buffer || '[ empty ]') : '[ empty ]';
      if (this.dfaStatus) {
        this.dfaStatus.textContent = lexResult.isValid ? 'ACCEPTED' : 'REJECTED';
        this.dfaStatus.className = `wb-status-pill ${lexResult.isValid ? 'accepted' : 'rejected'}`;
      }

      if (this.dfaTrace && lexResult.trace) {
        let traceHtml = '';
        lexResult.trace.forEach(s => {
          traceHtml += `<div class="sim-trace-row"><span class="sim-trace-step">${s.step}</span><span class="sim-trace-state">${s.stateBefore}</span><span class="sim-trace-arrow">→</span><span class="sim-trace-next">${s.stateAfter}</span><span>'${s.char}' [${s.charClass}]</span><small>${s.action}</small></div>`;
        });
        this.dfaTrace.innerHTML = traceHtml;
      }
    }

    // Update PDA live configuration
    if (pdaResult) {
      const lastStep = pdaResult.trace && pdaResult.trace.length > 0 ? pdaResult.trace[pdaResult.trace.length - 1] : null;
      if (this.pdaCurState && lastStep) this.pdaCurState.textContent = lastStep.stateAfter;
      if (this.pdaRemainingInput) this.pdaRemainingInput.textContent = 'ε (consumed)';
      if (this.pdaStackContents && lastStep) this.pdaStackContents.textContent = `[ ${lastStep.stack.join(' ')} ]`;
      if (this.pdaStackTop && lastStep) this.pdaStackTop.textContent = lastStep.stackTop || '⊥';
      if (this.pdaOutputQueue) this.pdaOutputQueue.textContent = pdaResult.postfix ? pdaResult.postfix.map(t => t.value).join(' ') : '—';
      if (this.pdaStatus) {
        this.pdaStatus.textContent = pdaResult.isValid ? 'ACCEPTED' : 'REJECTED';
        this.pdaStatus.className = `wb-status-pill ${pdaResult.isValid ? 'accepted' : 'rejected'}`;
      }

      if (this.pdaTrace && pdaResult.trace) {
        let traceHtml = '';
        pdaResult.trace.forEach(s => {
          traceHtml += `<div class="sim-trace-row"><span class="sim-trace-step">${s.step}</span><span class="sim-trace-state">${s.stateBefore}</span><span class="sim-trace-arrow">⊢</span><span class="sim-trace-next">${s.stateAfter}</span><span>Top:${s.stackTop} (${s.stackOp})</span><small>${s.action}</small></div>`;
        });
        this.pdaTrace.innerHTML = traceHtml;
      }
    }

    // Update TM live configuration
    if (evalResult) {
      if (this.tmCurState) this.tmCurState.textContent = evalResult.isValid ? 'q_accept' : 'q_reject';
      if (this.tmHeadPos) this.tmHeadPos.textContent = `Cell ${evalResult.steps.length}`;
      if (this.tmTapeDisplay) this.tmTapeDisplay.textContent = `[ ${pdaResult && pdaResult.postfix ? pdaResult.postfix.map(t => t.value).join(' ') : ''} □ ]`;
      if (this.tmReadSym) this.tmReadSym.textContent = '□';
      if (this.tmStatus) {
        this.tmStatus.textContent = evalResult.isValid ? `ACCEPTED (${evalResult.result})` : `REJECTED (${evalResult.errorMessage})`;
        this.tmStatus.className = `wb-status-pill ${evalResult.isValid ? 'accepted' : 'rejected'}`;
      }

      if (this.tmTrace && evalResult.steps) {
        let traceHtml = '';
        evalResult.steps.forEach(s => {
          traceHtml += `<div class="sim-trace-row"><span class="sim-trace-step">${s.step}</span><span class="sim-trace-state">${s.state}</span><span class="sim-trace-arrow">⊢</span><span class="sim-trace-next">${s.nextState}</span><span>Read:${s.read} Write:${s.write}</span><small>${s.action}</small></div>`;
        });
        this.tmTrace.innerHTML = traceHtml;
      }
    }
  }
}


// ==========================================================================
// AUTOMATED TEST SUITE RUNNER
// ==========================================================================

class AutomataTestRunner {
  constructor(calculatorUI) {
    this.calcUI = calculatorUI;
    this.tableBody = document.getElementById('testTableBody');
    this.runAllBtn = document.getElementById('runAllTestsBtn');
    this.statTotal = document.getElementById('testStatTotal');
    this.statPassed = document.getElementById('testStatPassed');
    this.statFailed = document.getElementById('testStatFailed');
    this.statTime = document.getElementById('testStatTime');

    this.testCases = [
      {
        id: 1,
        expr: '5 + 3',
        stage: 'Arithmetic Pipeline',
        expected: 'Result = 8',
        type: 'eval',
        check: (res) => res.isValid && res.result === 8
      },
      {
        id: 2,
        expr: '(5 + 3) * 2',
        stage: 'Arithmetic Pipeline',
        expected: 'Result = 16',
        type: 'eval',
        check: (res) => res.isValid && res.result === 16
      },
      {
        id: 3,
        expr: '3.14 * (10 / 2)',
        stage: 'Arithmetic Pipeline',
        expected: 'Result = 15.7',
        type: 'eval',
        check: (res) => res.isValid && Math.abs(res.result - 15.7) < 1e-6
      },
      {
        id: 4,
        expr: '100 - 25 * 3 + 10',
        stage: 'Arithmetic Pipeline',
        expected: 'Result = 35',
        type: 'eval',
        check: (res) => res.isValid && res.result === 35
      },
      {
        id: 5,
        expr: '(2 + 3',
        stage: 'PDA Syntax Analyzer',
        expected: 'Rejected: Unclosed parenthesis',
        type: 'pda_reject',
        check: (res) => !res.isValid && res.errorMessage.includes('unclosed opening parenthesis')
      },
      {
        id: 6,
        expr: '5 + * 3',
        stage: 'PDA Syntax Analyzer',
        expected: 'Rejected: Consecutive operators',
        type: 'pda_reject',
        check: (res) => !res.isValid && res.errorMessage.includes('consecutive operators')
      },
      {
        id: 7,
        expr: '5..2 + 1',
        stage: 'DFA Lexical Analyzer',
        expected: 'Rejected: Consecutive decimal points',
        type: 'dfa_reject',
        check: (res) => !res.isValid && res.errorMessage.includes('decimal points')
      },
      {
        id: 8,
        expr: '5 / 0',
        stage: 'Arithmetic Evaluator',
        expected: 'Rejected: Division-by-zero error',
        type: 'eval_reject',
        check: (res) => !res.isValid && res.errorMessage.includes('Division-by-zero')
      },
      {
        id: 9,
        expr: 'abc + 2',
        stage: 'DFA Lexical Analyzer',
        expected: 'Rejected: Unsupported characters',
        type: 'dfa_reject',
        check: (res) => !res.isValid && res.errorMessage.includes('Unsupported character')
      },
      {
        id: 10,
        expr: '111+11',
        stage: 'Genuine Unary TM',
        expected: 'Tape Result = 5 (11111)',
        type: 'unary_tm',
        check: (res) => res.isValid && res.result.includes('5')
      },
      {
        id: 11,
        expr: '1011',
        stage: 'Genuine Binary Incrementer TM',
        expected: 'Tape Result = 1100₂ (12)',
        type: 'binary_tm',
        check: (res) => res.isValid && res.result.includes('1100')
      },
      {
        id: 12,
        expr: '()',
        stage: 'PDA Syntax Analyzer',
        expected: 'Rejected: Empty parentheses',
        type: 'pda_reject',
        check: (res) => !res.isValid && res.errorMessage.includes('empty parentheses')
      },
      {
        id: 13,
        expr: '5 3 + 2',
        stage: 'PDA Syntax Analyzer',
        expected: 'Rejected: Adjacent numbers',
        type: 'pda_reject',
        check: (res) => !res.isValid && res.errorMessage.includes('adjacent numbers')
      }
    ];

    this.bindEvents();
    this.renderTestTable();
  }

  bindEvents() {
    if (this.runAllBtn) {
      this.runAllBtn.addEventListener('click', () => this.runAllTests());
    }
  }

  renderTestTable() {
    if (!this.tableBody) return;
    let html = '';
    this.testCases.forEach(test => {
      html += `
        <tr id="testRow_${test.id}">
          <td><strong>${test.id}</strong></td>
          <td><code>${test.expr}</code></td>
          <td><span class="stage1-class-pill">${test.stage}</span></td>
          <td>${test.expected}</td>
          <td id="testActual_${test.id}">—</td>
          <td id="testVerdict_${test.id}"><span class="test-badge-pending">PENDING</span></td>
          <td>
            <button class="sim-btn sim-btn-ghost test-run-btn" data-expr="${test.expr}">
              Load in Calculator
            </button>
          </td>
        </tr>
      `;
    });
    this.tableBody.innerHTML = html;

    this.tableBody.querySelectorAll('.test-run-btn').forEach(btn => {
      btn.addEventListener('click', () => {
        const expr = btn.dataset.expr;
        if (this.calcUI) {
          this.calcUI.input.value = expr;
          this.calcUI.switchSection('calculator');
          document.querySelectorAll('.nav-pill').forEach(p => p.classList.remove('active'));
          const calcNav = document.querySelector('[data-section="calculator"]');
          if (calcNav) calcNav.classList.add('active');
          setTimeout(() => this.calcUI.processExpression(), 200);
        }
      });
    });

    if (this.statTotal) this.statTotal.textContent = String(this.testCases.length);
  }

  async runAllTests() {
    const startTime = performance.now();
    let passedCount = 0;
    let failedCount = 0;

    for (const test of this.testCases) {
      const actualCell = document.getElementById(`testActual_${test.id}`);
      const verdictCell = document.getElementById(`testVerdict_${test.id}`);

      let testResult;
      let actualDisplay = '';
      let isPass = false;

      if (test.type === 'dfa_reject') {
        const dfaRes = dfaLexer(test.expr);
        testResult = dfaRes;
        actualDisplay = dfaRes.isValid ? 'Valid DFA' : dfaRes.errorMessage;
        isPass = test.check(dfaRes);
      } else if (test.type === 'pda_reject') {
        const dfaRes = dfaLexer(test.expr);
        if (!dfaRes.isValid) {
          testResult = dfaRes;
          actualDisplay = `DFA rejected: ${dfaRes.errorMessage}`;
          isPass = false;
        } else {
          const pdaRes = pdaParser(dfaRes.tokens);
          testResult = pdaRes;
          actualDisplay = pdaRes.isValid ? 'Valid PDA' : pdaRes.errorMessage;
          isPass = test.check(pdaRes);
        }
      } else if (test.type === 'eval_reject') {
        const dfaRes = dfaLexer(test.expr);
        const pdaRes = pdaParser(dfaRes.tokens);
        const evalRes = arithmeticEvaluator(pdaRes.postfix);
        testResult = evalRes;
        actualDisplay = evalRes.isValid ? `Result = ${evalRes.result}` : evalRes.errorMessage;
        isPass = test.check(evalRes);
      } else if (test.type === 'eval') {
        const dfaRes = dfaLexer(test.expr);
        const pdaRes = pdaParser(dfaRes.tokens);
        const evalRes = arithmeticEvaluator(pdaRes.postfix);
        testResult = evalRes;
        actualDisplay = evalRes.isValid ? `Result = ${evalRes.result}` : evalRes.errorMessage;
        isPass = test.check(evalRes);
      } else if (test.type === 'unary_tm') {
        const tmRes = runUnaryAdditionTM(test.expr);
        actualDisplay = tmRes.result;
        isPass = test.check(tmRes);
      } else if (test.type === 'binary_tm') {
        const binRes = runBinaryIncrementerTM(test.expr);
        actualDisplay = binRes.result;
        isPass = test.check(binRes);
      }

      if (actualCell) actualCell.textContent = actualDisplay;
      if (verdictCell) {
        verdictCell.innerHTML = isPass
          ? '<span class="test-badge-pass">PASS</span>'
          : '<span class="test-badge-fail">FAIL</span>';
      }

      if (isPass) passedCount++;
      else failedCount++;

      await new Promise(r => setTimeout(r, 40));
    }

    const duration = Math.round(performance.now() - startTime);
    if (this.statPassed) this.statPassed.textContent = String(passedCount);
    if (this.statFailed) this.statFailed.textContent = String(failedCount);
    if (this.statTime) this.statTime.textContent = `${duration}ms`;
  }
}




// ==========================================================================
// CALCULATOR UI CONTROLLER (3-Stage Pipeline Integration)
// ==========================================================================

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

    // Stage cards
    this.stage1Card = document.getElementById('stage1Card');
    this.stage2Card = document.getElementById('stage2Card');
    this.stage3Card = document.getElementById('stage3Card');

    // Step indicators
    this.step1 = document.getElementById('step1Indicator');
    this.step2 = document.getElementById('step2Indicator');
    this.step3 = document.getElementById('step3Indicator');

    // Stage 1 DFA Lexer Visualizer Controller
    this.dfaVisualizer = new DFALexerVisualizer();

    // Stage 2 PDA Syntax Analyzer Visualizer Controller
    this.pdaVisualizer = new PDAParserVisualizer();

    // Stage 3 TM & Evaluator Visualizer Controller
    this.tmVisualizer = new TMVisualizer();

    // Formal Automata Workbench Controller
    this.workbench = new WorkbenchController();

    // Automated Test Suite Runner
    this.testRunner = new AutomataTestRunner(this);

    this.bindEvents();
    this.initSections();
  }

  bindEvents() {
    if (this.parseBtn) {
      this.parseBtn.addEventListener('click', () => this.processExpression());
    }
    if (this.input) {
      this.input.addEventListener('keydown', (e) => {
        if (e.key === 'Enter') this.processExpression();
      });
    }

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
        const calcNav = document.querySelector('[data-section="calculator"]');
        if (calcNav) calcNav.classList.add('active');

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
    this.switchSection('calculator');
  }

  switchSection(section) {
    const calcSections = document.querySelectorAll('.hero, .pipeline-section');
    const theorySection = document.getElementById('theory');
    const examplesSection = document.getElementById('examples');
    const simulatorSection = document.getElementById('simulator');
    const workbenchSection = document.getElementById('workbench');
    const testsSection = document.getElementById('tests');

    calcSections.forEach(el => el.style.display = section === 'calculator' ? '' : 'none');
    if (theorySection) theorySection.style.display = section === 'theory' ? '' : 'none';
    if (examplesSection) examplesSection.style.display = section === 'examples' ? '' : 'none';
    if (simulatorSection) simulatorSection.style.display = section === 'simulator' ? '' : 'none';
    if (workbenchSection) workbenchSection.style.display = section === 'workbench' ? '' : 'none';
    if (testsSection) testsSection.style.display = section === 'tests' ? '' : 'none';

    if (section === 'simulator' && typeof simController !== 'undefined' && simController) {
      simController.init();
    }
  }

  resetUI() {
    if (this.tokenStream) this.tokenStream.innerHTML = '<div class="token-placeholder">Processing...</div>';
    if (this.postfixOutput) this.postfixOutput.innerHTML = '<div class="token-placeholder">Processing...</div>';
    if (this.resultDisplay) this.resultDisplay.innerHTML = '<div class="token-placeholder">Processing...</div>';
    if (this.errorCard) this.errorCard.style.display = 'none';
    if (this.progressBar) this.progressBar.style.width = '0%';

    // Reset stage cards
    [this.stage1Card, this.stage2Card, this.stage3Card].forEach(card => {
      if (card) {
        card.classList.remove('active');
        card.classList.remove('done');
      }
    });

    // Reset step indicators
    [this.step1, this.step2, this.step3].forEach(step => {
      if (step) {
        step.classList.remove('active');
        step.classList.remove('done');
      }
    });

    // Reset DFA highlights
    document.querySelectorAll('.dfa-state.highlight, .dfa-transition.highlight').forEach(el => {
      el.classList.remove('highlight');
    });

    if (this.dfaVisualizer) this.dfaVisualizer.pause();
    if (this.pdaVisualizer) this.pdaVisualizer.pause();
    if (this.tmVisualizer) this.tmVisualizer.pause();
  }

  showError(message) {
    if (this.errorCard) this.errorCard.style.display = 'flex';
    if (this.errorMessage) this.errorMessage.textContent = message;
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
      this.activateStage(1);
      const lexResult = dfaLexer(expression);
      this.dfaVisualizer.load(
        lexResult.trace,
        lexResult.tokens,
        lexResult.isValid,
        lexResult.errorMessage
      );

      // Update Workbench with DFA data
      if (this.workbench) {
        this.workbench.updateFromSimulation(lexResult, null, null, expression);
      }

      // Step-by-step DFA animation
      await this.dfaVisualizer.playAll();

      if (!lexResult.isValid) {
        throw new Error(lexResult.errorMessage || 'Lexical error: expression rejected by DFA');
      }
      this.markStageDone(1);

      // ---- STAGE 2: PDA Syntax Analyzer ----
      this.activateStage(2);
      const parseResult = pdaParser(lexResult.tokens);
      this.pdaVisualizer.load(
        parseResult.trace,
        parseResult.postfix,
        parseResult.isValid,
        parseResult.errorMessage
      );

      // Update Workbench with PDA data
      if (this.workbench) {
        this.workbench.updateFromSimulation(lexResult, parseResult, null, expression);
      }

      // Step-by-step PDA animation
      await this.pdaVisualizer.playAll();

      if (!parseResult.isValid) {
        throw new Error(parseResult.errorMessage || 'Syntax error: expression rejected by PDA');
      }
      this.markStageDone(2);

      // ---- STAGE 3: TM & Evaluator ----
      this.activateStage(3);
      const evalResult = arithmeticEvaluator(parseResult.postfix);
      this.tmVisualizer.loadEvaluator(
        evalResult.steps,
        evalResult.result,
        evalResult.isValid,
        evalResult.errorMessage,
        parseResult.postfix
      );

      // Update Workbench with TM data
      if (this.workbench) {
        this.workbench.updateFromSimulation(lexResult, parseResult, evalResult, expression);
      }

      // Step-by-step TM animation
      await this.tmVisualizer.playAll();

      if (!evalResult.isValid) {
        throw new Error(evalResult.errorMessage || 'Evaluation error');
      }
      this.markStageDone(3);

    } catch (error) {
      this.showError(error.message);
    }
  }

  activateStage(num) {
    const card = [this.stage1Card, this.stage2Card, this.stage3Card][num - 1];
    const step = [this.step1, this.step2, this.step3][num - 1];
    if (card) card.classList.add('active');
    if (step) step.classList.add('active');
  }

  markStageDone(num) {
    const card = [this.stage1Card, this.stage2Card, this.stage3Card][num - 1];
    const step = [this.step1, this.step2, this.step3][num - 1];
    if (card) {
      card.classList.remove('active');
      card.classList.add('done');
    }
    if (step) {
      step.classList.remove('active');
      step.classList.add('done');
    }
    if (this.progressBar) {
      this.progressBar.style.width = `${(num / 3) * 100}%`;
    }
  }
}


// =============================================
// INTERACTIVE AUTOMATA SIMULATORS
// DFA / PDA / TM — Full working simulations
// =============================================

// ========== DFA SIMULATOR ==========

const DFA_PRESETS = {
  binary_even_zeros: {
    name: 'Binary strings with even number of 0s',
    states: ['q0', 'q1'],
    alphabet: ['0', '1'],
    startState: 'q0',
    acceptStates: ['q0'],
    defaultInput: '01001',
    transitions: {
      'q0,0': 'q1',
      'q0,1': 'q0',
      'q1,0': 'q0',
      'q1,1': 'q1'
    }
  },
  ends_with_01: {
    name: 'Strings ending with "01"',
    states: ['q0', 'q1', 'q2'],
    alphabet: ['0', '1'],
    startState: 'q0',
    acceptStates: ['q2'],
    defaultInput: '1001',
    transitions: {
      'q0,0': 'q1',
      'q0,1': 'q0',
      'q1,0': 'q1',
      'q1,1': 'q2',
      'q2,0': 'q1',
      'q2,1': 'q0'
    }
  },
  divisible_by_3: {
    name: 'Binary number divisible by 3',
    states: ['q0', 'q1', 'q2'],
    alphabet: ['0', '1'],
    startState: 'q0',
    acceptStates: ['q0'],
    defaultInput: '110',
    transitions: {
      'q0,0': 'q0',
      'q0,1': 'q1',
      'q1,0': 'q2',
      'q1,1': 'q0',
      'q2,0': 'q1',
      'q2,1': 'q2'
    }
  },
  contains_aba: {
    name: 'Strings containing "aba" over {a,b}',
    states: ['q0', 'q1', 'q2', 'q3'],
    alphabet: ['a', 'b'],
    startState: 'q0',
    acceptStates: ['q3'],
    defaultInput: 'babab',
    transitions: {
      'q0,a': 'q1',
      'q0,b': 'q0',
      'q1,a': 'q1',
      'q1,b': 'q2',
      'q2,a': 'q3',
      'q2,b': 'q0',
      'q3,a': 'q3',
      'q3,b': 'q3'
    }
  }
};

class DFASimulator {
  constructor() {
    this.machine = null;
    this.currentState = null;
    this.inputString = '';
    this.inputPos = 0;
    this.traceLog = [];
    this.isRunning = false;
    this.isFinished = false;

    this.bindElements();
    this.bindEvents();
    this.loadPreset('binary_even_zeros');
  }

  bindElements() {
    this.presetSelect = document.getElementById('dfaPreset');
    this.customConfig = document.getElementById('dfaCustomConfig');
    this.inputField = document.getElementById('dfaSimInput');
    this.speedSlider = document.getElementById('dfaSimSpeed');
    this.tapeCells = document.getElementById('dfaSimTapeCells');
    this.diagram = document.getElementById('dfaSimDiagram');
    this.transTable = document.getElementById('dfaSimTransTable');
    this.trace = document.getElementById('dfaSimTrace');
    this.verdict = document.getElementById('dfaSimVerdict');

    // Formal displays
    this.statesDisplay = document.getElementById('dfaSimStatesDisplay');
    this.alphabetDisplay = document.getElementById('dfaSimAlphabetDisplay');
    this.startDisplay = document.getElementById('dfaSimStartDisplay');
    this.acceptDisplay = document.getElementById('dfaSimAcceptDisplay');
  }

  bindEvents() {
    this.presetSelect.addEventListener('change', () => {
      const val = this.presetSelect.value;
      if (val === 'custom') {
        this.customConfig.style.display = 'block';
      } else {
        this.customConfig.style.display = 'none';
        this.loadPreset(val);
      }
    });

    document.getElementById('dfaApplyCustom').addEventListener('click', () => this.applyCustom());
    document.getElementById('dfaSimStep').addEventListener('click', () => this.step());
    document.getElementById('dfaSimRun').addEventListener('click', () => this.runAll());
    document.getElementById('dfaSimReset').addEventListener('click', () => this.reset());
  }

  loadPreset(key) {
    const preset = DFA_PRESETS[key];
    if (!preset) return;
    this.machine = { ...preset };
    if (preset.defaultInput !== undefined) {
      this.inputField.value = preset.defaultInput;
    }
    this.updateFormalDisplay();
    this.renderTransitionTable();
    this.renderDiagram();
    this.reset();
  }

  applyCustom() {
    try {
      const states = document.getElementById('dfaCustomStates').value.split(',').map(s => s.trim()).filter(Boolean);
      const alphabet = document.getElementById('dfaCustomAlphabet').value.split(',').map(s => s.trim()).filter(Boolean);
      const startState = document.getElementById('dfaCustomStart').value.trim();
      const acceptStates = document.getElementById('dfaCustomAccept').value.split(',').map(s => s.trim()).filter(Boolean);
      const transLines = document.getElementById('dfaCustomTransitions').value.trim().split('\n');
      
      const transitions = {};
      for (const line of transLines) {
        const match = line.trim().match(/^(\S+),(\S+)→(\S+)$/);
        if (match) {
          transitions[`${match[1]},${match[2]}`] = match[3];
        }
      }

      this.machine = { states, alphabet, startState, acceptStates, transitions, name: 'Custom DFA' };
      this.updateFormalDisplay();
      this.renderTransitionTable();
      this.renderDiagram();
      this.reset();
    } catch (e) {
      alert('Error parsing custom DFA: ' + e.message);
    }
  }

  updateFormalDisplay() {
    if (!this.machine) return;
    this.statesDisplay.textContent = `{${this.machine.states.join(', ')}}`;
    this.alphabetDisplay.textContent = `{${this.machine.alphabet.join(', ')}}`;
    this.startDisplay.textContent = this.machine.startState;
    this.acceptDisplay.textContent = `{${this.machine.acceptStates.join(', ')}}`;
  }

  renderTransitionTable() {
    if (!this.machine) return;
    const { states, alphabet, transitions } = this.machine;

    let html = '<table><thead><tr><th>δ</th>';
    for (const sym of alphabet) {
      html += `<th>${sym}</th>`;
    }
    html += '</tr></thead><tbody>';

    for (const state of states) {
      html += `<tr><td class="sim-trans-state-col">${state}</td>`;
      for (const sym of alphabet) {
        const key = `${state},${sym}`;
        const next = transitions[key] || '—';
        html += `<td id="dfaTrans_${state}_${sym}">${next}</td>`;
      }
      html += '</tr>';
    }
    html += '</tbody></table>';
    this.transTable.innerHTML = html;
  }

  renderDiagram() {
    if (!this.machine) return;
    const { states, alphabet, transitions, startState, acceptStates } = this.machine;
    const n = states.length;

    // Layout states in a circle
    const cx = 300, cy = 140, radius = Math.min(110, 40 * n);
    const positions = {};
    states.forEach((s, i) => {
      const angle = (2 * Math.PI * i / n) - Math.PI / 2;
      positions[s] = {
        x: cx + radius * Math.cos(angle),
        y: cy + radius * Math.sin(angle)
      };
    });

    const svgW = 600, svgH = 280;
    let svg = `<svg viewBox="0 0 ${svgW} ${svgH}" xmlns="http://www.w3.org/2000/svg">`;

    // Defs for arrowheads
    svg += `<defs>
      <marker id="simArrow" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-auto">
        <path d="M0 0 L10 5 L0 10z" class="sim-svg-arrow"/>
      </marker>
      <marker id="simArrowActive" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-auto">
        <path d="M0 0 L10 5 L0 10z" fill="rgba(251,191,36,0.8)"/>
      </marker>
    </defs>`;

    // Start arrow
    const sp = positions[startState];
    svg += `<line x1="${sp.x - 55}" y1="${sp.y}" x2="${sp.x - 28}" y2="${sp.y}" stroke="rgba(168,85,247,0.4)" stroke-width="1.5" marker-end="url(#simArrow)"/>`;

    // Transitions (edges)
    const drawnEdges = {};
    for (const key of Object.keys(transitions)) {
      const [from, sym] = key.split(',');
      const to = transitions[key];
      const edgeKey = `${from}->${to}`;
      if (!drawnEdges[edgeKey]) drawnEdges[edgeKey] = [];
      drawnEdges[edgeKey].push(sym);
    }

    for (const edgeKey of Object.keys(drawnEdges)) {
      const [from, to] = edgeKey.split('->');
      const symbols = drawnEdges[edgeKey].join(',');
      const fp = positions[from];
      const tp = positions[to];

      if (from === to) {
        // Self-loop
        const loopR = 20;
        svg += `<path d="M${fp.x - 10} ${fp.y - 22} A${loopR} ${loopR} 0 1 1 ${fp.x + 10} ${fp.y - 22}" 
          fill="none" class="sim-svg-trans" id="dfaSimEdge_${from}_${to}" marker-end="url(#simArrow)"/>`;
        svg += `<text x="${fp.x}" y="${fp.y - 48}" class="sim-svg-trans-label">${symbols}</text>`;
      } else {
        // Check for reverse edge to curve
        const reverseKey = `${to}->${from}`;
        const hasReverse = drawnEdges[reverseKey];

        // Calculate control point
        const mx = (fp.x + tp.x) / 2;
        const my = (fp.y + tp.y) / 2;
        const dx = tp.x - fp.x;
        const dy = tp.y - fp.y;
        const len = Math.sqrt(dx * dx + dy * dy);
        const offsetDist = hasReverse ? 25 : 0;
        const nx = -dy / len * offsetDist;
        const ny = dx / len * offsetDist;
        const cpx = mx + nx;
        const cpy = my + ny;

        // Calculate start/end points on circle edge
        const r = 25;
        const angleTo = Math.atan2(cpy - fp.y, cpx - fp.x);
        const angleFrom = Math.atan2(cpy - tp.y, cpx - tp.x);
        const sx = fp.x + r * Math.cos(angleTo);
        const sy = fp.y + r * Math.sin(angleTo);
        const ex = tp.x + r * Math.cos(angleFrom);
        const ey = tp.y + r * Math.sin(angleFrom);

        svg += `<path d="M${sx} ${sy} Q${cpx} ${cpy} ${ex} ${ey}" 
          class="sim-svg-trans" id="dfaSimEdge_${from}_${to}" marker-end="url(#simArrow)"/>`;
        svg += `<text x="${cpx}" y="${cpy - 5}" class="sim-svg-trans-label">${symbols}</text>`;
      }
    }

    // States (circles)
    for (const state of states) {
      const p = positions[state];
      const isAccept = acceptStates.includes(state);
      svg += `<circle cx="${p.x}" cy="${p.y}" r="25" class="sim-svg-state${isAccept ? ' sim-svg-accept' : ''}" id="dfaSimState_${state}"/>`;
      if (isAccept) {
        svg += `<circle cx="${p.x}" cy="${p.y}" r="20" class="sim-svg-state-inner"/>`;
      }
      svg += `<text x="${p.x}" y="${p.y}" class="sim-svg-label">${state}</text>`;
    }

    svg += '</svg>';
    this.diagram.innerHTML = svg;
  }

  reset() {
    this.currentState = this.machine ? this.machine.startState : null;
    this.inputString = this.inputField.value;
    this.inputPos = 0;
    this.traceLog = [];
    this.isRunning = false;
    this.isFinished = false;

    // Reset tape
    this.renderTape();

    // Reset trace
    this.trace.innerHTML = '<div class="sim-trace-placeholder">Execution trace will appear here as the automaton processes input...</div>';
    this.verdict.className = 'sim-verdict';
    this.verdict.style.display = 'none';
    this.verdict.textContent = '';

    // Reset diagram highlights
    this.clearDiagramHighlights();
    if (this.currentState) {
      const el = document.getElementById(`dfaSimState_${this.currentState}`);
      if (el) el.classList.add('sim-svg-active');
    }

    // Clear table highlights
    document.querySelectorAll('.sim-trans-highlight').forEach(el => el.classList.remove('sim-trans-highlight'));
  }

  renderTape() {
    this.tapeCells.innerHTML = '';
    const str = this.inputField.value;
    for (let i = 0; i < str.length; i++) {
      const cell = document.createElement('div');
      cell.className = 'sim-tape-cell';
      if (i < this.inputPos) cell.classList.add('processed');
      if (i === this.inputPos && !this.isFinished) cell.classList.add('current');
      cell.textContent = str[i];
      this.tapeCells.appendChild(cell);
    }
    // Blank at end
    const blank = document.createElement('div');
    blank.className = 'sim-tape-cell blank';
    blank.textContent = '□';
    if (this.inputPos >= str.length && !this.isFinished) blank.classList.add('current');
    this.tapeCells.appendChild(blank);
  }

  clearDiagramHighlights() {
    document.querySelectorAll('.sim-svg-active').forEach(el => el.classList.remove('sim-svg-active'));
    document.querySelectorAll('.sim-svg-active-trans').forEach(el => el.classList.remove('sim-svg-active-trans'));
    document.querySelectorAll('.sim-trans-highlight').forEach(el => el.classList.remove('sim-trans-highlight'));
  }

  step() {
    if (!this.machine || this.isFinished) return;

    this.inputString = this.inputField.value;

    // First step — clear placeholder
    if (this.inputPos === 0 && this.traceLog.length === 0) {
      this.trace.innerHTML = '';
      this.renderTape();
    }

    if (this.inputPos >= this.inputString.length) {
      // No more input — decide accept/reject
      this.finalize();
      return;
    }

    const sym = this.inputString[this.inputPos];
    const prevState = this.currentState;
    const key = `${prevState},${sym}`;
    const nextState = this.machine.transitions[key];

    this.clearDiagramHighlights();

    if (!nextState) {
      // No transition — reject (dead state)
      this.addTraceRow(this.traceLog.length + 1, prevState, sym, 'DEAD', '(no transition)');
      this.isFinished = true;
      this.showVerdict(false, `REJECTED — No transition δ(${prevState}, ${sym})`);
      this.renderTape();
      return;
    }

    // Highlight transition
    const edgeEl = document.getElementById(`dfaSimEdge_${prevState}_${nextState}`);
    if (edgeEl) edgeEl.classList.add('sim-svg-active-trans');

    // Highlight table cell
    const tdEl = document.getElementById(`dfaTrans_${prevState}_${sym}`);
    if (tdEl) tdEl.classList.add('sim-trans-highlight');

    this.currentState = nextState;
    this.inputPos++;

    // Add trace row
    this.addTraceRow(this.traceLog.length + 1, prevState, sym, nextState, `δ(${prevState}, ${sym}) = ${nextState}`);
    this.traceLog.push({ from: prevState, symbol: sym, to: nextState });

    // Highlight current state
    const stateEl = document.getElementById(`dfaSimState_${nextState}`);
    if (stateEl) stateEl.classList.add('sim-svg-active');

    // Update tape
    this.renderTape();

    // If input exhausted, auto-finalize on next step
    if (this.inputPos >= this.inputString.length) {
      // Don't auto-finalize; let user click step one more time
    }
  }

  finalize() {
    const accepted = this.machine.acceptStates.includes(this.currentState);
    this.isFinished = true;
    this.renderTape();
    
    if (accepted) {
      this.showVerdict(true, `✓ ACCEPTED — Halted in accept state ${this.currentState} ∈ F`);
    } else {
      this.showVerdict(false, `✗ REJECTED — Halted in state ${this.currentState} ∉ F = {${this.machine.acceptStates.join(', ')}}`);
    }
  }

  async runAll() {
    if (!this.machine || this.isRunning) return;
    this.isRunning = true;
    this.reset();
    this.trace.innerHTML = '';
    this.renderTape();

    const speed = 1600 - parseInt(this.speedSlider.value);

    while (!this.isFinished) {
      this.step();
      await new Promise(r => setTimeout(r, speed));
    }

    this.isRunning = false;
  }

  addTraceRow(stepNum, from, symbol, to, desc) {
    const row = document.createElement('div');
    row.className = 'sim-trace-row';
    row.innerHTML = `
      <span class="sim-trace-step">${stepNum}</span>
      <span class="sim-trace-state">${from}</span>
      <span class="sim-trace-input">'${symbol}'</span>
      <span class="sim-trace-arrow">→</span>
      <span class="sim-trace-next">${to}</span>
      <span class="sim-trace-stack">${desc}</span>
    `;
    this.trace.appendChild(row);
    this.trace.scrollTop = this.trace.scrollHeight;
  }

  showVerdict(accepted, message) {
    this.verdict.textContent = message;
    this.verdict.className = `sim-verdict ${accepted ? 'accepted' : 'rejected'}`;
    this.verdict.style.display = 'block';
  }
}


// ========== PDA SIMULATOR ==========

const PDA_PRESETS = {
  balanced_parens: {
    name: 'Balanced Parentheses',
    states: ['q0', 'q1', 'q_accept'],
    alphabet: ['(', ')'],
    stackAlphabet: ['Z0', '('],
    startState: 'q0',
    initialStack: 'Z0',
    acceptStates: ['q_accept'],
    defaultInput: '(()())',
    transitions: [
      { from: 'q0', input: '(', stackTop: 'Z0', to: 'q0', stackPush: '(Z0' },
      { from: 'q0', input: '(', stackTop: '(', to: 'q0', stackPush: '((' },
      { from: 'q0', input: ')', stackTop: '(', to: 'q0', stackPush: 'ε' },
      { from: 'q0', input: 'ε', stackTop: 'Z0', to: 'q_accept', stackPush: 'Z0' }
    ]
  },
  anbn: {
    name: 'a^n b^n (Equal a\'s then b\'s)',
    states: ['q0', 'q1', 'q_accept'],
    alphabet: ['a', 'b'],
    stackAlphabet: ['Z0', 'A'],
    startState: 'q0',
    initialStack: 'Z0',
    acceptStates: ['q_accept'],
    defaultInput: 'aaabbb',
    transitions: [
      { from: 'q0', input: 'a', stackTop: 'Z0', to: 'q0', stackPush: 'AZ0' },
      { from: 'q0', input: 'a', stackTop: 'A', to: 'q0', stackPush: 'AA' },
      { from: 'q0', input: 'b', stackTop: 'A', to: 'q1', stackPush: 'ε' },
      { from: 'q1', input: 'b', stackTop: 'A', to: 'q1', stackPush: 'ε' },
      { from: 'q1', input: 'ε', stackTop: 'Z0', to: 'q_accept', stackPush: 'Z0' }
    ]
  },
  palindrome_marker: {
    name: 'w # wᴿ Palindromes with center marker',
    states: ['q0', 'q1', 'q_accept'],
    alphabet: ['a', 'b', '#'],
    stackAlphabet: ['Z0', 'A', 'B'],
    startState: 'q0',
    initialStack: 'Z0',
    acceptStates: ['q_accept'],
    defaultInput: 'ab#ba',
    transitions: [
      { from: 'q0', input: 'a', stackTop: 'Z0', to: 'q0', stackPush: 'AZ0' },
      { from: 'q0', input: 'b', stackTop: 'Z0', to: 'q0', stackPush: 'BZ0' },
      { from: 'q0', input: 'a', stackTop: 'A', to: 'q0', stackPush: 'AA' },
      { from: 'q0', input: 'a', stackTop: 'B', to: 'q0', stackPush: 'AB' },
      { from: 'q0', input: 'b', stackTop: 'A', to: 'q0', stackPush: 'BA' },
      { from: 'q0', input: 'b', stackTop: 'B', to: 'q0', stackPush: 'BB' },
      { from: 'q0', input: '#', stackTop: 'A', to: 'q1', stackPush: 'A' },
      { from: 'q0', input: '#', stackTop: 'B', to: 'q1', stackPush: 'B' },
      { from: 'q0', input: '#', stackTop: 'Z0', to: 'q1', stackPush: 'Z0' },
      { from: 'q1', input: 'a', stackTop: 'A', to: 'q1', stackPush: 'ε' },
      { from: 'q1', input: 'b', stackTop: 'B', to: 'q1', stackPush: 'ε' },
      { from: 'q1', input: 'ε', stackTop: 'Z0', to: 'q_accept', stackPush: 'Z0' }
    ]
  }
};

class PDASimulator {
  constructor() {
    this.machine = null;
    this.currentState = null;
    this.stack = [];
    this.inputString = '';
    this.inputPos = 0;
    this.traceLog = [];
    this.isRunning = false;
    this.isFinished = false;

    this.bindElements();
    this.bindEvents();
    this.loadPreset('balanced_parens');
  }

  bindElements() {
    this.presetSelect = document.getElementById('pdaPreset');
    this.customConfig = document.getElementById('pdaCustomConfig');
    this.inputField = document.getElementById('pdaSimInput');
    this.speedSlider = document.getElementById('pdaSimSpeed');
    this.tapeCells = document.getElementById('pdaSimTapeCells');
    this.currentStateDisplay = document.getElementById('pdaSimCurrentState');
    this.stackVis = document.getElementById('pdaSimStackVis');
    this.transTable = document.getElementById('pdaSimTransTable');
    this.trace = document.getElementById('pdaSimTrace');
    this.verdict = document.getElementById('pdaSimVerdict');

    this.statesDisplay = document.getElementById('pdaSimStatesDisplay');
    this.alphabetDisplay = document.getElementById('pdaSimAlphabetDisplay');
    this.stackAlphaDisplay = document.getElementById('pdaSimStackAlphaDisplay');
    this.startDisplay = document.getElementById('pdaSimStartDisplay');
    this.acceptDisplay = document.getElementById('pdaSimAcceptDisplay');
  }

  bindEvents() {
    this.presetSelect.addEventListener('change', () => {
      const val = this.presetSelect.value;
      if (val === 'custom') {
        this.customConfig.style.display = 'block';
      } else {
        this.customConfig.style.display = 'none';
        this.loadPreset(val);
      }
    });

    document.getElementById('pdaApplyCustom').addEventListener('click', () => this.applyCustom());
    document.getElementById('pdaSimStep').addEventListener('click', () => this.step());
    document.getElementById('pdaSimRun').addEventListener('click', () => this.runAll());
    document.getElementById('pdaSimReset').addEventListener('click', () => this.reset());
  }

  loadPreset(key) {
    const preset = PDA_PRESETS[key];
    if (!preset) return;
    this.machine = JSON.parse(JSON.stringify(preset));
    if (preset.defaultInput !== undefined) {
      this.inputField.value = preset.defaultInput;
    }
    this.updateFormalDisplay();
    this.renderTransitionTable();
    this.reset();
  }

  applyCustom() {
    try {
      const states = document.getElementById('pdaCustomStates').value.split(',').map(s => s.trim()).filter(Boolean);
      const alphabet = document.getElementById('pdaCustomAlphabet').value.split(',').map(s => s.trim()).filter(Boolean);
      const stackAlpha = document.getElementById('pdaCustomStackAlpha').value.split(',').map(s => s.trim()).filter(Boolean);
      const startState = document.getElementById('pdaCustomStart').value.trim();
      const initialStack = document.getElementById('pdaCustomInitStack').value.trim();
      const acceptStates = document.getElementById('pdaCustomAccept').value.split(',').map(s => s.trim()).filter(Boolean);
      const transLines = document.getElementById('pdaCustomTransitions').value.trim().split('\n');

      const transitions = [];
      for (const line of transLines) {
        // Format: state,input,stackTop→nextState,stackPush
        const match = line.trim().match(/^(\S+),(\S+),(\S+)→(\S+),(\S+)$/);
        if (match) {
          transitions.push({
            from: match[1],
            input: match[2],
            stackTop: match[3],
            to: match[4],
            stackPush: match[5]
          });
        }
      }

      this.machine = { states, alphabet, stackAlphabet: stackAlpha, startState, initialStack, acceptStates, transitions, name: 'Custom PDA' };
      this.updateFormalDisplay();
      this.renderTransitionTable();
      this.reset();
    } catch (e) {
      alert('Error parsing custom PDA: ' + e.message);
    }
  }

  updateFormalDisplay() {
    if (!this.machine) return;
    this.statesDisplay.textContent = `{${this.machine.states.join(', ')}}`;
    this.alphabetDisplay.textContent = `{${this.machine.alphabet.join(', ')}}`;
    this.stackAlphaDisplay.textContent = `{${this.machine.stackAlphabet.join(', ')}}`;
    this.startDisplay.textContent = this.machine.startState;
    this.acceptDisplay.textContent = `{${this.machine.acceptStates.join(', ')}}`;
  }

  renderTransitionTable() {
    if (!this.machine) return;
    let html = '<table><thead><tr><th>State</th><th>Input</th><th>Stack Top</th><th>→ Next State</th><th>Stack Push</th></tr></thead><tbody>';
    for (const t of this.machine.transitions) {
      html += `<tr>
        <td class="sim-trans-state-col">${t.from}</td>
        <td>${t.input}</td>
        <td>${t.stackTop}</td>
        <td>${t.to}</td>
        <td>${t.stackPush}</td>
      </tr>`;
    }
    html += '</tbody></table>';
    this.transTable.innerHTML = html;
  }

  reset() {
    if (!this.machine) return;
    this.currentState = this.machine.startState;
    this.stack = [this.machine.initialStack];
    this.inputString = this.inputField.value;
    this.inputPos = 0;
    this.traceLog = [];
    this.isRunning = false;
    this.isFinished = false;

    this.renderTape();
    this.renderStack();
    this.currentStateDisplay.textContent = this.currentState;
    this.trace.innerHTML = '<div class="sim-trace-placeholder">Execution trace will appear here...</div>';
    this.verdict.className = 'sim-verdict';
    this.verdict.style.display = 'none';
  }

  renderTape() {
    this.tapeCells.innerHTML = '';
    const str = this.inputField.value;
    for (let i = 0; i < str.length; i++) {
      const cell = document.createElement('div');
      cell.className = 'sim-tape-cell';
      if (i < this.inputPos) cell.classList.add('processed');
      if (i === this.inputPos && !this.isFinished) cell.classList.add('current');
      cell.textContent = str[i];
      this.tapeCells.appendChild(cell);
    }
    const blank = document.createElement('div');
    blank.className = 'sim-tape-cell blank';
    blank.textContent = '□';
    this.tapeCells.appendChild(blank);
  }

  renderStack() {
    this.stackVis.innerHTML = '';
    // Render top to bottom
    for (let i = 0; i < this.stack.length; i++) {
      const item = document.createElement('div');
      item.className = 'sim-pda-stack-item';
      if (this.stack[i] === this.machine.initialStack) {
        item.classList.add('sim-pda-stack-bottom');
      }
      if (i === 0) item.classList.add('sim-pda-stack-new');
      item.textContent = this.stack[i];
      this.stackVis.appendChild(item);
    }
  }

  findTransition(state, input, stackTop) {
    // Look for exact input match first
    for (const t of this.machine.transitions) {
      if (t.from === state && t.input === input && t.stackTop === stackTop) {
        return t;
      }
    }
    return null;
  }

  findEpsilonTransition(state, stackTop) {
    for (const t of this.machine.transitions) {
      if (t.from === state && t.input === 'ε' && t.stackTop === stackTop) {
        return t;
      }
    }
    return null;
  }

  step() {
    if (!this.machine || this.isFinished) return;
    this.inputString = this.inputField.value;

    if (this.inputPos === 0 && this.traceLog.length === 0) {
      this.trace.innerHTML = '';
    }

    const stackTop = this.stack.length > 0 ? this.stack[0] : null;

    // Try reading input symbol first
    if (this.inputPos < this.inputString.length) {
      const sym = this.inputString[this.inputPos];
      const trans = this.findTransition(this.currentState, sym, stackTop);

      if (trans) {
        const prevState = this.currentState;
        // Pop stack top
        this.stack.shift();
        // Push new symbols
        if (trans.stackPush !== 'ε') {
          // Parse stackPush into individual symbols
          const pushSymbols = this.parseStackSymbols(trans.stackPush);
          this.stack.unshift(...pushSymbols);
        }
        this.currentState = trans.to;
        this.inputPos++;

        this.addTraceRow(
          this.traceLog.length + 1,
          `(${prevState}, ${sym}, ${stackTop})`,
          `(${trans.to}, ${trans.stackPush})`,
          `[${this.stack.join(',')}]`
        );
        this.traceLog.push(trans);

        this.currentStateDisplay.textContent = this.currentState;
        this.renderTape();
        this.renderStack();
        return;
      }
    }

    // Try epsilon transition
    const epsTrans = this.findEpsilonTransition(this.currentState, stackTop);
    if (epsTrans) {
      const prevState = this.currentState;
      this.stack.shift();
      if (epsTrans.stackPush !== 'ε') {
        const pushSymbols = this.parseStackSymbols(epsTrans.stackPush);
        this.stack.unshift(...pushSymbols);
      }
      this.currentState = epsTrans.to;

      this.addTraceRow(
        this.traceLog.length + 1,
        `(${prevState}, ε, ${stackTop})`,
        `(${epsTrans.to}, ${epsTrans.stackPush})`,
        `[${this.stack.join(',')}]`
      );
      this.traceLog.push(epsTrans);

      this.currentStateDisplay.textContent = this.currentState;
      this.renderTape();
      this.renderStack();

      // Check if we reached accept state
      if (this.machine.acceptStates.includes(this.currentState)) {
        this.isFinished = true;
        this.showVerdict(true, `✓ ACCEPTED — Reached accept state ${this.currentState}`);
      }
      return;
    }

    // No transition available — check accept or reject
    if (this.inputPos >= this.inputString.length && this.machine.acceptStates.includes(this.currentState)) {
      this.isFinished = true;
      this.showVerdict(true, `✓ ACCEPTED — Input consumed, in accept state ${this.currentState}`);
    } else {
      this.isFinished = true;
      this.showVerdict(false, `✗ REJECTED — No valid transition from (${this.currentState}, ${this.inputPos < this.inputString.length ? this.inputString[this.inputPos] : 'ε'}, ${stackTop || '∅'})`);
    }
    this.renderTape();
  }

  parseStackSymbols(pushStr) {
    // Handle multi-character stack symbols like "AZ0"
    const symbols = [];
    const knownSymbols = this.machine.stackAlphabet.sort((a, b) => b.length - a.length);
    let remaining = pushStr;
    while (remaining.length > 0) {
      let found = false;
      for (const sym of knownSymbols) {
        if (remaining.startsWith(sym)) {
          symbols.push(sym);
          remaining = remaining.substring(sym.length);
          found = true;
          break;
        }
      }
      if (!found) {
        // Single char fallback
        symbols.push(remaining[0]);
        remaining = remaining.substring(1);
      }
    }
    return symbols;
  }

  async runAll() {
    if (!this.machine || this.isRunning) return;
    this.isRunning = true;
    this.reset();
    this.trace.innerHTML = '';

    const speed = 1600 - parseInt(this.speedSlider.value);
    let safetyCounter = 0;

    while (!this.isFinished && safetyCounter < 200) {
      this.step();
      safetyCounter++;
      await new Promise(r => setTimeout(r, speed));
    }

    if (!this.isFinished) {
      this.isFinished = true;
      this.showVerdict(false, '✗ REJECTED — Maximum steps exceeded (possible infinite loop)');
    }

    this.isRunning = false;
  }

  addTraceRow(stepNum, config, result, stackStr) {
    const row = document.createElement('div');
    row.className = 'sim-trace-row';
    row.innerHTML = `
      <span class="sim-trace-step">${stepNum}</span>
      <span class="sim-trace-state">${config}</span>
      <span class="sim-trace-arrow">⊢</span>
      <span class="sim-trace-next">${result}</span>
      <span class="sim-trace-stack">Stack: ${stackStr}</span>
    `;
    this.trace.appendChild(row);
    this.trace.scrollTop = this.trace.scrollHeight;
  }

  showVerdict(accepted, message) {
    this.verdict.textContent = message;
    this.verdict.className = `sim-verdict ${accepted ? 'accepted' : 'rejected'}`;
    this.verdict.style.display = 'block';
  }
}


// ========== TM SIMULATOR ==========

const TM_PRESETS = {
  binary_increment: {
    name: 'Binary Increment (+1)',
    states: ['q0', 'q_carry', 'q_done', 'q_accept'],
    alphabet: ['0', '1'],
    tapeAlphabet: ['0', '1', '□'],
    startState: 'q0',
    acceptState: 'q_accept',
    rejectState: 'q_reject',
    defaultInput: '1011',
    // Move to rightmost digit first, then carry
    transitions: {
      'q0,0': { write: '0', move: 'R', next: 'q0' },
      'q0,1': { write: '1', move: 'R', next: 'q0' },
      'q0,□': { write: '□', move: 'L', next: 'q_carry' },
      'q_carry,0': { write: '1', move: 'L', next: 'q_done' },
      'q_carry,1': { write: '0', move: 'L', next: 'q_carry' },
      'q_carry,□': { write: '1', move: 'R', next: 'q_accept' },
      'q_done,0': { write: '0', move: 'L', next: 'q_done' },
      'q_done,1': { write: '1', move: 'L', next: 'q_done' },
      'q_done,□': { write: '□', move: 'R', next: 'q_accept' }
    }
  },
  palindrome_check: {
    name: 'Palindrome Checker {0,1}',
    states: ['q0', 'q_saw0', 'q_saw1', 'q_ret0', 'q_ret1', 'q_back', 'q_accept', 'q_reject'],
    alphabet: ['0', '1'],
    tapeAlphabet: ['0', '1', 'X', '□'],
    startState: 'q0',
    acceptState: 'q_accept',
    rejectState: 'q_reject',
    defaultInput: '1001',
    transitions: {
      // Read leftmost, mark it
      'q0,0': { write: 'X', move: 'R', next: 'q_saw0' },
      'q0,1': { write: 'X', move: 'R', next: 'q_saw1' },
      'q0,X': { write: 'X', move: 'R', next: 'q_accept' },
      'q0,□': { write: '□', move: 'R', next: 'q_accept' },
      // Saw 0: go right to find rightmost
      'q_saw0,0': { write: '0', move: 'R', next: 'q_saw0' },
      'q_saw0,1': { write: '1', move: 'R', next: 'q_saw0' },
      'q_saw0,X': { write: 'X', move: 'L', next: 'q_ret0' },
      'q_saw0,□': { write: '□', move: 'L', next: 'q_ret0' },
      // Check rightmost matches 0
      'q_ret0,0': { write: 'X', move: 'L', next: 'q_back' },
      'q_ret0,1': { write: '1', move: 'L', next: 'q_reject' },
      'q_ret0,X': { write: 'X', move: 'L', next: 'q_accept' },
      // Saw 1: go right
      'q_saw1,0': { write: '0', move: 'R', next: 'q_saw1' },
      'q_saw1,1': { write: '1', move: 'R', next: 'q_saw1' },
      'q_saw1,X': { write: 'X', move: 'L', next: 'q_ret1' },
      'q_saw1,□': { write: '□', move: 'L', next: 'q_ret1' },
      // Check rightmost matches 1
      'q_ret1,1': { write: 'X', move: 'L', next: 'q_back' },
      'q_ret1,0': { write: '0', move: 'L', next: 'q_reject' },
      'q_ret1,X': { write: 'X', move: 'L', next: 'q_accept' },
      // Rewind to start
      'q_back,0': { write: '0', move: 'L', next: 'q_back' },
      'q_back,1': { write: '1', move: 'L', next: 'q_back' },
      'q_back,X': { write: 'X', move: 'R', next: 'q0' }
    }
  },
  zero_one_equal: {
    name: 'Equal 0s and 1s',
    states: ['q0', 'q_find1', 'q_find0', 'q_return', 'q_accept', 'q_reject'],
    alphabet: ['0', '1'],
    tapeAlphabet: ['0', '1', 'X', 'Y', '□'],
    startState: 'q0',
    acceptState: 'q_accept',
    rejectState: 'q_reject',
    defaultInput: '0011',
    transitions: {
      // Mark a 0, go find a 1
      'q0,0': { write: 'X', move: 'R', next: 'q_find1' },
      'q0,1': { write: 'Y', move: 'R', next: 'q_find0' },
      'q0,X': { write: 'X', move: 'R', next: 'q0' },
      'q0,Y': { write: 'Y', move: 'R', next: 'q0' },
      'q0,□': { write: '□', move: 'R', next: 'q_accept' },
      // Find matching 1
      'q_find1,0': { write: '0', move: 'R', next: 'q_find1' },
      'q_find1,1': { write: 'Y', move: 'L', next: 'q_return' },
      'q_find1,Y': { write: 'Y', move: 'R', next: 'q_find1' },
      'q_find1,□': { write: '□', move: 'L', next: 'q_reject' },
      // Find matching 0
      'q_find0,1': { write: '1', move: 'R', next: 'q_find0' },
      'q_find0,0': { write: 'X', move: 'L', next: 'q_return' },
      'q_find0,X': { write: 'X', move: 'R', next: 'q_find0' },
      'q_find0,□': { write: '□', move: 'L', next: 'q_reject' },
      // Return to start
      'q_return,0': { write: '0', move: 'L', next: 'q_return' },
      'q_return,1': { write: '1', move: 'L', next: 'q_return' },
      'q_return,X': { write: 'X', move: 'L', next: 'q_return' },
      'q_return,Y': { write: 'Y', move: 'L', next: 'q_return' },
      'q_return,□': { write: '□', move: 'R', next: 'q0' }
    }
  }
};

class TMSimulator {
  constructor() {
    this.machine = null;
    this.currentState = null;
    this.tape = [];
    this.headPos = 0;
    this.stepCount = 0;
    this.isRunning = false;
    this.isFinished = false;

    this.bindElements();
    this.bindEvents();
    this.loadPreset('binary_increment');
  }

  bindElements() {
    this.presetSelect = document.getElementById('tmPreset');
    this.customConfig = document.getElementById('tmCustomConfig');
    this.inputField = document.getElementById('tmSimInput');
    this.speedSlider = document.getElementById('tmSimSpeed');
    this.tapeCellsEl = document.getElementById('tmSimTapeCells');
    this.currentStateEl = document.getElementById('tmSimCurrentState');
    this.headPosEl = document.getElementById('tmSimHeadPos');
    this.stepCountEl = document.getElementById('tmSimStepCount');
    this.headStateLabel = document.getElementById('tmSimHeadStateLabel');
    this.transTable = document.getElementById('tmSimTransTable');
    this.trace = document.getElementById('tmSimTrace');
    this.verdict = document.getElementById('tmSimVerdict');

    this.statesDisplay = document.getElementById('tmSimStatesDisplay');
    this.alphabetDisplay = document.getElementById('tmSimAlphabetDisplay');
    this.tapeAlphaDisplay = document.getElementById('tmSimTapeAlphaDisplay');
    this.startDisplay = document.getElementById('tmSimStartDisplay');
  }

  bindEvents() {
    this.presetSelect.addEventListener('change', () => {
      const val = this.presetSelect.value;
      if (val === 'custom') {
        this.customConfig.style.display = 'block';
      } else {
        this.customConfig.style.display = 'none';
        this.loadPreset(val);
      }
    });

    document.getElementById('tmApplyCustom').addEventListener('click', () => this.applyCustom());
    document.getElementById('tmSimStep').addEventListener('click', () => this.step());
    document.getElementById('tmSimRun').addEventListener('click', () => this.runAll());
    document.getElementById('tmSimReset').addEventListener('click', () => this.reset());
  }

  loadPreset(key) {
    const preset = TM_PRESETS[key];
    if (!preset) return;
    this.machine = JSON.parse(JSON.stringify(preset));
    if (preset.defaultInput !== undefined) {
      this.inputField.value = preset.defaultInput;
    }
    this.updateFormalDisplay();
    this.renderTransitionTable();
    this.reset();
  }

  applyCustom() {
    try {
      const states = document.getElementById('tmCustomStates').value.split(',').map(s => s.trim()).filter(Boolean);
      const alphabet = document.getElementById('tmCustomAlphabet').value.split(',').map(s => s.trim()).filter(Boolean);
      const tapeAlpha = document.getElementById('tmCustomTapeAlpha').value.split(',').map(s => s.trim()).filter(Boolean);
      const startState = document.getElementById('tmCustomStart').value.trim();
      const acceptState = document.getElementById('tmCustomAccept').value.trim();
      const rejectState = document.getElementById('tmCustomReject').value.trim();
      const transLines = document.getElementById('tmCustomTransitions').value.trim().split('\n');

      const transitions = {};
      for (const line of transLines) {
        // Format: state,read→nextState,write,direction
        const match = line.trim().match(/^(\S+),(\S+)→(\S+),(\S+),([LRlr])$/);
        if (match) {
          transitions[`${match[1]},${match[2]}`] = {
            next: match[3],
            write: match[4],
            move: match[5].toUpperCase()
          };
        }
      }

      this.machine = { states, alphabet, tapeAlphabet: tapeAlpha, startState, acceptState, rejectState, transitions, name: 'Custom TM' };
      this.updateFormalDisplay();
      this.renderTransitionTable();
      this.reset();
    } catch (e) {
      alert('Error parsing custom TM: ' + e.message);
    }
  }

  updateFormalDisplay() {
    if (!this.machine) return;
    this.statesDisplay.textContent = `{${this.machine.states.join(', ')}}`;
    this.alphabetDisplay.textContent = `{${this.machine.alphabet.join(', ')}}`;
    this.tapeAlphaDisplay.textContent = `{${this.machine.tapeAlphabet.join(', ')}}`;
    this.startDisplay.textContent = this.machine.startState;
  }

  renderTransitionTable() {
    if (!this.machine) return;
    let html = '<table><thead><tr><th>State</th><th>Read</th><th>Write</th><th>Move</th><th>Next State</th></tr></thead><tbody>';
    for (const key of Object.keys(this.machine.transitions)) {
      const [state, read] = key.split(',');
      const t = this.machine.transitions[key];
      html += `<tr id="tmTransRow_${state}_${read}">
        <td class="sim-trans-state-col">${state}</td>
        <td>${read}</td>
        <td>${t.write}</td>
        <td>${t.move === 'R' ? '→ R' : '← L'}</td>
        <td>${t.next}</td>
      </tr>`;
    }
    html += '</tbody></table>';
    this.transTable.innerHTML = html;
  }

  reset() {
    if (!this.machine) return;
    this.currentState = this.machine.startState;
    this.tape = [];
    const inputStr = this.inputField.value;
    for (const ch of inputStr) {
      this.tape.push(ch);
    }
    // Add blanks on both sides
    this.tape.push('□');
    this.tape.push('□');
    this.tape.unshift('□');

    this.headPos = 1; // Start at first input character (after leading blank)
    this.stepCount = 0;
    this.isRunning = false;
    this.isFinished = false;

    this.renderTape();
    this.updateInfoDisplay();
    this.trace.innerHTML = '<div class="sim-trace-placeholder">Execution trace will appear here...</div>';
    this.verdict.className = 'sim-verdict';
    this.verdict.style.display = 'none';

    // Clear table highlights
    document.querySelectorAll('#tmSimTransTable .sim-trans-highlight').forEach(el => el.classList.remove('sim-trans-highlight'));
  }

  renderTape() {
    this.tapeCellsEl.innerHTML = '';
    for (let i = 0; i < this.tape.length; i++) {
      const cell = document.createElement('div');
      cell.className = 'sim-tape-cell';
      if (this.tape[i] === '□') cell.classList.add('blank');
      if (i === this.headPos) cell.classList.add('current');
      cell.textContent = this.tape[i];
      cell.id = `tmSimTapeCell_${i}`;
      this.tapeCellsEl.appendChild(cell);
    }
  }

  updateInfoDisplay() {
    this.currentStateEl.textContent = this.currentState;
    this.headPosEl.textContent = this.headPos;
    this.stepCountEl.textContent = this.stepCount;
    this.headStateLabel.textContent = this.currentState;
  }

  step() {
    if (!this.machine || this.isFinished) return;

    if (this.stepCount === 0 && this.trace.querySelector('.sim-trace-placeholder')) {
      this.trace.innerHTML = '';
    }

    // Check for accept/reject state
    if (this.currentState === this.machine.acceptState) {
      this.isFinished = true;
      this.showVerdict(true, `✓ ACCEPTED — Reached accept state ${this.currentState}. Tape: ${this.tape.join('')}`);
      return;
    }
    if (this.currentState === this.machine.rejectState) {
      this.isFinished = true;
      this.showVerdict(false, `✗ REJECTED — Reached reject state ${this.currentState}`);
      return;
    }

    const read = this.tape[this.headPos];
    const key = `${this.currentState},${read}`;
    const trans = this.machine.transitions[key];

    // Clear previous table highlight
    document.querySelectorAll('#tmSimTransTable .sim-trans-highlight').forEach(el => el.classList.remove('sim-trans-highlight'));

    if (!trans) {
      this.isFinished = true;
      this.showVerdict(false, `✗ HALTED — No transition δ(${this.currentState}, ${read})`);
      return;
    }

    // Highlight table row
    const rowEl = document.getElementById(`tmTransRow_${this.currentState}_${read}`);
    if (rowEl) {
      rowEl.querySelectorAll('td').forEach(td => td.classList.add('sim-trans-highlight'));
    }

    const prevState = this.currentState;

    // Write
    this.tape[this.headPos] = trans.write;

    // Move
    if (trans.move === 'R') {
      this.headPos++;
      // Extend tape if needed
      if (this.headPos >= this.tape.length) {
        this.tape.push('□');
      }
    } else {
      this.headPos--;
      if (this.headPos < 0) {
        this.tape.unshift('□');
        this.headPos = 0;
      }
    }

    this.currentState = trans.next;
    this.stepCount++;

    // Add trace
    this.addTraceRow(this.stepCount, prevState, read, trans.write, trans.move, trans.next);

    this.renderTape();
    this.updateInfoDisplay();

    // Scroll current cell into view
    const currentCell = document.getElementById(`tmSimTapeCell_${this.headPos}`);
    if (currentCell) {
      currentCell.scrollIntoView({ behavior: 'smooth', inline: 'center', block: 'nearest' });
    }

    // Auto-check for halt states
    if (this.currentState === this.machine.acceptState) {
      this.isFinished = true;
      this.showVerdict(true, `✓ ACCEPTED — Reached accept state. Tape: ${this.tape.filter(c => c !== '□').join('')}`);
    } else if (this.currentState === this.machine.rejectState) {
      this.isFinished = true;
      this.showVerdict(false, `✗ REJECTED — Reached reject state ${this.currentState}`);
    }
  }

  async runAll() {
    if (!this.machine || this.isRunning) return;
    this.isRunning = true;
    this.reset();
    this.trace.innerHTML = '';

    const speed = 1600 - parseInt(this.speedSlider.value);
    let safetyCounter = 0;

    while (!this.isFinished && safetyCounter < 500) {
      this.step();
      safetyCounter++;
      await new Promise(r => setTimeout(r, speed));
    }

    if (!this.isFinished) {
      this.isFinished = true;
      this.showVerdict(false, '✗ HALTED — Maximum steps exceeded (possible infinite loop)');
    }

    this.isRunning = false;
  }

  addTraceRow(stepNum, prevState, read, write, move, nextState) {
    const row = document.createElement('div');
    row.className = 'sim-trace-row';
    row.innerHTML = `
      <span class="sim-trace-step">${stepNum}</span>
      <span class="sim-trace-state">${prevState}</span>
      <span class="sim-trace-input">R:'${read}'</span>
      <span class="sim-trace-arrow">→</span>
      <span class="sim-trace-next">W:'${write}' ${move === 'R' ? '→' : '←'} ${nextState}</span>
      <span class="sim-trace-stack">Head:${this.headPos}</span>
    `;
    this.trace.appendChild(row);
    this.trace.scrollTop = this.trace.scrollHeight;
  }

  showVerdict(accepted, message) {
    this.verdict.textContent = message;
    this.verdict.className = `sim-verdict ${accepted ? 'accepted' : 'rejected'}`;
    this.verdict.style.display = 'block';
  }
}


// ========== SIMULATOR TAB CONTROLLER ==========

class SimulatorController {
  constructor() {
    this.dfaSim = null;
    this.pdaSim = null;
    this.tmSim = null;
    this.initialized = false;

    this.bindTabs();
  }

  bindTabs() {
    document.querySelectorAll('.sim-tab').forEach(tab => {
      tab.addEventListener('click', () => {
        document.querySelectorAll('.sim-tab').forEach(t => t.classList.remove('active'));
        tab.classList.add('active');

        const simType = tab.dataset.sim;
        document.querySelectorAll('.sim-panel').forEach(p => p.style.display = 'none');

        if (simType === 'dfa') {
          document.getElementById('simDfa').style.display = 'block';
          if (!this.dfaSim) this.dfaSim = new DFASimulator();
        } else if (simType === 'pda') {
          document.getElementById('simPda').style.display = 'block';
          if (!this.pdaSim) this.pdaSim = new PDASimulator();
        } else if (simType === 'tm') {
          document.getElementById('simTm').style.display = 'block';
          if (!this.tmSim) this.tmSim = new TMSimulator();
        }
      });
    });
  }

  init() {
    if (this.initialized) return;
    this.initialized = true;
    // Initialize DFA by default (it's the default tab)
    this.dfaSim = new DFASimulator();
  }
}


// ========== Initialize ==========
let simController;

document.addEventListener('DOMContentLoaded', () => {
  new CalculatorUI();
  simController = new SimulatorController();

  // Lazy-init simulators when simulator section becomes visible
  const simulatorNav = document.querySelector('[data-section="simulator"]');
  if (simulatorNav) {
    simulatorNav.addEventListener('click', () => {
      simController.init();
    });
  }
});
