import React, { useState, useEffect, useRef } from "react";

/** ---------- Logic: tokens, parser, AST, evaluation ---------- **/

type TokenType =
  | "VAR"
  | "LPAREN"
  | "RPAREN"
  | "NOT"
  | "AND"
  | "OR"
  | "IMP"
  | "BICOND";

type Token =
  | { type: "VAR"; name: string }
  | { type: Exclude<TokenType, "VAR"> };

// Accept both ASCII and Unicode connectives
function tokenize(input: string): Token[] {
  const tokens: Token[] = [];
  let i = 0;
  while (i < input.length) {
    const c = input[i];
    if (c === " " || c === "\t" || c === "\n") {
      i++;
      continue;
    }
    if (c >= "A" && c <= "Z") {
      tokens.push({ type: "VAR", name: c });
      i++;
    } else if (c === "(") {
      tokens.push({ type: "LPAREN" });
      i++;
    } else if (c === ")") {
      tokens.push({ type: "RPAREN" });
      i++;
    } else if (c === "~" || c === "¬") {
      tokens.push({ type: "NOT" });
      i++;
    } else if (c === "&" || c === "∧") {
      tokens.push({ type: "AND" });
      i++;
    } else if (c === "v" || c === "V" || c === "∨") {
      tokens.push({ type: "OR" });
      i++;
    } else if (input.slice(i, i + 2) === "->") {
      tokens.push({ type: "IMP" });
      i += 2;
    } else if (c === "→") {
      tokens.push({ type: "IMP" });
      i += 1;
    } else if (input.slice(i, i + 3) === "<->") {
      tokens.push({ type: "BICOND" });
      i += 3;
    } else if (c === "↔") {
      tokens.push({ type: "BICOND" });
      i += 1;
    } else {
      throw new Error(`Unexpected character: '${c}'`);
    }
  }
  return tokens;
}

type Connective = "NOT" | "AND" | "OR" | "IMP" | "BICOND";

type FormulaNode =
  | { id: string; type: "VAR"; name: string }
  | { id: string; type: "UNARY"; op: "NOT"; child: FormulaNode }
  | {
      id: string;
      type: "BINARY";
      op: Exclude<Connective, "NOT">;
      left: FormulaNode;
      right: FormulaNode;
    };
    
type BinaryNode = Extract<FormulaNode, { type: "BINARY" }>;


let idCounter = 0;
function genId(): string {
  return `n${idCounter++}`;
}

function parseFormula(input: string): FormulaNode {
  idCounter = 0;
  const tokens = tokenize(input);
  let pos = 0;

  function next(): Token | undefined {
    return tokens[pos];
  }

  function eat(expected?: TokenType): Token {
    const tok = tokens[pos];
    if (!tok) {
      throw new Error("Unexpected end of input");
    }
    if (expected && tok.type !== expected) {
      throw new Error(`Expected ${expected}, got ${tok.type}`);
    }
    pos++;
    return tok;
  }

  // Precedence: BICOND > IMP > OR > AND > NOT/atoms/parentheses

  function parsePrimary(): FormulaNode {
    const t = next();
    if (!t) throw new Error("Unexpected end of input in primary");
    if (t.type === "VAR") {
      eat("VAR");
      return { id: genId(), type: "VAR", name: t.name };
    } else if (t.type === "LPAREN") {
      eat("LPAREN");
      const inside = parseBicond();
      if (!next() || next()!.type !== "RPAREN") {
        throw new Error("Missing closing parenthesis");
      }
      eat("RPAREN");
      return inside;
    } else {
      throw new Error(`Unexpected token in primary: ${t.type}`);
    }
  }

  function parseUnary(): FormulaNode {
    const t = next();
    if (t && t.type === "NOT") {
      eat("NOT");
      const child = parseUnary();
      return { id: genId(), type: "UNARY", op: "NOT", child };
    }
    return parsePrimary();
  }

  function parseAnd(): FormulaNode {
    let node = parseUnary();
    while (next() && next()!.type === "AND") {
      eat("AND");
      const right = parseUnary();
      node = { id: genId(), type: "BINARY", op: "AND", left: node, right };
    }
    return node;
  }

  function parseOr(): FormulaNode {
    let node = parseAnd();
    while (next() && next()!.type === "OR") {
      eat("OR");
      const right = parseAnd();
      node = { id: genId(), type: "BINARY", op: "OR", left: node, right };
    }
    return node;
  }

  function parseImp(): FormulaNode {
    let node = parseOr();
    while (next() && next()!.type === "IMP") {
      eat("IMP");
      const right = parseOr();
      node = { id: genId(), type: "BINARY", op: "IMP", left: node, right };
    }
    return node;
  }

  function parseBicond(): FormulaNode {
    let node = parseImp();
    while (next() && next()!.type === "BICOND") {
      eat("BICOND");
      const right = parseImp();
      node = { id: genId(), type: "BINARY", op: "BICOND", left: node, right };
    }
    return node;
  }

  const root = parseBicond();
  if (pos !== tokens.length) {
    throw new Error("Extra tokens at end of input");
  }
  return root;
}

type Assignment = Record<string, boolean>;

function getAtoms(node: FormulaNode, acc = new Set<string>()): string[] {
  if (node.type === "VAR") {
    acc.add(node.name);
  } else if (node.type === "UNARY") {
    getAtoms(node.child, acc);
  } else {
    getAtoms(node.left, acc);
    getAtoms(node.right, acc);
  }
  return Array.from(acc).sort();
}

// Generate rows top→bottom as TT TF FT FF (canonical classroom order).
function allAssignments(atoms: string[]): Assignment[] {
  const n = atoms.length;
  const total = 1 << n; // 2^n
  const rows: Assignment[] = [];
  for (let mask = total - 1; mask >= 0; mask--) {
    const asg: Assignment = {};
    atoms.forEach((atom, i) => {
      const bitPos = n - 1 - i;
      asg[atom] = !!(mask & (1 << bitPos));
    });
    rows.push(asg);
  }
  return rows;
}

function evalNode(node: FormulaNode, asg: Assignment): boolean {
  switch (node.type) {
    case "VAR":
      return asg[node.name];
    case "UNARY":
      return !evalNode(node.child, asg);
    case "BINARY": {
      const l = evalNode(node.left, asg);
      const r = evalNode(node.right, asg);
      switch (node.op) {
        case "AND":
          return l && r;
        case "OR":
          return l || r;
        case "IMP":
          return !l || r;
        case "BICOND":
          return l === r;
        default:
          throw new Error(`Unknown binary op: ${node.op}`);
      }
    }
    default:
      throw new Error("Unknown node type");
  }
}

// Canonical ASCII pretty-printer for grammaticality checking
// Canonical ASCII pretty-printer for grammaticality checking
function formulaToAscii(node: FormulaNode): string {
  if (node.type === "VAR") {
    return node.name;
  }

  if (node.type === "UNARY") {
    return `~${formulaToAscii(node.child)}`;
  }

  // From here on, it's a binary node; cast to make TS happy
  const b = node as BinaryNode;
  let opStr: string;
  switch (b.op) {
    case "AND":
      opStr = "&";
      break;
    case "OR":
      opStr = "v";
      break;
    case "IMP":
      opStr = "->";
      break;
    case "BICOND":
      opStr = "<->";
      break;
    default:
      opStr = "?";
  }
  return `(${formulaToAscii(b.left)} ${opStr} ${formulaToAscii(b.right)})`;
}

// Unicode pretty-printer for display
// Unicode pretty-printer for display
function formulaToUnicode(node: FormulaNode): string {
  if (node.type === "VAR") {
    return node.name;
  }

  if (node.type === "UNARY") {
    return `¬${formulaToUnicode(node.child)}`;
  }

  const b = node as BinaryNode;
  let opStr: string;
  switch (b.op) {
    case "AND":
      opStr = "∧";
      break;
    case "OR":
      opStr = "∨";
      break;
    case "IMP":
      opStr = "→";
      break;
    case "BICOND":
      opStr = "↔";
      break;
    default:
      opStr = "?";
  }

  return `(${formulaToUnicode(b.left)} ${opStr} ${formulaToUnicode(
    b.right
  )})`;
}

/**
 * Collect non-atomic subformulas in evaluation order (children before parent).
 */
function collectSubformulas(
  node: FormulaNode,
  acc: FormulaNode[] = []
): FormulaNode[] {
  if (node.type === "VAR") return acc;
  if (node.type === "UNARY") {
    collectSubformulas(node.child, acc);
    acc.push(node);
  } else {
    collectSubformulas(node.left, acc);
    collectSubformulas(node.right, acc);
    acc.push(node);
  }
  return acc;
}

/** ---------- Random formula generator ---------- **/

const ATOM_POOL = ["P", "Q", "R", "S"];

function randInt(min: number, max: number): number {
  // inclusive min, inclusive max
  return Math.floor(Math.random() * (max - min + 1)) + min;
}

function randomAtom(atoms: string[]): string {
  return atoms[randInt(0, atoms.length - 1)];
}

function randomBinaryOp(): Exclude<Connective, "NOT"> {
  const ops: Exclude<Connective, "NOT">[] = ["AND", "OR", "IMP", "BICOND"];
  return ops[randInt(0, ops.length - 1)];
}

function generateRandomFormulaAST(
  maxDepth: number,
  atoms: string[]
): FormulaNode {
  if (maxDepth <= 0) {
    return { id: genId(), type: "VAR", name: randomAtom(atoms) };
  }

  const chooseUnary = Math.random() < 0.3; // ~30% chance for negation

  if (chooseUnary) {
    const child = generateRandomFormulaAST(maxDepth - 1, atoms);
    return { id: genId(), type: "UNARY", op: "NOT", child };
  } else {
    const left = generateRandomFormulaAST(maxDepth - 1, atoms);
    const right = generateRandomFormulaAST(maxDepth - 1, atoms);
    const op = randomBinaryOp();
    return { id: genId(), type: "BINARY", op, left, right };
  }
}

function generateRandomFormulaString(): string {
  const numAtoms = randInt(2, 3); // 2–3 different atoms
  const atoms = ATOM_POOL.slice(0, numAtoms);
  const depth = randInt(1, 3); // structural complexity
  const ast = generateRandomFormulaAST(depth, atoms);
  // For UI, use Unicode
  return formulaToUnicode(ast);
}

/** ---------- React component + quiz / logging types ---------- **/

type CellGuess = "T" | "F" | null;
type CellFeedback = "correct" | "incorrect" | "missing" | null;
type ColumnStatus = "pending" | "correct";

type QuizQuestionStatus = "pending" | "in-progress" | "completed";

interface QuizQuestion {
  id: number;
  formula: string; // stored in Unicode form
  status: QuizQuestionStatus;
}

interface LogEntry {
  id: number;
  ts: string;
  quizIndex: number | null; // 0-based; null = practice
  columnIndex: number | null; // 0-based column index
  message: string;
}

let logIdCounter = 0;

const DEFAULT_FORMULA = "(P ∧ Q) → ¬R";

const App: React.FC = () => {
  const [email, setEmail] = useState<string>("");
  const [formulaStr, setFormulaStr] = useState<string>(DEFAULT_FORMULA);
  const [root, setRoot] = useState<FormulaNode | null>(null);
  const [parseError, setParseError] = useState<string | null>(null);
  const [grammarWarning, setGrammarWarning] = useState<string | null>(null);

  const inputRef = useRef<HTMLInputElement | null>(null);

  // truth-table state
  const [guesses, setGuesses] = useState<CellGuess[][]>([]);
  const [feedback, setFeedback] = useState<CellFeedback[][]>([]);
  const [columnStatus, setColumnStatus] = useState<ColumnStatus[]>([]);
  const [activeColIndex, setActiveColIndex] = useState<number>(0);
  const [summary, setSummary] = useState<string>("");

  // quiz state (linear, no skipping)
  const [quizQuestions, setQuizQuestions] = useState<QuizQuestion[]>([]);
  const [inQuiz, setInQuiz] = useState<boolean>(false);
  const [currentQuizIndex, setCurrentQuizIndex] = useState<number | null>(null);

  // logging + certificate
  const [logEntries, setLogEntries] = useState<LogEntry[]>([]);
  const [showCertificate, setShowCertificate] = useState<boolean>(false);
  const [certificateTimestamp, setCertificateTimestamp] = useState<string | null>(
    null
  );


  function openLogWindow() {
    if (!logEntries.length) {
      alert("No log entries recorded yet.");
      return;
    }

    const safeEmail = email || "email@domain.edu";

    const logLines = logEntries.map((entry) => {
      const context =
        entry.quizIndex !== null
          ? `Quiz item ${entry.quizIndex + 1}${
              entry.columnIndex !== null
                ? ` · Column ${entry.columnIndex + 1}`
                : ""
            }`
          : "Practice / system";

      return `[${entry.ts}] ${context} :: ${entry.message}`;
    });

    const escapedLog = logLines
      .join("\n\n")
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;");

    const html = `<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <title>Truth Table Quiz Log</title>
</head>
<body style="margin:12px; font-family: monospace; background:#ffffff;">
  <div style="font-size:12px; font-weight:bold; margin-bottom:6px;">
    Truth Table Quiz Log — ${safeEmail}
  </div>
  <div style="font-size:10px; white-space:pre-wrap; line-height:1.3;">
${escapedLog}
  </div>
</body>
</html>`;

    const blob = new Blob([html], { type: "text/html" });
    const url = URL.createObjectURL(blob);

    const win = window.open(
      url,
      "_blank",
      "width=900,height=700,noopener,noreferrer"
    );
    if (!win) {
      // Popup blocked
      alert(
        "Your browser blocked the log window. Please allow pop-ups for this site."
      );
      return;
    }

    // Optionally revoke after a while
    setTimeout(() => URL.revokeObjectURL(url), 60_000);
  }



  function addLogEntry(
    message: string,
    quizIndex: number | null,
    columnIndex: number | null
  ) {
    const ts = new Date().toLocaleString();
    setLogEntries((prev) => [
      ...prev,
      {
        id: ++logIdCounter,
        ts,
        quizIndex,
        columnIndex,
        message,
      },
    ]);
  }

  // Normalize for grammaticality check
  function normalizeForGrammar(s: string): string {
    return s
      .replace(/\s+/g, "")
      .replace(/¬/g, "~")
      .replace(/[∧&]/g, "&")
      .replace(/[∨vV]/g, "v")
      .replace(/→/g, "->")
      .replace(/↔/g, "<->");
  }

  function loadFormula(str: string) {
    setGrammarWarning(null);
    try {
      const ast = parseFormula(str);
      setRoot(ast);
      setParseError(null);

      // canonical ASCII version
      const canonicalAscii = formulaToAscii(ast);

      const inputNorm = normalizeForGrammar(str);
      const canonicalNorm = normalizeForGrammar(canonicalAscii);

      if (inputNorm !== canonicalNorm) {
        setGrammarWarning("THIS IS UNGRAMMATICAL. I AM FIXING IT.");
      } else {
        setGrammarWarning(null);
      }

      // Always show canonical Unicode in the input after parsing
      setFormulaStr(formulaToUnicode(ast));
    } catch (e: any) {
      setRoot(null);
      setParseError(e.message || "Parse error");
      setGuesses([]);
      setFeedback([]);
      setColumnStatus([]);
      setActiveColIndex(0);
      setSummary("");
    }
  }

  function handleParse() {
    setInQuiz(false);
    setCurrentQuizIndex(null);
    setQuizQuestions([]);
    loadFormula(formulaStr);
    setShowCertificate(false);
  }

  // Parse default formula on mount
  useEffect(() => {
    loadFormula(DEFAULT_FORMULA);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  // Derived values
  const atoms: string[] = root ? getAtoms(root) : [];
  const assignments: Assignment[] = root ? allAssignments(atoms) : [];
  const subformulas: FormulaNode[] = root ? collectSubformulas(root) : [];
  const hasSubformulas = subformulas.length > 0;

  // Safe active node to avoid out-of-bounds crashes
  const activeNode: FormulaNode | null =
    hasSubformulas &&
    activeColIndex >= 0 &&
    activeColIndex < subformulas.length
      ? subformulas[activeColIndex]
      : null;

  // Re-init student data when root/subformulas/rows change
  useEffect(() => {
    if (!root || !hasSubformulas) {
      setGuesses([]);
      setFeedback([]);
      setColumnStatus([]);
      setActiveColIndex(0);
      setSummary("");
      return;
    }
    const numCols = subformulas.length;
    const numRows = assignments.length;
    setGuesses(
      Array.from({ length: numCols }, () =>
        Array<CellGuess>(numRows).fill(null)
      )
    );
    setFeedback(
      Array.from({ length: numCols }, () =>
        Array<CellFeedback>(numRows).fill(null)
      )
    );
    setColumnStatus(Array<ColumnStatus>(numCols).fill("pending"));
    setActiveColIndex(0);
    setSummary("");
  }, [root, hasSubformulas, subformulas.length, assignments.length]);

  function loadRandomPracticeFormula() {
    const f = generateRandomFormulaString();
    setInQuiz(false);
    setQuizQuestions([]);
    setCurrentQuizIndex(null);
    setShowCertificate(false);
    loadFormula(f);
    addLogEntry("Loaded random practice formula.", null, null);
  }

  function startQuiz() {
    if (!email.trim()) {
      alert("Please enter your email before starting the quiz.");
      return;
    }
    const numQuestions = 5;
    const qs: QuizQuestion[] = [];
    for (let i = 0; i < numQuestions; i++) {
      const f = generateRandomFormulaString();
      qs.push({
        id: i + 1,
        formula: f,
        status: i === 0 ? "in-progress" : "pending",
      });
    }
    setQuizQuestions(qs);
    setInQuiz(true);
    setCurrentQuizIndex(0);
    setShowCertificate(false);
    loadFormula(qs[0].formula);
    addLogEntry("Started 5-question quiz.", 0, null);
  }

  function toggleGuess(colIdx: number, rowIdx: number) {
    if (colIdx !== activeColIndex) return;
    if (!root) return;
    if (columnStatus[colIdx] === "correct") return;

    setGuesses((prev) => {
      const next = prev.map((col) => [...col]);
      const current = next[colIdx][rowIdx];
      const newVal: CellGuess =
        current === null ? "T" : current === "T" ? "F" : null;
      next[colIdx][rowIdx] = newVal;
      return next;
    });

    setFeedback((prev) => {
      const next = prev.map((col) => [...col]);
      next[colIdx][rowIdx] = null;
      return next;
    });

    setSummary("");
  }

  function handleCheckActiveColumn() {
    if (!root || !hasSubformulas) return;
    const colIdx = activeColIndex;
    if (colIdx < 0 || colIdx >= subformulas.length) return; // safety

    const node = subformulas[colIdx];
    const correctValues = assignments.map((asg) => evalNode(node, asg));

    let correctCount = 0;
    let incorrectCount = 0;
    let missingCount = 0;

    const newFeedbackCol: CellFeedback[] = guesses[colIdx].map((g, rowIdx) => {
      if (g === null) {
        missingCount++;
        return "missing";
      }
      const correct = correctValues[rowIdx] ? "T" : "F";
      if (g === correct) {
        correctCount++;
        return "correct";
      } else {
        incorrectCount++;
        return "incorrect";
      }
    });

    setFeedback((prev) => {
      const next = prev.map((col) => [...col]);
      next[colIdx] = newFeedbackCol;
      return next;
    });

    const total = guesses[colIdx].length;
    if (total === 0) {
      setSummary("");
      return;
    }

    let newSummary = `Column ${colIdx + 1} of ${
      subformulas.length
    } (${formulaToUnicode(
      node
    )}): Correct: ${correctCount}, Incorrect: ${incorrectCount}, Missing: ${missingCount}.`;

    const quizIndexForLog =
      inQuiz && currentQuizIndex !== null ? currentQuizIndex : null;

    if (incorrectCount === 0 && missingCount === 0) {
      setColumnStatus((prev) => {
        const next = [...prev];
        next[colIdx] = "correct";
        return next;
      });

      newSummary += " ✅ All rows correct.";

      if (colIdx < subformulas.length - 1) {
        setActiveColIndex(colIdx + 1);
        newSummary += " Moving to the next subformula column.";
      } else {
        newSummary += " You have completed all subformulas.";

        const finalTruths = correctValues;
        const allTrue = finalTruths.every((v) => v === true);
        const allFalse = finalTruths.every((v) => v === false);
        if (allTrue) {
          newSummary += " This formula is a tautology.";
        } else if (allFalse) {
          newSummary += " This formula is a contradiction.";
        } else {
          newSummary += " This formula is contingent.";
        }

        // Linear quiz integration when last column is correct
        if (inQuiz && currentQuizIndex !== null) {
          setQuizQuestions((prev) =>
            prev.map((q, idx) =>
              idx === currentQuizIndex
                ? { ...q, status: "completed" }
                : q
            )
          );

          if (currentQuizIndex < quizQuestions.length - 1) {
            const nextIndex = currentQuizIndex + 1;
            setCurrentQuizIndex(nextIndex);
            setQuizQuestions((prev) =>
              prev.map((q, idx) =>
                idx === nextIndex
                  ? { ...q, status: "in-progress" }
                  : q
              )
            );
            const nextFormula = quizQuestions[nextIndex].formula;
            loadFormula(nextFormula);
            newSummary += ` Moving to quiz item ${nextIndex + 1}.`;
          } else {
            newSummary += " You have completed all quiz items.";
            setInQuiz(false);
            setCurrentQuizIndex(null);
            addLogEntry("Finished quiz.", currentQuizIndex, null);
          }
        }
      }
      setSummary(newSummary);
    } else {
      newSummary += " Try fixing the highlighted rows.";
      setSummary(newSummary);
    }

    addLogEntry(newSummary, quizIndexForLog, colIdx);
  }

  function handleCertify() {
    if (!email.trim()) {
      alert("Please enter your email before generating a certificate.");
      return;
    }
    if (!quizQuestions.length) {
      alert("You need to start a quiz before certifying your result.");
      return;
    }
    const ts = new Date().toLocaleString();
    setCertificateTimestamp(ts);
    setShowCertificate(true);
    addLogEntry("Generated certificate view.", null, null);
  }

  // Compute which columns are inputs to the active subformula
  const relevantAtomIndices = new Set<number>();
  const relevantSubformulaIndices = new Set<number>();
  let dependencyLabel = "";

  if (root && hasSubformulas && activeNode) {
    const node = activeNode;

    const atomIndexByName: Record<string, number> = {};
    atoms.forEach((name, idx) => {
      atomIndexByName[name] = idx;
    });

    const subformulaIndexById: Record<string, number> = {};
    subformulas.forEach((sf, idx) => {
      subformulaIndexById[sf.id] = idx;
    });

    const addChild = (child: FormulaNode) => {
      if (child.type === "VAR") {
        const idx = atomIndexByName[child.name];
        if (idx !== undefined) relevantAtomIndices.add(idx);
      } else {
        const idx = subformulaIndexById[child.id];
        if (idx !== undefined) relevantSubformulaIndices.add(idx);
      }
    };

    if (node.type === "UNARY") {
      addChild(node.child);
    } else if (node.type === "BINARY") {
      addChild(node.left);
      addChild(node.right);
    }

    const atomLabels = Array.from(relevantAtomIndices)
      .sort((a, b) => a - b)
      .map((idx) => atoms[idx]);

    const subformulaLabels = Array.from(relevantSubformulaIndices)
      .sort((a, b) => a - b)
      .map((idx) => formulaToUnicode(subformulas[idx]));

    if (atomLabels.length || subformulaLabels.length) {
      const parts: string[] = [];
      if (atomLabels.length) parts.push(atomLabels.join(", "));
      if (subformulaLabels.length) parts.push(subformulaLabels.join(", "));
      dependencyLabel = parts.join(" and ");
    }
  }

  function insertSymbol(sym: string) {
    const input = inputRef.current;
    if (!input) return;
    const start = input.selectionStart ?? formulaStr.length;
    const end = input.selectionEnd ?? formulaStr.length;
    const before = formulaStr.slice(0, start);
    const after = formulaStr.slice(end);
    const newVal = before + sym + after;
    setFormulaStr(newVal);
    window.requestAnimationFrame(() => {
      input.focus();
      const pos = start + sym.length;
      input.setSelectionRange(pos, pos);
    });
  }

  const primaryButtonStyle: React.CSSProperties = {
    padding: "0.4rem 0.9rem",
    borderRadius: "999px",
    border: "none",
    background:
      "linear-gradient(135deg, rgba(59,130,246,1), rgba(37,99,235,1))",
    color: "white",
    fontSize: "0.9rem",
    fontWeight: 600,
    cursor: "pointer",
    boxShadow: "0 6px 14px rgba(37,99,235,0.4)",
  };

  const secondaryButtonStyle: React.CSSProperties = {
    padding: "0.4rem 0.9rem",
    borderRadius: "999px",
    border: "1px solid rgba(148,163,184,0.6)",
    backgroundColor: "white",
    color: "#1f2933",
    fontSize: "0.9rem",
    fontWeight: 500,
    cursor: "pointer",
  };

  const disabledButtonStyle: React.CSSProperties = {
    ...secondaryButtonStyle,
    cursor: "not-allowed",
    opacity: 0.6,
  };

  return (
    <div
      style={{
        minHeight: "100vh",
        background:
          "radial-gradient(circle at top, #e0f2fe 0, #f8fafc 40%, #eef2ff 100%)",
        padding: "2rem 0",
      }}
    >
      <div
        style={{
          maxWidth: 960,
          margin: "0 auto",
          padding: "1.75rem 2rem",
          borderRadius: 18,
          backgroundColor: "white",
          boxShadow: "0 18px 45px rgba(15,23,42,0.18)",
          fontFamily:
            '-apple-system, BlinkMacSystemFont, "SF Pro Text", system-ui, sans-serif',
        }}
      >
        <header
          style={{
            display: "flex",
            justifyContent: "space-between",
            alignItems: "flex-end",
            gap: "1rem",
            marginBottom: "1.25rem",
          }}
        >
          <div>
            <h1
              style={{
                fontSize: "1.35rem",
                fontWeight: 700,
                margin: 0,
                letterSpacing: "0.02em",
                color: "#0f172a",
              }}
            >
              Truth Table Trainer
            </h1>
            <div
              style={{
                fontSize: "0.8rem",
                color: "#64748b",
                marginTop: "0.15rem",
              }}
            >
              Build truth tables one subformula at a time.
            </div>
          </div>
          <div style={{ textAlign: "right", fontSize: "0.8rem" }}>
            <div style={{ color: "#94a3b8" }}>TT · TF · FT · FF ordering</div>
          </div>
        </header>

        {/* Email entry */}
        <section
          style={{
            marginBottom: "0.9rem",
            display: "flex",
            flexWrap: "wrap",
            gap: "0.75rem",
            alignItems: "center",
          }}
        >
          <div style={{ flex: "1 1 220px" }}>
            <label
              style={{
                display: "block",
                marginBottom: "0.2rem",
                fontSize: "0.8rem",
                fontWeight: 600,
                color: "#0f172a",
              }}
            >
              Email (for watermarking your certificate)
            </label>
            <input
              type="email"
              value={email}
              onChange={(e) => setEmail(e.target.value)}
              placeholder="you@university.edu"
              style={{
                width: "100%",
                padding: "0.45rem 0.7rem",
                borderRadius: 999,
                border: "1px solid rgba(148,163,184,0.9)",
                fontSize: "0.85rem",
              }}
            />
          </div>
          <div
            style={{
              fontSize: "0.75rem",
              color: "#6b7280",
              maxWidth: 280,
            }}
          >
            This email will be printed and watermarked on your quiz receipt so
            screenshots are tied to your identity.
          </div>
        </section>

        <section style={{ marginBottom: "1rem" }}>
          <label
            style={{
              display: "block",
              marginBottom: "0.25rem",
              fontSize: "0.85rem",
              fontWeight: 600,
              color: "#0f172a",
            }}
          >
            Formula
          </label>
          <input
            ref={inputRef}
            style={{
              width: "100%",
              padding: "0.55rem 0.7rem",
              fontFamily: "monospace",
              fontSize: "0.95rem",
              borderRadius: 10,
              border: "1px solid rgba(148,163,184,0.9)",
              outline: "none",
              boxShadow: "0 1px 2px rgba(15,23,42,0.05)",
            }}
            value={formulaStr}
            onChange={(e) => setFormulaStr(e.target.value)}
            placeholder="e.g. (P ∧ Q) → ¬R"
          />
          <div
            style={{
              marginTop: "0.45rem",
              display: "flex",
              flexWrap: "wrap",
              alignItems: "center",
              gap: "0.4rem",
              fontSize: "0.8rem",
            }}
          >
            <span style={{ color: "#6b7280" }}>Insert connective:</span>
            {[
              { label: "¬", sym: "¬" },
              { label: "∧", sym: "∧" },
              { label: "∨", sym: "∨" },
              { label: "→", sym: "→" },
              { label: "↔", sym: "↔" },
            ].map((btn) => (
              <button
                key={btn.sym}
                type="button"
                onClick={() => insertSymbol(btn.sym)}
                style={{
                  padding: "0.15rem 0.45rem",
                  borderRadius: 999,
                  border: "1px solid rgba(148,163,184,0.7)",
                  backgroundColor: "#f9fafb",
                  cursor: "pointer",
                  fontSize: "0.9rem",
                  fontFamily: "system-ui, sans-serif",
                }}
              >
                {btn.label}
              </button>
            ))}
            <span style={{ color: "#9ca3af", marginLeft: "0.5rem" }}>
              You can also type ~, &amp;, v, -&gt;, &lt;-&gt;.
            </span>
          </div>
          <div
            style={{
              marginTop: "0.6rem",
              display: "flex",
              flexWrap: "wrap",
              gap: "0.5rem",
              alignItems: "center",
            }}
          >
            <button type="button" style={primaryButtonStyle} onClick={handleParse}>
              Load formula
            </button>
            <button
              type="button"
              style={secondaryButtonStyle}
              onClick={loadRandomPracticeFormula}
            >
              Random practice formula
            </button>
            <button
              type="button"
              style={email.trim() ? secondaryButtonStyle : disabledButtonStyle}
              onClick={startQuiz}
              disabled={!email.trim()}
            >
              Start 5-question quiz
            </button>
            <button
              type="button"
              style={
                quizQuestions.length && email.trim()
                  ? secondaryButtonStyle
                  : disabledButtonStyle
              }
              onClick={handleCertify}
              disabled={!quizQuestions.length || !email.trim()}
            >
              Certify your result
            </button>
          </div>

          {parseError && (
            <div
              style={{
                marginTop: "0.6rem",
                padding: "0.55rem 0.7rem",
                borderRadius: 10,
                backgroundColor: "#fef2f2",
                color: "#b91c1c",
                fontSize: "0.85rem",
                border: "1px solid #fecaca",
              }}
            >
              <strong>Parse error:</strong> {parseError}
            </div>
          )}

          {grammarWarning && !parseError && (
            <div
              style={{
                marginTop: "0.6rem",
                padding: "0.6rem 0.75rem",
                borderRadius: 10,
                backgroundColor: "#fef2f2",
                color: "#7f1d1d",
                fontSize: "0.9rem",
                border: "1px solid #fecaca",
                fontWeight: 700,
                textTransform: "uppercase",
              }}
            >
              THIS IS UNGRAMMATICAL. I AM FIXING IT.
            </div>
          )}
        </section>

        {root && (
          <>
            <section style={{ marginBottom: "0.9rem" }}>
              <div
                style={{
                  fontSize: "0.85rem",
                  marginBottom: "0.15rem",
                  color: "#0f172a",
                }}
              >
                <strong>Parsed formula:</strong>{" "}
                <code>{formulaToUnicode(root)}</code>
              </div>
              <div style={{ fontSize: "0.8rem", color: "#64748b" }}>
                <strong>Atoms:</strong>{" "}
                {atoms.length > 0 ? atoms.join(", ") : "(none)"}
              </div>
            </section>

            {!hasSubformulas && (
              <p style={{ fontSize: "0.9rem", color: "#475569" }}>
                This formula is just a single atomic proposition. There are no
                non-atomic subformulas to compute.
              </p>
            )}

            {hasSubformulas && (
              <>
                <section style={{ marginBottom: "0.6rem" }}>
                  <p
                    style={{
                      marginBottom: "0.2rem",
                      fontSize: "0.85rem",
                      color: "#475569",
                    }}
                  >
                    Work left-to-right through the subformula columns. You can
                    only edit the <strong>active column</strong>, highlighted in
                    blue in the header.
                  </p>
                  <p
                    style={{
                      fontSize: "0.8rem",
                      marginTop: 0,
                      color: "#6b7280",
                    }}
                  >
                    Active column:{" "}
                    <strong>
                      {activeColIndex + 1} / {subformulas.length}
                    </strong>{" "}
                    (
                    <code>
                      {activeNode ? formulaToUnicode(activeNode) : "—"}
                    </code>
                    )
                  </p>
                  {dependencyLabel && (
                    <p
                      style={{
                        fontSize: "0.8rem",
                        marginTop: 0,
                        color: "#6b7280",
                      }}
                    >
                      To compute this column, use:{" "}
                      <code>{dependencyLabel}</code>
                    </p>
                  )}
                </section>

                <div style={{ overflowX: "auto" }}>
                  <table
                    style={{
                      borderCollapse: "collapse",
                      minWidth: "100%",
                      marginBottom: "0.6rem",
                      fontSize: "0.85rem",
                    }}
                  >
                    <thead>
                      <tr>
                        {atoms.map((a, idx) => (
                          <th
                            key={a}
                            style={{
                              border: "1px solid #e5e7eb",
                              padding: "0.25rem 0.5rem",
                              backgroundColor: relevantAtomIndices.has(idx)
                                ? "#fef3c7"
                                : "#f9fafb",
                              fontWeight: 600,
                              color: "#0f172a",
                            }}
                          >
                            {a}
                          </th>
                        ))}
                        {subformulas.map((sf, idx) => {
                          let bg = "#f9fafb";
                          if (idx === activeColIndex) {
                            bg = "#dbeafe";
                          } else if (columnStatus[idx] === "correct") {
                            bg = "#dcfce7";
                          } else if (relevantSubformulaIndices.has(idx)) {
                            bg = "#ffe4f3";
                          }
                          return (
                            <th
                              key={sf.id}
                              style={{
                                border: "1px solid #e5e7eb",
                                padding: "0.25rem 0.5rem",
                                backgroundColor: bg,
                                fontWeight: 600,
                                color: "#0f172a",
                              }}
                            >
                              {formulaToUnicode(sf)}
                            </th>
                          );
                        })}
                      </tr>
                    </thead>
                    <tbody>
                      {assignments.map((asg, rowIdx) => (
                        <tr key={rowIdx}>
                          {atoms.map((a, atomIdx) => (
                            <td
                              key={a}
                              style={{
                                border: "1px solid #e5e7eb",
                                padding: "0.2rem 0.45rem",
                                textAlign: "center",
                                backgroundColor: relevantAtomIndices.has(
                                  atomIdx
                                )
                                  ? "#fffbeb"
                                  : "white",
                              }}
                            >
                              {asg[a] ? "T" : "F"}
                            </td>
                          ))}
                          {subformulas.map((sf, colIdx) => {
                            const status = columnStatus[colIdx];
                            const cellFeedback =
                              feedback[colIdx]?.[rowIdx] ?? null;
                            const isActive = colIdx === activeColIndex;
                            const interactive =
                              isActive && status !== "correct";

                            let bg = "white";
                            if (cellFeedback === "correct") bg = "#dcfce7";
                            else if (cellFeedback === "incorrect")
                              bg = "#fee2e2";
                            else if (cellFeedback === "missing")
                              bg = "#fef3c7";
                            else if (!interactive && status === "pending") {
                              bg = relevantSubformulaIndices.has(colIdx)
                                ? "#fff0fa"
                                : "#f3f4f6";
                            }

                            return (
                              <td
                                key={sf.id + "-" + rowIdx}
                                style={{
                                  border: "1px solid #e5e7eb",
                                  padding: "0.2rem 0.45rem",
                                  textAlign: "center",
                                  cursor: interactive ? "pointer" : "default",
                                  backgroundColor: bg,
                                  userSelect: "none",
                                }}
                                onClick={() =>
                                  interactive && toggleGuess(colIdx, rowIdx)
                                }
                                title={
                                  interactive
                                    ? "Click to cycle between T, F, and blank"
                                    : ""
                                }
                              >
                                {guesses[colIdx]?.[rowIdx] ?? "·"}
                              </td>
                            );
                          })}
                        </tr>
                      ))}
                    </tbody>
                  </table>
                </div>

                <button
                  type="button"
                  style={primaryButtonStyle}
                  onClick={handleCheckActiveColumn}
                  disabled={!root || !hasSubformulas}
                >
                  Check active column
                </button>

                {summary && (
                  <div
                    style={{
                      marginTop: "0.6rem",
                      fontFamily: "monospace",
                      whiteSpace: "pre-wrap",
                      fontSize: "0.85rem",
                      backgroundColor: "#f9fafb",
                      padding: "0.45rem 0.6rem",
                      borderRadius: 10,
                      border: "1px solid #e5e7eb",
                      color: "#0f172a",
                    }}
                  >
                    {summary}
                  </div>
                )}
              </>
            )}
          </>
        )}

        {!root && !parseError && (
          <p style={{ fontSize: "0.9rem", color: "#475569", marginTop: "0.75rem" }}>
            Enter a formula above and click “Load formula” to begin.
          </p>
        )}

        {quizQuestions.length > 0 && (
          <section style={{ marginTop: "1.4rem" }}>
            <h2
              style={{
                fontSize: "0.95rem",
                fontWeight: 600,
                marginBottom: "0.3rem",
                color: "#0f172a",
              }}
            >
              Quiz progress
            </h2>
            <p style={{ fontSize: "0.8rem", color: "#6b7280" }}>
              Items are completed in order. You can’t skip ahead.
            </p>
            <table
              style={{
                borderCollapse: "collapse",
                minWidth: "100%",
                marginTop: "0.25rem",
                fontSize: "0.8rem",
              }}
            >
              <thead>
                <tr>
                  <th
                    style={{
                      border: "1px solid #e5e7eb",
                      padding: "0.25rem 0.5rem",
                    }}
                  >
                    #
                  </th>
                  <th
                    style={{
                      border: "1px solid #e5e7eb",
                      padding: "0.25rem 0.5rem",
                    }}
                  >
                    Formula
                  </th>
                  <th
                    style={{
                      border: "1px solid #e5e7eb",
                      padding: "0.25rem 0.5rem",
                    }}
                  >
                    Status
                  </th>
                </tr>
              </thead>
              <tbody>
                {quizQuestions.map((q, idx) => (
                  <tr
                    key={q.id}
                    style={{
                      backgroundColor:
                        currentQuizIndex === idx ? "#eff6ff" : "white",
                    }}
                  >
                    <td
                      style={{
                        border: "1px solid #e5e7eb",
                        padding: "0.25rem 0.5rem",
                        textAlign: "center",
                      }}
                    >
                      {idx + 1}
                    </td>
                    <td
                      style={{
                        border: "1px solid #e5e7eb",
                        padding: "0.25rem 0.5rem",
                        fontFamily: "monospace",
                      }}
                    >
                      {q.formula}
                    </td>
                    <td
                      style={{
                        border: "1px solid #e5e7eb",
                        padding: "0.25rem 0.5rem",
                        textTransform: "capitalize",
                      }}
                    >
                      {q.status}
                    </td>
                  </tr>
                ))}
              </tbody>
            </table>
          </section>
        )}

        {/* Certificate / log view */}
       {showCertificate && (
         <section
           style={{
             marginTop: "1.8rem",
             position: "relative",
             borderRadius: 16,
             border: "1px solid #e5e7eb",
             overflow: "hidden",
             backgroundColor: "white",
           }}
         >
           {/* Watermark layer */}
           <div
             style={{
               position: "absolute",
               inset: 0,
               pointerEvents: "none",
               opacity: 0.12,
               display: "flex",
               flexDirection: "column",
               justifyContent: "space-around",
               alignItems: "center",
               fontSize: "2.3rem",
               fontWeight: 700,
               color: "#0f172a",
               transform: "rotate(-20deg)",
               zIndex: 1,
             }}
           >
             {Array.from({ length: 6 }).map((_, idx) => (
               <div key={idx} style={{ whiteSpace: "nowrap" }}>
                 {email || "email@domain.edu"}
               </div>
             ))}
           </div>

           {/* Foreground content */}
           <div
             style={{
               position: "relative",
               zIndex: 2,
               padding: "1.1rem 1.2rem",
             }}
           >
             <h2
               style={{
                 fontSize: "1rem",
                 fontWeight: 700,
                 margin: 0,
                 marginBottom: "0.3rem",
                 color: "#0f172a",
               }}
             >
               Truth Table Quiz Receipt
             </h2>
             <div
               style={{
                 fontSize: "0.8rem",
                 color: "#4b5563",
                 marginBottom: "0.5rem",
               }}
             >
               <div>
                 <strong>Email:</strong> {email || "(not provided)"}
               </div>
               <div>
                 <strong>Generated:</strong>{" "}
                 {certificateTimestamp || "(unknown time)"}
               </div>
             </div>

             <div
               style={{
                 fontSize: "0.8rem",
                 color: "#4b5563",
                 marginBottom: "0.6rem",
               }}
             >
               <strong>Quiz overview</strong>
             </div>
             <table
               style={{
                 borderCollapse: "collapse",
                 width: "100%",
                 fontSize: "0.78rem",
                 marginBottom: "0.9rem",
                 backgroundColor: "rgba(255,255,255,0.9)",
               }}
             >
               <thead>
                 <tr>
                   <th
                     style={{
                       border: "1px solid #e5e7eb",
                       padding: "0.25rem 0.4rem",
                     }}
                   >
                     #
                   </th>
                   <th
                     style={{
                       border: "1px solid #e5e7eb",
                       padding: "0.25rem 0.4rem",
                     }}
                   >
                     Formula
                   </th>
                   <th
                     style={{
                       border: "1px solid #e5e7eb",
                       padding: "0.25rem 0.4rem",
                     }}
                   >
                     Status
                   </th>
                 </tr>
               </thead>
               <tbody>
                 {quizQuestions.map((q, idx) => (
                   <tr key={q.id}>
                     <td
                       style={{
                         border: "1px solid #e5e7eb",
                         padding: "0.25rem 0.4rem",
                         textAlign: "center",
                       }}
                     >
                       {idx + 1}
                     </td>
                     <td
                       style={{
                         border: "1px solid #e5e7eb",
                         padding: "0.25rem 0.4rem",
                         fontFamily: "monospace",
                       }}
                     >
                       {q.formula}
                     </td>
                     <td
                       style={{
                         border: "1px solid #e5e7eb",
                         padding: "0.25rem 0.4rem",
                         textTransform: "capitalize",
                       }}
                     >
                       {q.status}
                     </td>
                   </tr>
                 ))}
               </tbody>
             </table>

             <div
               style={{
                 display: "flex",
                 alignItems: "center",
                 justifyContent: "space-between",
                 gap: "0.5rem",
                 marginBottom: "0.25rem",
               }}
             >
               <div
                 style={{
                   fontSize: "0.8rem",
                   color: "#4b5563",
                 }}
               >
                 <strong>Interaction log</strong> (each check / update)
               </div>
               <button
                 type="button"
                 onClick={openLogWindow}
                 style={{
                   padding: "0.25rem 0.6rem",
                   borderRadius: 999,
                   border: "1px solid #cbd5f5",
                   backgroundColor: "#eff6ff",
                   fontSize: "0.7rem",
                   cursor: "pointer",
                   whiteSpace: "nowrap",
                 }}
               >
                 Pop out full log
               </button>
             </div>

             <div
               style={{
                 maxHeight: 340, // a bit taller than before
                 overflowY: "auto",
                 borderRadius: 10,
                 border: "1px solid #e5e7eb",
                 backgroundColor: "rgba(249,250,251,0.9)",
                 padding: "0.5rem 0.65rem",
                 fontSize: "0.72rem",
                 fontFamily: "monospace",
               }}
             >
               {logEntries.length === 0 && (
                 <div style={{ color: "#9ca3af" }}>
                   No log entries recorded.
                 </div>
               )}
               {logEntries.map((entry) => (
                 <div
                   key={entry.id}
                   style={{
                     marginBottom: "0.25rem",
                     borderBottom: "1px dotted #e5e7eb",
                     paddingBottom: "0.2rem",
                   }}
                 >
                   <div style={{ color: "#6b7280" }}>
                     [{entry.ts}]{" "}
                     {entry.quizIndex !== null
                       ? `Quiz item ${entry.quizIndex + 1}`
                       : "Practice / system"}{" "}
                     {entry.columnIndex !== null
                       ? `· Column ${entry.columnIndex + 1}`
                       : ""}
                   </div>
                   <div>{entry.message}</div>
                 </div>
               ))}
             </div>

             <div
               style={{
                 fontSize: "0.7rem",
                 color: "#6b7280",
                 marginTop: "0.4rem",
               }}
             >
               Take a screenshot of this receipt (including your email
               watermark) and upload it as your proof of completion.
             </div>
           </div>
         </section>
       )}
       
        

        <hr style={{ margin: "1.3rem 0" }} />
        <details>
          <summary style={{ fontSize: "0.85rem", cursor: "pointer" }}>
            Syntax help
          </summary>
          <ul style={{ fontSize: "0.8rem", color: "#4b5563" }}>
            <li>Variables: capital letters (P, Q, R, ...)</li>
            <li>
              Negation: <code>¬P</code> or <code>~P</code>
            </li>
            <li>
              Conjunction: <code>P ∧ Q</code> or <code>P &amp; Q</code>
            </li>
            <li>
              Disjunction: <code>P ∨ Q</code> or <code>P v Q</code>
            </li>
            <li>
              Conditional: <code>P → Q</code> or <code>P -&gt; Q</code>
            </li>
            <li>
              Biconditional: <code>P ↔ Q</code> or <code>P &lt;-&gt; Q</code>
            </li>
            <li>
              For full grammaticality in this tool, binary connectives should
              appear inside parentheses, e.g. <code>(P ∧ Q)</code>.
            </li>
          </ul>
        </details>
      </div>
    </div>
  );
};

export default App;
