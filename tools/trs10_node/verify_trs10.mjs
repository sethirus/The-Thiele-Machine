#!/usr/bin/env node

import { execFileSync } from "node:child_process";
import { createHash, createPublicKey, verify as verifySignature } from "node:crypto";
import { existsSync, mkdtempSync, readFileSync, rmSync, statSync, writeFileSync } from "node:fs";
import path from "node:path";
import { tmpdir } from "node:os";
import { fileURLToPath, pathToFileURL } from "node:url";

const TRS10_VERSION = "TRS-1.0";
const SIG_SCHEME = "ed25519";
const EXECUTION_STATE_MODEL = "thiele.vmstate.v1";
const ED25519_SPKI_PREFIX = Buffer.from("302a300506032b6570032100", "hex");
const REGISTER_NAMES = new Map([
  ["zero", 0],
  ["sp", 31],
  ...Array.from({ length: 32 }, (_, index) => [`r${index}`, index]),
]);

function fail(message) {
  throw new Error(message);
}

function parseArgs(argv) {
  if (argv.length < 3) {
    fail("usage: node verify_trs10.mjs <receipt.json> --trusted-pubkey <hex> [--base-dir <dir>]");
  }
  const args = { receipt: argv[2], trustedPubkey: null, baseDir: null };
  for (let index = 3; index < argv.length; index += 1) {
    const token = argv[index];
    if (token === "--trusted-pubkey") {
      args.trustedPubkey = argv[index + 1];
      index += 1;
    } else if (token === "--base-dir") {
      args.baseDir = argv[index + 1];
      index += 1;
    } else {
      fail(`unknown argument: ${token}`);
    }
  }
  if (!args.trustedPubkey) {
    fail("missing required argument: --trusted-pubkey");
  }
  return args;
}

function sortCanonical(value) {
  if (value === null || typeof value === "boolean" || typeof value === "number" || typeof value === "string") {
    return value;
  }
  if (Array.isArray(value)) {
    return value.map(sortCanonical);
  }
  if (typeof value === "object") {
    return Object.fromEntries(
      Object.keys(value)
        .sort()
        .map((key) => [key, sortCanonical(value[key])]),
    );
  }
  return String(value);
}

function canonicalJsonBytes(obj) {
  return Buffer.from(JSON.stringify(sortCanonical(obj)), "utf8");
}

function sha256Bytes(buffer) {
  return createHash("sha256").update(buffer).digest("hex");
}

function sha256File(filePath) {
  return sha256Bytes(readFileSync(filePath));
}

function validateReceiptPath(pathValue, fieldName) {
  if (typeof pathValue !== "string" || pathValue.length === 0) {
    fail(`${fieldName} must be a non-empty string`);
  }
  if (path.isAbsolute(pathValue) || path.posix.basename(pathValue) !== pathValue || path.win32.basename(pathValue) !== pathValue) {
    fail(`${fieldName} uses unsupported path form: ${JSON.stringify(pathValue)}`);
  }
  if (pathValue.includes("/") || pathValue.includes("\\") || pathValue === "." || pathValue === "..") {
    fail(`${fieldName} uses unsupported path form: ${JSON.stringify(pathValue)}`);
  }
  return pathValue;
}

function validateHexString(value, fieldName, expectedLength) {
  if (typeof value !== "string" || value.length !== expectedLength || !/^[0-9a-fA-F]+$/.test(value)) {
    fail(`${fieldName} must be a ${expectedLength}-character hex string`);
  }
  return value;
}

function validateIntField(value, fieldName) {
  if (!Number.isInteger(value)) {
    fail(`${fieldName} must be an integer`);
  }
  return value;
}

function validateStrField(value, fieldName) {
  if (typeof value !== "string" || value.length === 0) {
    fail(`${fieldName} must be a non-empty string`);
  }
  return value;
}

function extractSignedPayload(receipt) {
  if (receipt.version !== TRS10_VERSION) {
    fail(`Unsupported receipt version: ${JSON.stringify(receipt.version)}`);
  }

  const kind = receipt.kind ?? "fileset";
  const payload = { version: receipt.version, kind };

  if (kind === "fileset") {
    if ("program" in receipt || "execution" in receipt) {
      fail("Hybrid fileset receipt must not include execution fields");
    }
    if (!Array.isArray(receipt.files) || receipt.files.length === 0) {
      fail("Receipt must contain a non-empty files list");
    }
    for (const entry of receipt.files) {
      if (typeof entry !== "object" || entry === null) {
        fail("Receipt file entries must be objects");
      }
      for (const field of ["path", "sha256", "size"]) {
        if (!(field in entry)) {
          fail(`Receipt file entry missing field: ${field}`);
        }
      }
      validateReceiptPath(entry.path, "fileset.path");
      validateHexString(entry.sha256, "fileset.sha256", 64);
      validateIntField(entry.size, "fileset.size");
    }
    payload.files = receipt.files;
  } else if (kind === "execution") {
    if ("files" in receipt) {
      fail("Hybrid execution receipt must not include fileset fields");
    }
    if (typeof receipt.program !== "object" || receipt.program === null) {
      fail("Execution receipt missing program object");
    }
    if (typeof receipt.execution !== "object" || receipt.execution === null) {
      fail("Execution receipt missing execution object");
    }
    for (const field of ["path", "source_sha256", "canonical_sha256", "fuel", "line_count"]) {
      if (!(field in receipt.program)) {
        fail(`Execution receipt program missing field: ${field}`);
      }
    }
    validateReceiptPath(receipt.program.path, "program.path");
    validateHexString(receipt.program.source_sha256, "program.source_sha256", 64);
    validateHexString(receipt.program.canonical_sha256, "program.canonical_sha256", 64);
    validateIntField(receipt.program.fuel, "program.fuel");
    validateIntField(receipt.program.line_count, "program.line_count");
    for (const field of ["state_model", "pre_state_digest", "post_state_digest", "mu_start", "mu_end", "mu_delta"]) {
      if (!(field in receipt.execution)) {
        fail(`Execution receipt execution missing field: ${field}`);
      }
    }
    validateStrField(receipt.execution.state_model, "execution.state_model");
    validateHexString(receipt.execution.pre_state_digest, "execution.pre_state_digest", 64);
    validateHexString(receipt.execution.post_state_digest, "execution.post_state_digest", 64);
    validateIntField(receipt.execution.mu_start, "execution.mu_start");
    validateIntField(receipt.execution.mu_end, "execution.mu_end");
    validateIntField(receipt.execution.mu_delta, "execution.mu_delta");
    payload.program = receipt.program;
    payload.execution = receipt.execution;
  } else {
    fail(`Unsupported receipt kind: ${JSON.stringify(kind)}`);
  }

  if ("metadata" in receipt) {
    payload.metadata = receipt.metadata;
  }
  if ("key_id" in receipt) {
    validateStrField(receipt.key_id, "key_id");
    payload.key_id = receipt.key_id;
  }
  if (!("global_digest" in receipt)) {
    fail("Receipt missing global_digest");
  }
  validateHexString(receipt.global_digest, "global_digest", 64);
  if (receipt.sig_scheme !== SIG_SCHEME) {
    fail(`Unsupported signature scheme: ${JSON.stringify(receipt.sig_scheme)}`);
  }
  if (!("signature" in receipt)) {
    fail("Receipt missing signature");
  }
  validateHexString(receipt.signature, "signature", 128);
  return payload;
}

function verifyDigestSignature(publicKeyHex, signatureHex, digestHex) {
  const publicKeyDer = Buffer.concat([ED25519_SPKI_PREFIX, Buffer.from(publicKeyHex.trim(), "hex")]);
  const publicKey = createPublicKey({ key: publicKeyDer, format: "der", type: "spki" });
  const ok = verifySignature(null, Buffer.from(digestHex, "utf8"), publicKey, Buffer.from(signatureHex, "hex"));
  if (!ok) {
    fail("invalid signature");
  }
}

function stripComments(line) {
  let output = line.trim();
  for (const marker of ["#", ";", "//"]) {
    const index = output.indexOf(marker);
    if (index >= 0) {
      output = output.slice(0, index).trim();
    }
  }
  return output;
}

function resolveToken(token, labels) {
  if (REGISTER_NAMES.has(token)) {
    return String(REGISTER_NAMES.get(token));
  }
  if (labels.has(token)) {
    return String(labels.get(token));
  }
  return token;
}

function preprocessSource(sourceText) {
  const rawLines = [];
  const labels = new Map();
  let pc = 0;

  for (const rawLine of sourceText.split(/\r?\n/)) {
    const line = stripComments(rawLine);
    if (!line) {
      continue;
    }
    if (line.endsWith(":")) {
      labels.set(line.slice(0, -1).trim(), pc);
      continue;
    }
    const upper = line.split(/\s+/, 1)[0].toUpperCase();
    if (upper === "FUEL") {
      continue;
    }
    rawLines.push({ line, upper });
    if (!upper.startsWith("INIT_") && upper !== ".DATA" && upper !== "INIT_MEM") {
      pc += 1;
    }
  }

  const output = [];
  for (const { line, upper } of rawLines) {
    if (upper === "NOP") {
      output.push("LOAD_IMM 0 0 0");
      continue;
    }
    if (upper === "MOV") {
      const parts = line.split(/\s+/);
      output.push(`XFER ${resolveToken(parts[1], labels)} ${resolveToken(parts[2], labels)} 1`);
      continue;
    }
    if (line.includes("{")) {
      let rebuilt = "";
      let index = 0;
      let firstToken = true;
      while (index < line.length) {
        const char = line[index];
        if (char === "{") {
          const end = line.indexOf("}", index);
          rebuilt += line.slice(index, end + 1);
          index = end + 1;
          firstToken = false;
          continue;
        }
        if (char === " " || char === "\t") {
          rebuilt += char;
          index += 1;
          continue;
        }
        let end = index;
        while (end < line.length && ![" ", "\t", "{", "}"].includes(line[end])) {
          end += 1;
        }
        const token = line.slice(index, end);
        rebuilt += firstToken ? token : resolveToken(token, labels);
        firstToken = false;
        index = end;
      }
      output.push(rebuilt);
      continue;
    }

    const parts = line.split(/\s+/);
    output.push([parts[0], ...parts.slice(1).map((token) => resolveToken(token, labels))].join(" "));
  }
  return output;
}

function extractFuel(sourceText, defaultFuel = 256) {
  for (const rawLine of sourceText.split(/\r?\n/)) {
    const line = stripComments(rawLine);
    if (!line) {
      continue;
    }
    const parts = line.split(/\s+/);
    if (parts[0]?.toUpperCase() === "FUEL" && parts.length > 1) {
      return Number.parseInt(parts[1], 0);
    }
  }
  return defaultFuel;
}

function canonicalizeProgram(programPath) {
  const sourceText = readFileSync(programPath, "utf8");
  const preprocessedLines = preprocessSource(sourceText);
  const fuel = extractFuel(sourceText);
  const traceLines = [`FUEL ${fuel}`];
  for (const line of preprocessedLines) {
    const parts = line.split(/\s+/);
    if (parts[0]?.toUpperCase() === ".DATA" && parts.length >= 3) {
      traceLines.push(`INIT_MEM ${parts[1]} ${parts[2]}`);
    } else {
      traceLines.push(line);
    }
  }
  const canonicalProgram = { format: "thiele.trace.v1", lines: traceLines };
  return {
    sourceSha256: sha256File(programPath),
    canonicalSha256: sha256Bytes(canonicalJsonBytes(canonicalProgram)),
    fuel,
    lineCount: traceLines.length,
    canonicalLines: traceLines,
  };
}

function canonicalProgramFacts(programPath) {
  const canonicalProgram = canonicalizeProgram(programPath);
  return {
    sourceSha256: canonicalProgram.sourceSha256,
    canonicalSha256: canonicalProgram.canonicalSha256,
    fuel: canonicalProgram.fuel,
    lineCount: canonicalProgram.lineCount,
  };
}

function splitInitLines(canonicalLines) {
  return canonicalLines.filter((line) => {
    const opcode = line.split(/\s+/, 1)[0]?.toUpperCase();
    return opcode === "FUEL" || opcode?.startsWith("INIT_");
  });
}

function runVmTrace(lines, repoRoot) {
  const runnerPath = path.join(repoRoot, "build", "extracted_vm_runner");
  if (!existsSync(runnerPath)) {
    fail(`extracted VM runner not found: ${runnerPath}`);
  }
  const tempDir = mkdtempSync(path.join(tmpdir(), "trs10-node-"));
  const tracePath = path.join(tempDir, "trace.txt");
  writeFileSync(tracePath, `${lines.join("\n")}\n`, "utf8");
  try {
    const stdout = execFileSync(runnerPath, [tracePath], { cwd: repoRoot, encoding: "utf8" });
    return JSON.parse(stdout);
  } finally {
    rmSync(tempDir, { recursive: true, force: true });
  }
}

function normalizeValue(value) {
  if (value === null || typeof value === "boolean" || typeof value === "number" || typeof value === "string") {
    return value;
  }
  if (Array.isArray(value)) {
    return value.map(normalizeValue);
  }
  if (typeof value === "object") {
    return Object.fromEntries(Object.keys(value).sort().map((key) => [String(key), normalizeValue(value[key])]));
  }
  return String(value);
}

function normalizeVmState(state) {
  const modulesSource = Array.isArray(state.modules) ? state.modules : (state.graph?.modules ?? []);
  const modules = modulesSource
    .map((module) => ({
      id: Number(module.id ?? 0),
      region: Array.isArray(module.region) ? module.region.map((item) => Number(item)) : [],
      axioms: normalizeValue(module.axioms ?? []),
    }))
    .sort((left, right) => left.id - right.id);

  return {
    pc: Number(state.pc ?? 0),
    mu: Number(state.mu ?? 0),
    err: Boolean(state.err ?? false),
    regs: Array.isArray(state.regs) ? state.regs.slice(0, 32).map((value) => Number(value)) : [],
    mem: Array.isArray(state.mem) ? state.mem.map((value) => Number(value)) : [],
    csrs: normalizeValue(state.csrs ?? {}),
    modules,
    mu_tensor: Array.isArray(state.mu_tensor) ? state.mu_tensor.map((value) => Number(value)) : [],
    logic_acc: Number(state.logic_acc ?? 0),
    mstatus: Number(state.mstatus ?? 0),
    certified: Boolean(state.certified ?? false),
    witness: Array.isArray(state.witness) ? state.witness.map((value) => Number(value)) : [],
  };
}

function digestVmState(state) {
  return sha256Bytes(canonicalJsonBytes(normalizeVmState(state)));
}

function verifyFileset(receipt, baseDir) {
  for (const entry of receipt.files) {
    const relativePath = validateReceiptPath(entry.path, "fileset.path");
    const filePath = path.join(baseDir, relativePath);
    if (!existsSync(filePath) || !statSync(filePath).isFile()) {
      fail(`Receipt file missing during verification: ${filePath}`);
    }
    if (sha256File(filePath) !== entry.sha256) {
      fail(`Digest mismatch for ${entry.path}`);
    }
    if (statSync(filePath).size !== entry.size) {
      fail(`Size mismatch for ${entry.path}`);
    }
  }
}

function verifyExecution(receipt, baseDir, repoRoot) {
  const relativePath = validateReceiptPath(receipt.program.path, "program.path");
  const programPath = path.join(baseDir, relativePath);
  if (!existsSync(programPath) || !statSync(programPath).isFile()) {
    fail(`Execution receipt program missing during verification: ${programPath}`);
  }

  const canonicalProgram = canonicalizeProgram(programPath);
  if (canonicalProgram.sourceSha256 !== receipt.program.source_sha256) {
    fail("Execution receipt source_sha256 does not match program file");
  }
  if (canonicalProgram.canonicalSha256 !== receipt.program.canonical_sha256) {
    fail("Execution receipt canonical_sha256 does not match canonicalized program");
  }
  if (canonicalProgram.fuel !== receipt.program.fuel) {
    fail("Execution receipt fuel does not match canonicalized program");
  }
  if (canonicalProgram.lineCount !== receipt.program.line_count) {
    fail("Execution receipt line_count does not match canonicalized program");
  }

  const preState = runVmTrace(splitInitLines(canonicalProgram.canonicalLines), repoRoot);
  const postState = runVmTrace(canonicalProgram.canonicalLines, repoRoot);

  if (receipt.execution.state_model !== EXECUTION_STATE_MODEL) {
    fail(`Unsupported execution state model: ${JSON.stringify(receipt.execution.state_model)}`);
  }
  if (digestVmState(preState) !== receipt.execution.pre_state_digest) {
    fail("Execution receipt pre_state_digest mismatch");
  }
  if (digestVmState(postState) !== receipt.execution.post_state_digest) {
    fail("Execution receipt post_state_digest mismatch");
  }
  const muStart = Number(preState.mu ?? 0);
  const muEnd = Number(postState.mu ?? 0);
  if (receipt.execution.mu_start !== muStart) {
    fail("Execution receipt mu_start mismatch");
  }
  if (receipt.execution.mu_end !== muEnd) {
    fail("Execution receipt mu_end mismatch");
  }
  if (receipt.execution.mu_delta !== muEnd - muStart) {
    fail("Execution receipt mu_delta mismatch");
  }
}

function main() {
  const args = parseArgs(process.argv);
  const receiptPath = path.resolve(args.receipt);
  const baseDir = path.resolve(args.baseDir ?? path.dirname(receiptPath));
  const repoRoot = path.resolve(path.dirname(new URL(import.meta.url).pathname), "..", "..");
  const receipt = JSON.parse(readFileSync(receiptPath, "utf8"));
  const payload = extractSignedPayload(receipt);
  const expectedDigest = sha256Bytes(canonicalJsonBytes(payload));
  if (receipt.global_digest !== expectedDigest) {
    fail("Receipt global_digest does not match canonical payload digest");
  }
  verifyDigestSignature(args.trustedPubkey, receipt.signature, expectedDigest);

  if (payload.kind === "fileset") {
    verifyFileset(receipt, baseDir);
  } else {
    verifyExecution(receipt, baseDir, repoRoot);
  }
  console.log("Receipt verification succeeded");
}

export { canonicalProgramFacts, canonicalizeProgram };

const isDirectRun = process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href;

if (isDirectRun) {
  try {
    main();
  } catch (error) {
    console.error(`Receipt verification failed: ${error.message}`);
    process.exit(1);
  }
}