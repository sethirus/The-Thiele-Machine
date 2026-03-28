#!/usr/bin/env node

import path from "node:path";

import { canonicalProgramFacts } from "./verify_trs10.mjs";

if (process.argv.length !== 3) {
  console.error("usage: node canonicalize_program.mjs <program.asm>");
  process.exit(1);
}

const programPath = path.resolve(process.argv[2]);
console.log(JSON.stringify(canonicalProgramFacts(programPath)));