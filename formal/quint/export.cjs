#!/usr/bin/env node
'use strict';

// Serialization adapter only. All boards, transitions and properties are
// evaluated by the pinned Quint interpreter from bml.qnt.
const { spawnSync } = require('node:child_process');
const { mkdtempSync, readFileSync, rmSync } = require('node:fs');
const { tmpdir } = require('node:os');
const path = require('node:path');

const runtime = require('./node_modules/@informalsystems/quint/package.json');
if (runtime.version !== '0.33.1') {
  throw new Error('Expected Quint 0.33.1, found ' + runtime.version);
}
const cli = path.join(__dirname, 'node_modules', '@informalsystems', 'quint', 'dist', 'src', 'cli.js');
const temporary = mkdtempSync(path.join(tmpdir(), 'traffic-quint-'));
try {
  const tracePath = path.join(temporary, 'transitions.itf.json');
  const result = spawnSync(process.execPath, [
    cli, 'run', 'bml_export.qnt',
    '--backend=typescript', '--max-samples=1', '--max-steps=0',
    '--seed=20261118', '--verbosity=0', '--out-itf=' + tracePath,
  ], { cwd: __dirname, encoding: 'utf8', maxBuffer: 4 * 1024 * 1024 });
  if (result.error) throw result.error;
  if (result.status !== 0) {
    throw new Error('Quint export failed (' + result.status + '): ' + result.stderr + '\n' + result.stdout);
  }
  const trace = JSON.parse(readFileSync(tracePath, 'utf8'));
  if (trace['#meta']?.status !== 'ok' || trace.states?.length !== 1) {
    throw new Error('Expected exactly one successful deterministic Quint state');
  }
  const rows = trace.states[0].rows;
  if (!Array.isArray(rows) || rows.length !== 3120) {
    throw new Error('Expected 3120 exhaustive transition rows, got ' + rows?.length);
  }
  const integer = x => {
    const value = (x && typeof x === 'object') ? x['#bigint'] : x;
    if (!/^-?\d+$/.test(String(value))) throw new Error('Invalid ITF integer');
    return String(value);
  };
  const lines = rows.map(row => {
    if (!Array.isArray(row) || row.length !== 10) throw new Error('Invalid row width');
    return row.map(integer).join('\t');
  });
  process.stdout.write(lines.join('\n') + '\n');
} finally {
  rmSync(temporary, { recursive: true, force: true });
}
