# Smoosh — Lean 4 Implementation

A Lean 4 translation of [Smoosh](https://github.com/mgree/smoosh), a POSIX-compatible shell semantics. The original implementation is written in [Lem](https://www.cl.cam.ac.uk/~pes20/lem/) (OCaml-based specification language). This Lean port provides a symbolic execution engine for shell scripts, with a test runner that validates behavior against expected outputs.

## Prerequisites

- **Lean 4** toolchain: `leanprover/lean4:v4.27.0` (specified in `lean-toolchain`)
- **Lake** build system (bundled with Lean)

## Building

```bash
cd lean-smoosh

# Build the test runner executable
lake build smoosh-test

# Build the library only
lake build Smoosh
```

The build produces:
- `.lake/build/bin/smoosh-test` — test runner for shell JSON test cases
- `.lake/build/lib/` — compiled Lean library

## Running Tests

All test files are self-contained in the `tests/` directory. The `tools/` directory contains the OCaml `dump_ast` binary for regenerating JSON ASTs from `.test` files.

### Run All Tests

```bash
# Run full test suite (builds smoosh-test if needed)
bash run_tests.sh

# Verbose mode — shows failure details
bash run_tests.sh --verbose

# Filter to specific tests
bash run_tests.sh --filter=builtin.echo
```

### Run a Single Test

```bash
.lake/build/bin/smoosh-test tests/shell_json/<test-name>.json
```

This prints the stdout output from the symbolic shell execution.

### Regenerating JSON ASTs

If you edit a `.test` file, regenerate its JSON AST using the OCaml `dump_ast` binary:

```bash
# Generate JSON from a shell test script
tools/dump_ast tests/shell/builtin.echo.exitcode.test > tests/shell_json/builtin.echo.exitcode.json
```

### Test Suite Details

The test suite (in `run_tests.sh`) compares:
- **stdout** — against `.out` files (empty expected if no `.out` file)
- **exit code** — against `.ec` files (default expected: 0)
- Skipped tests: eval builtin tests (require runtime parsing) and async trap tests
- Each test runs with a 5-second timeout

### Current Test Results

| Metric | Count |
|---|---|
| Total test JSON files | 186 |
| Total tested (excl. skipped) | 180 |
| **Passing** | **114** |
| **Failing** | **66** |
| **Skipped (eval/async)** | **6** |
| **Pass rate (of tested)** | **63%** |

*Tests without `.out`/`.ec` files pass if ec=0 and stdout is empty.*

**Skipped tests**: `builtin.eval`, `builtin.eval.break`, `builtin.eval.trap`, `semantics.eval.makeadder` (require `eval` runtime parsing), `semantics.traps.async`, `semantics.traps.inherit` (require async signal delivery).

#### Failure Breakdown

| Category | Count | Description |
|---|---|---|
| External commands / `$TEST_SHELL` dependency | ~25 | Tests needing real shell execution, external utilities (`grep`, `sed`, `kill`, `mkfifo`, etc.) |
| Filesystem / glob / pattern matching | ~10 | Tests needing real filesystem (glob expansion, `touch`, file tests) |
| Trap / signal handling gaps | ~3 | Signal delivery, trap variable expansion timing |
| Builtin behavior gaps | ~9 | `dot`/`source`, `hash`, `history`, `times` |
| Background / wait / pipe semantics | ~6 | PID tracking, `wait` for killed processes, job control |
| Interactive / monitoring modes | ~5 | Interactive prompts, job control, monitor mode |
| Other (tilde, IFS, redir) | ~4 | Tilde expansion, IFS edge cases, FD redirection |

#### Failing tests

<details>
<summary>Click to expand full list (66 failures)</summary>

| Test | Category |
|---|---|
| `benchmark.fact5` | Stack overflow (recursive factorial with `ulimit`) |
| `benchmark.while` | External commands (`head`, `sed`) |
| `builtin.cd.pwd` | TEST_ONLY: filesystem-dependent |
| `builtin.command.exec` | `command -p` path lookup (symbolic execve) |
| `builtin.dot.break` | `break` inside sourced file |
| `builtin.dot.path` | `source` PATH lookup |
| `builtin.dot.return` | `return` inside sourced file |
| `builtin.dot.unreadable` | Unreadable file error handling |
| `builtin.exec.modernish.mkfifo.loop` | External `mkfifo` command |
| `builtin.export` | External commands needed |
| `builtin.export.override` | Symbolic execve |
| `builtin.export.unset` | External `grep` |
| `builtin.hash.nonposix` | External `ls`, `grep` |
| `builtin.history.nonposix` | `history` builtin (non-POSIX) |
| `builtin.jobs` | External `grep` |
| `builtin.kill0_+5` | Signal delivery |
| `builtin.kill.jobs` | Signal delivery / job control |
| `builtin.kill.signame` | Signal delivery / trap interaction |
| `builtin.readonly.assign.interactive` | Interactive mode |
| `builtin.set.quoted` | External `grep` |
| `builtin.source.setvar` | `source`/`dot` unimplemented |
| `builtin.test.nonposix` | TEST_ONLY: filesystem |
| `builtin.test.-nt.-ot.absent` | TEST_ONLY: filesystem |
| `builtin.test.symlink` | TEST_ONLY: filesystem |
| `builtin.times.ioerror` | Complex pipe/signal interaction |
| `builtin.trap.redirect` | Variable expansion timing in trap handler |
| `semantics.background.nojobs.stdin` | Background stdin redirect |
| `semantics.background.pid` | PID tracking |
| `semantics.background.pipe.pid` | PID tracking in pipes |
| `semantics.backtick.fds` | Backtick FD handling |
| `semantics.backtick.ppid` | `$PPID` (external) |
| `semantics.-C` | TEST_ONLY: noclobber |
| `semantics.command.argv0` | `$0` handling (external) |
| `semantics.dot.glob` | Glob expansion (filesystem) |
| `semantics.errexit.carryover` | Symbolic execve |
| `semantics.errexit.trap` | Signal delivery (`kill -s USR1 $$`) |
| `semantics.error.noninteractive` | External script execution |
| `semantics.escaping.backslash` | External commands |
| `semantics.escaping.quote` | External commands |
| `semantics.evalorder.fun` | External `rm`, file existence checks |
| `semantics.expansion.quotes.adjacent` | Glob expansion (filesystem) |
| `semantics.-h.nonposix` | `hash` builtin |
| `semantics.interactive.expansion.exit` | Interactive mode |
| `semantics.kill.traps` | Signal delivery |
| `semantics.monitoring.ttou` | Monitor mode / TTOU |
| `semantics.pattern.hyphen` | Glob expansion (filesystem) |
| `semantics.pattern.modernish` | Glob expansion (filesystem) |
| `semantics.pattern.rightbracket` | Glob expansion (filesystem) |
| `semantics.pipe.chained` | External `seq` |
| `semantics.redir.fds` | High FD redirection (symbolic execve) |
| `semantics.redir.from` | TEST_ONLY: filesystem |
| `semantics.redir.toomany` | TEST_ONLY: external `seq` |
| `semantics.return.not` | TEST_ONLY: OCaml mismatch |
| `semantics.simple.link` | External commands |
| `semantics.slash.glob` | Glob expansion (filesystem) |
| `semantics.subshell.background.traps` | Signal delivery |
| `semantics.tilde.colon` | Tilde expansion in colon paths |
| `semantics.wait.alreadydead` | Signal delivery / wait |
| `sh.-c.arg0` | External execution |
| `sh.env.ppid` | External execution |
| `sh.file.weirdness` | External execution |
| `sh.interactive.ps1` | Interactive mode |
| `sh.monitor.bg` | Monitor mode |
| `sh.monitor.fg` | Monitor mode |
| `sh.ps1.override` | Interactive mode |
| `sh.set.ifs` | External script execution |

</details>

#### Tests Fixed (previously failing, now passing)

<details>
<summary>Click to expand list of fixed tests</summary>

The following tests were fixed through targeted translation corrections:

| Test | Fix Applied |
|---|---|
| `builtin.command.keyword` | Fixed `command -v` keyword handling |
| `builtin.command.nospecial` | Fixed stderr format |
| `builtin.dot.nonexistent` | Fixed error message |
| `builtin.exec.badredir` | Fixed exit code for bad redirections |
| `builtin.exitcode` | Fixed builtin exit code propagation |
| `builtin.pwd.exitcode` | Fixed `pwd` exit code |
| `builtin.source.nonexistent` | Fixed error message |
| `builtin.source.nonexistent.earlyexit` | Fixed early exit behavior |
| `builtin.trap.exit.subshell` | Fixed EXIT trap in subshell via `osWaitpid` |
| `builtin.trap.nested` | Fixed `parseTrapString` with nesting-aware splitting + quote-aware words |
| `builtin.trap.return` | Fixed `parseTrapString` function definition parsing |
| `builtin.trap.subshell.false.exit` | Fixed subshell exit code with trap |
| `builtin.trap.subshell.loud` | Fixed `parseTrapString` subshell parsing with `splitTopLevel` |
| `builtin.trap.subshell.loud2` | Fixed `parseTrapString` subshell parsing |
| `builtin.trap.subshell.truefalse` | Fixed subshell trap interaction |
| `builtin.unset` | Fixed unset error message |
| `parse.error` | Fixed parse error handling |
| `semantics.background` | Fixed `osWaitpid` to step background processes |
| `semantics.backtick.exit` | Fixed backtick exit status |
| `semantics.for.readonly` | Fixed readonly in for loop |
| `semantics.fun.error.restore` | Fixed `osOpenFileForRedir` to check file existence for `from_` redirects |
| `semantics.redir.close` | Fixed redirect close + exit code |
| `semantics.return.trap` | Fixed return + trap interaction |
| `semantics.substring.quotes` | Fixed substring with quotes |
| `semantics.var.alt.nullifs` | Fixed `$@` with null IFS alternative |
| `builtin.alias.empty` | Fixed `builtinAlias` `splitStringOn` → `String.splitOn` for empty alias values + alias expansion in `runCommand` |
| `builtin.trap.supershell` | Fixed `clearSupershellTraps` to reset supershell traps in subshell + `trap -p` display for supershell traps |

</details>

---

### Implementation Progress & Key Fixes

<details>
<summary>Click to expand detailed implementation notes</summary>

#### Critical Bug Fix: `osWaitpid` Background Process Stepping

**Problem**: The Lean `osWaitpid` in `OsSymbolic.lean` had a spurious `findJobWithPid` check at the top that short-circuited for running jobs, returning `(os, none)` instead of stepping the child process via the proc table.

**Root Cause**: The OCaml `symbolic_step_pid` (which implements `os_waitpid`) never checks the job table — it works directly with the proc table via `proc_select`. The Lean translation incorrectly added a job-table check that prevented background processes from ever being stepped during `wait`.

**Fix**: Removed the `findJobWithPid` guard from `osWaitpid`. The job table check is correctly done by the wrapper functions (`waitpidOrLookup`, `waitForJob`, `waitForPid`) in `Os.lean`.

**Impact**: Fixed `semantics.background` and enabled correct background process output capture.

#### EXIT Trap Handling in `osWaitpid`

Added EXIT trap processing when a child process exits (its statement reaches `Done`). The OCaml code checks for an EXIT trap handler in `symbolic_step_pid` and, if found, keeps the process running with the handler as a new statement. This was missing in the initial Lean translation.

#### `builtinWait` (Wait for All Background Jobs)

Implemented the OCaml `builtin_wait` logic for the no-arguments case: iterate through active jobs (running or stopped), create `Stmt.wait` for each PID, and sequence them with `Stmt.semi`, ending with `Stmt.done` to return exit code 0.

#### Field Splitting & IFS Handling

- Fixed `$@` expansion when IFS is null (should not split, per POSIX)
- Fixed `toFields` to properly handle empty IFS by not inserting field separators

#### Escaping & Quote Removal

- Fixed multiple escaping edge cases in `removeQuotes` and `quoteRemoval`
- Fixed `tildePrefix` to handle quoted segments correctly

#### Builtin Exit Codes

- Fixed exit code propagation for special builtins (`break`, `continue`, `return`, `exit`)
- Fixed `checkTrapsWrap` to use `.unchecked` mode matching OCaml behavior

#### Trap Handling

- Fixed `builtinTrap` signal parsing to match OCaml's `trap_parse_signal`
- Fixed return/break interaction with trap handlers
- Fixed nested trap execution

#### Redirect Close

- Fixed `osCloseAndSaveFd` to properly save FIFO numbers for later restoration
- Fixed `restoreFds` to handle the `Close` variant of saved FD info

</details>

---

## Project Structure

```
lean-smoosh/
├── lakefile.toml           # Build configuration
├── lean-toolchain          # Lean version (v4.27.0)
├── Main.lean               # Test runner entry point
├── run_tests.sh            # Automated test runner script
├── Smoosh/
│   ├── Prelude.lean         # Types, utilities, AST definitions
│   ├── Num.lean             # Numeric parsing and formatting
│   ├── Signal.lean          # Signal types and conversions
│   ├── Os.lean              # OS state, typeclass, helpers
│   ├── OsSymbolic.lean      # Symbolic OS implementation
│   ├── Pattern.lean         # Glob pattern parsing and matching
│   ├── SmooshPath.lean      # Pathname expansion (globbing)
│   ├── Fields.lean          # Field splitting, quote removal
│   ├── Arith.lean           # Arithmetic expression evaluation
│   ├── Test.lean            # `test`/`[` builtin expression parser
│   ├── Command.lean         # Builtins and command dispatch
│   ├── Semantics.lean       # Core step evaluation engine
│   ├── FromJson.lean        # JSON → AST parser for test cases
│   └── Basic.lean           # Module re-export
├── tests/
│   ├── shell_json/          # 186 pre-parsed JSON ASTs (from dump_ast)
│   └── shell/               # Expected outputs (.out, .ec, .err) + test scripts (.test)
└── tools/
    ├── dump_ast             # OCaml binary: parses .test → JSON AST
    └── dump_ast.ml          # Source code for dump_ast (reference)
```

---

## Function Mapping: OCaml (Lem) → Lean

Below is a comprehensive mapping of functions from each OCaml `.lem` source file to their Lean counterparts. Functions are grouped by source file.

### `smoosh_prelude.lem` → `Smoosh/Prelude.lean`

| OCaml (Lem) | Lean | Notes |
|---|---|---|
| `alphabetic` | `alphabetic` | |
| `alphanumerics` | `alphanumerics` | |
| `is_alpha` | `isAlpha` | |
| `is_alphanumeric` | `isAlphanumeric` | |
| `is_variable_initial_char` | `isVariableInitialChar` | |
| `is_variable_char` | `isVariableChar` | |
| `uppercase` | `uppercase` | |
| `parens` | `parens` | |
| `tails` | `tails` | |
| `insertBy` | `insertBy` | |
| `sortBy` | `sortBy'` | |
| `sort` | — | ❌ Not translated (uses `sortBy` directly) |
| `compare_by_first` | — | ❌ Not translated (Lean uses native ordering) |
| `collect_either` | `collectEither` | |
| `isInfixOf` | `isInfixOf` | |
| `replace` | `replace'` | |
| `replace_string` | `replaceString` | |
| `ltrim_newlines_cl` | `ltrimNewlines` | |
| `intersperse` | `intersperse'` | |
| `trimr_one_newline` | `trimrOneNewline` | |
| `trimr_newlines` | `trimrNewlines` | |
| `pad_left_with` | `padLeftWith` | |
| `pad_right_with` | `padRightWith` | |
| `pad_left` | `padLeft` | |
| `pad_right` | `padRight` | |
| `maximum` | `maximum'` | |
| `break` | `break'` | |
| `spaced` | `spaced` | |
| `spaced_many` | `spacedMany` | |
| `break_on_esc` | `breakOnEsc` | |
| `split_on` | `splitOn` | |
| `split_string_on` | `splitStringOn` | |
| `adjust_nth` | `adjustNth` | |
| `between` | `between` | |
| `ambient_charclass` | `ambientCharclass` | |
| `lc_ambient` | `lcAmbient` | |
| `perms_all_clear` | `permsAllClear` | |
| `all_file_perms` | `allFilePerms` | |
| `default_umask` | `defaultUmask` | |
| `invert_file_perms` | `invertFilePerms` | |
| `invert_perms` | `invertPerms` | |
| `nat_of_file_perms` | `natOfFilePerms` | |
| `pushredir` | (inline) | Merged into `stepEval` |
| `with_redirs` | `withRedirs` | |
| `close_fd_and_then` | `closeFdAndThen` | |
| `try_avoid_fork` | `tryAvoidFork` | |
| `is_terminating_control` | (inline) | Checked within `stepEval` |
| `combine_redirs` | `combineRedirs` | |
| `is_active_job` | `isActiveJob` | In `JobInfo` |
| `string_of_job_status` | `stringOfJobStatus` | |
| `cur_prev_jobs` | `curPrevJobs` | |
| `string_of_job_number` | `stringOfJobNumber` | |
| `padded_string_of_job_status` | `paddedStringOfJobStatus` | |
| `ran_command_substitution` | — | ❌ Not translated (debug/logging) |
| `nat_of_symbolic_string` | `natOfSymbolicString` | |
| `split_equal` | `splitEqual` | |
| `try_split_assign` | `trySplitAssign` | |
| `try_extract_field` | `tryExtractField` | |
| `try_extract_dup_tgt` | `tryExtractDupTgt` | |
| `try_expand_redir` | (inline) | Inlined in `stepRedir` |
| `try_command_words` | `tryCommandWords` | |
| `try_command_fields` | `tryCommandFields` | |
| `try_command_expansion_state` | `tryCommandExpansionState` | |
| `collect_command_names` | `collectCommandNames` | |
| `parse_source_for_dot` | `parseSourceForDot` | |
| `parse_source_propagates_control` | `parseSourcePropagatesControl` | |
| `string_of_stmt` | `stringOfStmt` | Full pretty-printer |
| `string_of_words` | `stringOfWords` | |
| `string_of_entry` | `stringOfEntry` | |
| `string_of_expansion_step` | `stringOfExpansionStep` | |
| `string_of_evaluation_step` | `stringOfEvaluationStep` | |
| `string_of_symbolic` | — | ❌ Not translated |
| `string_of_symbolic_char` | — | ❌ Not translated |
| `char_list_of_symbolic_string` | — | ❌ Not translated (Lean uses `.data`) |
| `string_of_symbolic_string` | (inline) | Uses `String.ofList` directly |
| `string_of_fields` | `stringOfFields` | |
| `string_of_job` | `stringOfJob` | |
| `braces` | `braces` | |
| `background` | `background'` | |
| `show_unless` | `showUnless` | |
| `default_shell_state` | — | Inlined in `OsSymbolic.lean` as `os_empty` |
| Types, AST, etc. | Types, AST, etc. | All type definitions (Stmt, SymbolicString, ShellState, etc.) are in Prelude.lean |

### `smoosh_num.lem` → `Smoosh/Num.lean`

| OCaml (Lem) | Lean | Notes |
|---|---|---|
| `has_bit` | `hasBit` | |
| `is_whitespace` | `isWhitespace` | |
| `is_digit` | `isDigit` | |
| `is_octal_digit` | `isOctalDigit` | |
| `is_num_const_char` | `isNumConstChar` | |
| `is_numeric` | `isNumeric` | |
| `hexalpha_to_num` | `hexalphaToNum` | |
| `trim` | `trim` | |
| `readConstant` | `readConstant` | |
| `readInteger_loop` | `readIntegerLoop` | |
| `readUnsignedInteger` | `readUnsignedInteger` | |
| `readSignedInteger` | `readSignedInteger` | |
| `highestNat` | `highestNat` | |
| `readNat` | `readNat` | |
| `parse_nat` | `parseNat` | |
| `conv_digit` | `convDigit` | |
| `write_helper` | `writeHelper` | |
| `unbounded_write_base` | `unboundedWriteBase` | |
| `unbounded_write_decimal` | `unboundedWriteDecimal` | |
| `unbounded_write_octal` | `unboundedWriteOctal` | |
| `unbounded_write_hex` | `unboundedWriteHex` | |
| `unbounded_read` | `unboundedRead` | |
| `readInt64_loop` | — | ❌ Not translated (64-bit integer parsing) |
| `readInt64` | — | ❌ Not translated |
| `readInt32_loop` | — | ❌ Not translated (32-bit integer parsing) |
| `readInt32` | — | ❌ Not translated |
| `write32` | — | ❌ Not translated |
| `write64` | — | ❌ Not translated |

### `signal.lem` / `signal_platform.lem` → `Smoosh/Signal.lean`

| OCaml (Lem) | Lean | Notes |
|---|---|---|
| `all_signals` | `Signal.allSignals` | |
| `undefined_traps` | `Signal.undefinedTraps` | |
| `stopped_signals` | `Signal.stoppedSignals` | |
| `string_of_signal` | `Signal.toString` | |
| `signal_of_string` | `Signal.ofString` | |
| `signal_default_behavior` | `Signal.defaultBehavior` | |
| `ocaml_signal_of_signal` | `Signal.platformInt` | Renamed; maps signal to platform integer |
| `signal_of_ocaml_signal` | — | ❌ Not translated (platform integer → Signal) |
| `uppercase_char` | `uppercaseChar` | |

### `os.lem` → `Smoosh/Os.lean`

| OCaml (Lem) | Lean | Notes |
|---|---|---|
| `lookup_string_param` | `lookupStringParam` | |
| `lookup_concrete_param` | `lookupConcreteParam` | |
| `is_set_param` | `isSetParam` | |
| `lookup_local_param` | (inline) | Inlined in `lookupParam` |
| `lookup_local_param_loop` | (inline) | Inlined in locals handling |
| `lookup_positional_param` | (inline) | Inlined in `lookupParam` |
| `is_readonly` | (inline) | Check in `checkParam` |
| `internal_set_param` | `internalSetParam` | |
| `set_local_param` | `setLocalParam` | |
| `set_local_param_opts` | `setLocalParamOpts` | |
| `set_local_param_opts_loop` | `setLocalParamOptsLoop` | |
| `set_local_param_loop` | `setLocalParamLoop` | |
| `unset_param` | `unsetParam` | |
| `exit_with` | `exitWith` | |
| `is_monitoring` | `isMonitoring` | |
| `get_path` | `getPath` | |
| `get_function_params` | `getFunctionParams` | |
| `ps4` | `ps4` | |
| `log` | `logStep` | |
| `log_step` | `logStep` | |
| `log_trace_with` | `logTraceWith` | |
| `add_to_history` | `addToHistory` | |
| `hash_lookup` | `hashLookup` | |
| `hash_insert` | `hashInsert` | |
| `clear_hash` | `clearHash` | |
| `ec_of_job_status` | `ecOfJobStatus` | |
| `find_job_with_pid` | `findJobWithPid` | |
| `delete_job` | `deleteJob` | |
| `check_param` | `checkParam` | |
| `update_trap` | `updateTrap` | |
| `exit_trap` | `exitTrap` | |
| `clear_traps_for_subshell` | `clearTrapsForSubshell` | |
| `concretize` | `concretize` | |
| `concretize_many` | `concretizeMany` | |
| `lookup_function` | `lookupFunction` | |
| `set_function_params` | `setFunctionParams` | |
| `lookup_param` | `lookupParam` | |
| `get_env` | `getEnv` | |
| `prepare_subshell` | `prepareSubshell` | |
| `force_local_param` | `forceLocalParam` | |
| `checked_set_param` | `checkedSetParam` | |
| `set_param` | `setParam` | |
| `pop_locals` | `popLocals` | |
| `push_locals` | `pushLocals` | |
| `new_local_scope` | `newLocalScope` | |
| `xtrace` | `xtrace` | |
| `redirect` | `redirect` | |
| `restore_fds` | `restoreFds` | |
| `really_do_redirs` | `reallyDoRedirs` | |
| `do_redirs` | `doRedirs` | |
| `fork_pipe_subshell` | `forkPipeSubshell` | |
| `run_pipe` | `runPipe` | |
| `run_pipe_loop` | `runPipeLoop` | |
| `set_sh_opt` | `setShOpt` | |
| `unset_sh_opt` | `unsetShOpt` | |
| `waitpid_or_lookup` | `waitpidOrLookup` | |
| `wait_for_job` | `waitForJob` | |
| `wait_for_pid` | `waitForPid` | |
| `try_write_fd` | `tryWriteFd` | |
| `write_stdout` | `writeStdout` | |
| `write_stderr` | `writeStderr` | |
| `fail_with_code` | `failWithCode` | |
| `fail_with` | `failWith` | |
| `safe_write_stdout` | `safeWriteStdout` | |
| `safe_write_stderr` | `safeWriteStderr` | |
| `is_dir` | `isDir` | |
| `canonicalize_path` | `canonicalizePath` | |
| `canonicalize_split_path` | `canonicalizeSplitPath` | |
| `set_readonly` | `setReadonly` | |
| `set_exported` | `setExported` | |
| `collect_vars` | `collectVars` | |
| `readonly_vars` | `readonlyVars` | |
| `exported_vars` | `exportedVars` | |
| `exported_set_vars` | `exportedSetVars` | |
| `show_job` | `stringOfJob` | In Prelude.lean |
| `show_job_when` | (inline) | Inlined in job display logic |
| `active_jobs` | (inline) | Inlined in `builtinJobs` |
| `show_jobs` | (inline) | Inlined in `builtinJobs` |
| `add_job` | `addJob` | |
| `update_job_with_pid` | (inline) | Inlined in `waitpidOrLookup` |
| `update_jobs` | (inline) | Inlined in job handling |
| `delete_jobs` | (inline) | Inlined in job cleanup |
| `close_fd` | `closeFd` | |
| OS typeclass | `class OS` | All operations defined in typeclass |
| `printable_shell_env` | — | ❌ Not translated |
| `ps1` | `osSetPs1` | In OS typeclass |
| `out_of_fuel` | — | ❌ Not translated (Lean uses `maxSteps` in Main) |
| `string_of_fuel` | — | ❌ Not translated |
| `entry_unspecified` | — | ❌ Not translated |
| `entry_undefined` | — | ❌ Not translated |
| `try_entry_step` | — | ❌ Not translated |
| `in_unspecified_state` | — | ❌ Not translated |
| `in_undefined_state` | — | ❌ Not translated |
| `extract_unspec` | — | ❌ Not translated |
| `extract_trace` | — | ❌ Not translated |
| `show_changed_jobs` | — | ❌ Not translated (async job notification) |

### `os_symbolic.lem` → `Smoosh/OsSymbolic.lean`

| OCaml (Lem) | Lean | Notes |
|---|---|---|
| `symbolic_fs_dotdot` | (inline) | Implemented inline in `symbolicFsResolveComps` |
| `symbolic_fs_subdir` | `symbolicFsSubdir` | |
| `symbolic_fs_resolve_comps` | `symbolicFsResolveComps` | |
| `symbolic_fs_resolve_path` | `symbolicFsResolvePath` | |
| `symbolic_fs_resolve_dir` | `symbolicFsResolveNode` | Returns `Option SymbolicFs` |
| `symbolic_fs_write` | `symbolicFsWrite` | |
| `fs_empty` | (inline) | Inlined in `defaultSymbolic` |
| `symbolic_empty` | `defaultSymbolic` | |
| `os_empty` | (inline) | Inlined in initialization |
| `no_signals` | `noSignals` | |
| `proc_exit_status` | `procExitStatus` | |
| `proc_alive` | `procAlive` | |
| `proc_stepped` | (inline) | Checked inline in `osWaitpid` |
| `proc_stmt` | (inline) | Accessed via pattern matching |
| `proc_set_ec` | `procSetEc` | |
| `proc_set_stmt` | (inline) | Inlined in process update |
| `proc_save_state` | `procSaveState` | |
| `proc_select` | (inline) | Inlined in `osWaitpid` |
| `symbolic_clear_stepped` | (inline) | Done in `stepWorld`/tick logic |
| `symbolic_resolve_fd` | `symbolicResolveFd` | |
| `read_fifo` | `readAllFifo` | |
| `read_char_fifo` | `readCharFifo` | |
| `write_fifo` | (inline) | Inlined in `symbolicWriteFd` |
| `mkfifo` | (inline) | Inlined in pipe creation |
| `read_all_fifo` | `readAllFifo` | |
| `symbolic_fresh_fd` | `symbolicFreshFd` | |
| `symbolic_fds_reads_fifo` | `symbolicFdsReadsFifo` | |
| `symbolic_fds_writes_fifo` | `symbolicFdsWritesFifo` | |
| `step_world` | `stepWorld` | |
| `symbolic_write_fd` | `symbolicWriteFd` | With SIGPIPE logic |
| `symbolic_has_reader` | `symbolicHasReader` | |
| `symbolic_find_writer` | `symbolicFindWriter` | |
| `symbolic_writes_fifo` | `symbolicWritesFifo` | |
| `string_read_line_cl` | `stringReadLineCl` | |
| `string_read_line` | `stringReadLine` | |
| `symbolic_step_pid` | `osWaitpid` | In instance `OS Symbolic` |
| `symbolic_signal_pid` | `osSignalPid` | In instance `OS Symbolic` |
| `symbolic_file_type` | `osFileType` | In instance |
| `symbolic_file_type_follow` | `osFileTypeFollow` | In instance |
| `os_init` | `osInit` | In instance |
| `os_pipe` | `osPipe` | In instance — FD computation fixed |
| `os_fork_and_subshell` | `osForkAndSubshell` | In instance |
| `os_execve` | `osExecve` | In instance — returns `os` (no-op) |
| `os_read_line_fd` | `osReadLineFd` | In instance — fully implemented |
| `os_readdir` | `osReaddir` | In instance — fully implemented |
| `os_chdir` | `osChdir` | In instance — with directory check |
| `set_pwdir` | (inline) | Inlined in `osChdir` |
| `get_stdout` | `getSymbolicStdout` | In Main.lean |
| `get_stderr` | `getSymbolicStderr` | In Main.lean |
| `symbolic_set_param` | (inline) | Uses `internalSetParam` |
| `proc_receive_signal` | — | ❌ Partially implemented within `osSignalPid` |
| `blocking_read_all_fd` | `blockingReadAllFd` | |
| `count_open_fifo` | `countOpenFifo` | |

### `semantics.lem` → `Smoosh/Semantics.lean`

| OCaml (Lem) | Lean | Notes |
|---|---|---|
| `expand_param` | `expandParam` | |
| `expand_control` | `expandControl` | |
| `expand_words` | `expandWords` | |
| `step_expansion` | `stepExpansion` | |
| `step_redir` | `stepRedir` | |
| `step_redir_state` | (merged) | Merged into `stepRedir` |
| `internal_check_traps` | `internalCheckTraps` | |
| `check_traps` | `checkTraps` | |
| `expansion_error` | `expansionError` | |
| `step_eval` | `stepEval` | Core evaluation step |
| `full_evaluation` | `fullEvaluation` | In Main.lean |
| `eval` | `runToCompletion` | In Main.lean |
| `try_match_substring` | `tryMatchSubstring` | Substring pattern matching |
| `enter_loop` / `exit_loop` | `enterLoop` / `exitLoop` | Loop depth tracking |
| `parseTrapWord` | `parseTrapWord` | ✨ Lean-only trap string parsing |
| `parseTrapSimpleCmd` | `parseTrapSimpleCmd` | ✨ Lean-only |
| `parseTrapString` | `parseTrapString` | ✨ Lean-only |
| `isAssignment` | `isAssignment` | ✨ Lean-only assignment detection |
| `symbolic_run_full_expansion` | — | ❌ Not translated |
| `symbolic_full_expansion` | — | ❌ Not translated |
| `try_step_pid` | — | ❌ Not translated |
| `try_step_all_loop` | — | ❌ Not translated |
| `try_step_all` | — | ❌ Not translated |
| `run_trace_evaluation_loop` | — | ❌ Not translated |
| `run_trace_evaluation` | — | ❌ Not translated |
| `symbolic_full_evaluation` | — | ❌ Not translated (used by OCaml test runner) |
| `real_eval` | — | ❌ Not translated (concrete OS evaluation) |
| `real_eval_for_exit_code` | — | ❌ Not translated |

### `command.lem` → `Smoosh/Command.lean`

| OCaml (Lem) | Lean | Notes |
|---|---|---|
| `run_command` | `runCommand` | |
| `is_special_builtin` | `isSpecialBuiltin` | |
| `is_builtin` | `isBuiltin` | |
| `builtin_names` | `builtinNames` | |
| `is_unspecified_utility` | — | ❌ Not translated |
| `command_path_ok` | (inline) | Check inlined in `resolveCommandName` |
| `resolve_path_with` | `resolvePathWith` | |
| `resolve_command_name_in_path` | `resolveCommandNameInPath` | |
| `resolve_command_name` | `resolveCommandName` | |
| `check_execve` | → `runCommand` | Inlined in command dispatch |
| `early_hash` | → `runCommand` | Inlined in command dispatch |
| `strip_double_dash` | `stripDoubleDash` | |
| `getopt` | — | ❌ Not translated |
| `getopts` | `getOpts` | |
| `builtin_colon` | `builtinColon` | |
| `builtin_true` | `builtinTrue` | |
| `builtin_false` | `builtinFalse` | |
| `builtin_break` | `builtinBreak` | |
| `builtin_continue` | `builtinContinue` | |
| `builtin_exit` | `builtinExit` | |
| `builtin_return` | `builtinReturn` | |
| `builtin_shift` | `builtinShift` | |
| `unset_var` | (inline) | Inlined in `builtinUnset` |
| `unset_fun` | `unsetFunction` | |
| `unset_mode` | (inline) | Inlined in `builtinUnset` |
| `unset_all` | (inline) | Inlined in `builtinUnset` |
| `builtin_unset` | `builtinUnset` | |
| `builtin_export` | `builtinExport` | |
| `builtin_readonly` | `builtinReadonly` | |
| `add_locals` | (inline) | Inlined in `builtinLocal` |
| `builtin_local` | `builtinLocal` | |
| `builtin_times` | `builtinTimes` | |
| `builtin_eval` | `builtinEval` | |
| `builtin_source` / `builtin_dot` | `builtinDot` | |
| `builtin_exec` | `builtinExec` | |
| `builtin_set` | `builtinSet` | |
| `builtin_trap` | `builtinTrap` | |
| `trap_parse_signal` | (inline) | Inlined in `builtinTrap` |
| `trap_parse_signals` | (inline) | Inlined in `builtinTrap` |
| `trap_handle_signal` | (inline) | Inlined in `builtinTrap` |
| `show_varlist` | `showVarlist'` | |
| `update_varlist` | `updateVarlist` | |
| `log_null_argv_unspec` | — | ❌ Not translated |
| `special_builtins` | `specialBuiltinNames` | |
| `builtin_cd` | `builtinCd` | |
| `builtin_pwd` | `builtinPwd` | |
| `builtin_echo` | `builtinEcho` | |
| `builtin_test` | `builtinTest` | |
| `builtin_bracket` | (inline) | Handled in `builtinTest` |
| `builtin_type` | `builtinType` | |
| `builtin_umask` | `builtinUmask` | |
| `builtin_alias` | `builtinAlias` | |
| `builtin_unalias` | `builtinUnalias` | |
| `builtin_wait` | `builtinWait` | |
| `builtin_read` | `builtinRead` | |
| `builtin_printf` | `builtinPrintf` | |
| `builtin_getopts` | `builtinGetopts` | |
| `builtin_hash` | `builtinHash` | |
| `builtin_jobs` | `builtinJobs` | |
| `builtin_fg` | `builtinFg` | |
| `builtin_bg` | `builtinBg` | |
| `builtin_kill` | `builtinKill` | |
| `signal_pids` | (inline) | Inlined in `builtinKill` |
| `kill_signal_of_num` | (inline) | Inlined in `builtinKill` |
| `builtin_command` | `builtinCommand` | |
| `builtin_history` | `builtinHistory` | Non-POSIX extension |
| `builtin_help` | — | ❌ Not translated |
| `builtin_fc` | — | ❌ Not translated (command history editing) |
| `builtin_ulimit` | — | ❌ Not translated (XSI) |
| `set_getopt_longopt` | (inline) | Inlined in `builtinSet` |
| `set_getopt_shortopt` | (inline) | Inlined in `builtinSet` |
| `set_showopts` | (inline) | Inlined in `builtinSet` |
| `set_getopt` | (inline) | Inlined in `builtinSet` |
| `set_getopts` | (inline) | Inlined in `builtinSet` |
| `set_add_opt` | (inline) | Inlined in `builtinSet` |
| `sprintf_esc` | `printfProcessEscapes` | |
| `sprintf_format_b` | (inline) | Inlined in printf |
| `printf_format` | `printfGoFmt` | |
| `printf_loop` | `printfRepeat` | |
| `getopts_loop` | (inline) | Inlined in `builtinGetopts` |
| `send_sigcont` | (inline) | Inlined in `builtinFg`/`builtinBg` |
| — | `builtinMkdir` | ✨ Lean-only (symbolic fs helpers) |
| — | `builtinSleep` | ✨ Lean-only |
| — | `builtinTouch` | ✨ Lean-only |
| — | `builtinChmod` | ✨ Lean-only |
| — | `builtinLn` | ✨ Lean-only |
| — | `builtinRm` | ✨ Lean-only |
| — | `builtinCat` | ✨ Lean-only |
| — | `lookupSpecialBuiltin` | ✨ Lean-only dispatch map |
| — | `lookupRegularBuiltin` | ✨ Lean-only dispatch map |
| — | `isShellKeyword` | ✨ Lean-only |
| — | `nonBuiltinUtilities` | ✨ Lean-only |
| `current_job` | — | ❌ Not translated |
| `prev_job` | — | ❌ Not translated |
| `find_job` | — | ❌ Not translated |
| `job_cmd_cs` | — | ❌ Not translated |
| `job_of_symbolic_string` | — | ❌ Not translated |
| `pid_of_symbolic_string` | — | ❌ Not translated |
| `show_job_specs` | — | ❌ Not translated |
| `read_set_empty_vars` | — | ❌ Not translated (inlined in `builtinRead`) |
| `read_assign_vars` | — | ❌ Not translated (inlined in `builtinRead`) |
| `jobs_of_argv` | — | ❌ Not translated |

### `pattern.lem` → `Smoosh/Pattern.lean`

| OCaml (Lem) | Lean | Notes |
|---|---|---|
| `parse_bracket_terminator` | `parseBracketTerminator` | |
| `parse_bracket_class` | (inline) | Merged into `parseBracketTerminator` |
| `parse_bracket_char` | `parseBracketChar` | |
| `range_bc` | (inline) | Inlined in `matchEntry` |
| `parse_bracket_quoted_entries` | — | ❌ Not translated |
| `parse_bracket_entries` | `parseBracketEntries` | |
| `bracket_initial_literal` | `bracketInitialLiteral` | |
| `parse_bracket` | `parseBracket` | |
| `parse_quoted_pattern` | — | ❌ Not translated |
| `parse_pattern_char` | (inline) | Merged into `parsePatternLoop` |
| `parse_pattern_loop` | `parsePatternLoop` | |
| `parse_pattern` | `parsePattern` | |
| `match_entry` | `matchEntry` | |
| `match_exact_pattern` | `matchExactPattern` | |
| `match_exact` | `matchExact` | |
| `try_match_substring_loop` | (inline) | Replaced by `matchShortest`/`matchLongest` |
| `try_match_substring` | `matchShortest`, `matchLongest` | Split into two functions |
| `string_of_bracket_char` | `stringOfBracketChar` | |
| `string_of_bracket_entry` | `stringOfBracketEntry` | |
| `string_of_pattern_char` | `stringOfPatternChar` | |
| `string_of_pattern` | `stringOfPattern` | |

### `fields.lem` → `Smoosh/Fields.lean`

| OCaml (Lem) | Lean | Notes |
|---|---|---|
| `is_ws` | `isWs` | |
| `collect_non_ifs` | `collectNonIfs` | |
| `split_expstring` | `splitExpstring` | |
| `split_word` | `splitWord` | |
| `concat_expanded` | `concatExpanded` | |
| `skip_field_splitting` | `skipFieldSplitting` | |
| `combine_fields` | `combineFields` | |
| `clean_fields` | `cleanFields` | |
| `field_splitting` | `fieldSplitting` | |
| `needs_expansion` | `needsExpansion` | |
| `insert_field_separators` | `insertFieldSeparators` | |
| `pathname_expansion` | `pathnameExpansion` | |
| `remove_quotes` | `removeQuotes` | |
| `to_fields` | `toFields` | |
| `finalize_fields` | `finalizeFields` | |
| `quote_removal` | `quoteRemoval` | |
| `collapse_quoted` | — | ❌ Not translated |
| `split_fields` | — | ❌ Not translated (replaced by `combineFields`) |
| `debug_tmp_field` | — | ❌ Not translated (debug helper) |

### `path.lem` → `Smoosh/SmooshPath.lean`

| OCaml (Lem) | Lean | Notes |
|---|---|---|
| `split_on_slash` | `splitOnSlash` | |
| `has_leading_dot` | `hasLeadingDot` | |
| `has_trailing_slash` | `hasTrailingSlash` | |
| `parse_path_pattern` | `parsePathPattern` | |
| `match_pattern_file_list` | `matchPatternFileList` | |
| `match_dir` | `matchDir` | |
| `walk` | `walk` | |
| `match_path` | `matchPath` | |
| `match_path_symbolic` | — | ❌ Not translated |

### `arith.lem` → `Smoosh/Arith.lean`

| OCaml (Lem) | Lean | Notes |
|---|---|---|
| `lexer` | `lexer` | |
| `span` | `span'` | |
| `parse_assignment` | `parseAssignment` | |
| `parse_conditional` | `parseConditional` | |
| `parse_bool_or` | `parseBoolOr` | |
| `parse_bool_and` | `parseBoolAnd` | |
| `parse_bit_or` | `parseBitOr` | |
| `parse_bit_xor` | `parseBitXOr` | |
| `parse_bit_and` | `parseBitAnd` | |
| `parse_equality` | `parseEquality` | |
| `parse_relational` | `parseRelational` | |
| `parse_bit_shift` | `parseBitShift` | |
| `parse_additive` | `parseAdditive` | |
| `parse_multiplicative` | `parseMultiplicative` | |
| `unary_term` | `parseUnary` | |
| `number_term` | `parsePrimary` | |
| `parse_arith_exp` | `parseArith` | |
| `eval_arith` | `evalArith` | |
| `arith` | — | ❌ Not translated (top-level wrapper with bounded ints) |
| `arith64` | — | ❌ Not translated |
| `symbolic_arith_big_num` | — | ❌ Not translated |
| `symbolic_arith32` | — | ❌ Not translated |
| `symbolic_arith64` | — | ❌ Not translated |

### `test.lem` → `Smoosh/Test.lean`

| OCaml (Lem) | Lean | Notes |
|---|---|---|
| `parse_test_expr_disjunction` | `parseTestExprDisjunction` | |
| `parse_test_expr_conjunction` | `parseTestExprConjunction` | |
| `parse_test_expr_negation` | `parseTestExprNegation` | |
| `parse_test_expr_equality` | `parseTestExprEquality` | |
| `parse_test_expr_unary` | `parseTestExprUnary` | |
| `parse_test_expr` | `parseTestExpr` | |
| `eval_test_expr` | `evalTestExpr` | |
| `read_two_nats` | `readTwoNats` | |
| `string_of_test_expr` | `stringOfTestExpr` | |

### `smoosh.lem` → `Main.lean` / `Smoosh/FromJson.lean`

| OCaml (Lem) | Lean | Notes |
|---|---|---|
| `eval` | `runToCompletion` | Main.lean |
| `full_evaluation` | `fullEvaluation` | Main.lean |
| — | `runTestFromJson` | ✨ Lean-only (JSON-based test runner) |
| — | `getSymbolicStdout` | ✨ Lean-only |
| — | `getSymbolicStderr` | ✨ Lean-only |
| JSON AST parsing | `FromJson.lean` | ✨ Lean-only module |

### Not Translated: `os_system.lem`

The file `os_system.lem` (461 lines) implements the concrete/system OS layer (real file I/O, process forking via Unix syscalls). This is **intentionally not translated** — the Lean implementation is purely symbolic.

---

## Translation Gaps Summary

### Intentionally Not Translated

| Component | Reason |
|---|---|
| `os_system.lem` (461 lines) | Concrete OS layer — Lean uses symbolic mode only |
| `real_eval` / `real_eval_for_exit_code` | Concrete evaluation — not needed for symbolic testing |
| `signal_of_ocaml_signal` / `signal_of_platform_int` | OCaml-specific signal integer mapping |
| 32/64-bit integer parsing (`readInt32`, `readInt64`, `write32`, `write64`) | Lean uses unbounded integers |
| `arith` / `arith64` / `symbolic_arith*` | Bounded arithmetic wrappers — Lean uses unbounded |
| Debug/tracing helpers (`debug_tmp_field`, `printable_shell_env`) | Not needed for test execution |
| `out_of_fuel` / `string_of_fuel` | OCaml step-limit — Lean uses `maxSteps` in Main |
| `entry_unspecified` / `entry_undefined` / `in_unspecified_state` | Unspecified behavior tracking |
| `extract_unspec` / `extract_trace` | Log extraction — not needed for tests |
| `show_changed_jobs` | Async job notification — not needed for symbolic |
| `builtin_help` | Help text display |
| `builtin_fc` | Command history editing (fc builtin) |
| `builtin_ulimit` | Resource limits (XSI extension) |
| `is_unspecified_utility` | Unspecified utility detection |
| `log_null_argv_unspec` | Unspecified behavior logging |
| `ran_command_substitution` | Debug helper |
| `sort` / `compare_by_first` | Lean uses native ordering |

### Partially Translated (functional but simplified)

| Component | Gap |
|---|---|
| `osExecve` | Returns `os` unchanged (no-op); OCaml also returns `Left "unimplemented"` in symbolic mode |
| `proc_receive_signal` | Signal handling within `osSignalPid` is simplified |
| `parse_bracket_quoted_entries` | Double-quote handling inside bracket expressions not translated |
| `parse_quoted_pattern` | Quoted pattern parsing inside bracket context not translated |
| `EvalLoop` | Runtime parsing (`eval` builtin) uses simplified trap-style parser — not full shell parser |
| Job control helpers (`current_job`, `prev_job`, `find_job`) | Job spec parsing (`%N`) not translated |
| `builtinRead` | `read_set_empty_vars`/`read_assign_vars` inlined and simplified |

### Lean-Only Additions

The Lean implementation adds several builtins not present in the OCaml version to support symbolic filesystem operations:
- `builtinTouch`, `builtinMkdir`, `builtinChmod`, `builtinLn`, `builtinRm`, `builtinCat`, `builtinSleep`
- `lookupSpecialBuiltin`, `lookupRegularBuiltin` — dispatch maps for builtin resolution
- `isShellKeyword`, `nonBuiltinUtilities`, `nonBuiltinSpecialUtilities` — classification helpers
- `parseTrapWord`, `parseTrapSimpleCmd`, `parseTrapString` — simplified trap command parsing
- `isAssignment` — assignment detection for simple commands
- `FromJson.lean` — JSON test case parser
- `Main.lean` — test runner with stdout/stderr extraction

---

## Architecture

```
                    ┌─────────────┐
                    │  Main.lean  │  Test runner entry point
                    │ (JSON→AST)  │  Reads .json, runs symbolic eval
                    └──────┬──────┘
                           │
                    ┌──────▼──────┐
                    │ Semantics   │  Core step evaluator
                    │ (stepEval)  │  Stmt reduction loop
                    └──┬───┬──┬──┘
                       │   │  │
              ┌────────┘   │  └────────┐
              ▼            ▼           ▼
        ┌──────────┐ ┌──────────┐ ┌──────────┐
        │ Command  │ │ Fields   │ │ Pattern  │
        │ Builtins │ │ Splitting│ │ Matching │
        │ Dispatch │ │ Expansion│ │ Globbing │
        └────┬─────┘ └──────────┘ └────┬─────┘
             │                         │
             └─────────┬───────────────┘
                       ▼
                ┌──────────────┐
                │  Os.lean     │  OS typeclass + helpers
                │  (class OS)  │  Redirection, pipes, etc.
                └──────┬───────┘
                       │
                ┌──────▼───────┐
                │ OsSymbolic   │  Symbolic OS implementation
                │ (instance)   │  FIFOs, processes, FS
                └──────────────┘
```
