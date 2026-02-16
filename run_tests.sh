#!/usr/bin/env bash
# run_tests.sh — Test runner for lean-smoosh
#
# Runs each JSON test case through the symbolic shell and compares output
# against expected .out, .ec, and .err files.
#
# Usage:
#   bash run_tests.sh              # Run all tests
#   bash run_tests.sh --verbose    # Show details for failures
#   bash run_tests.sh --filter PAT # Run only tests matching PAT

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BIN="$SCRIPT_DIR/.lake/build/bin/smoosh-test"
JSON_DIR="$SCRIPT_DIR/tests/shell_json"
TEST_DIR="$SCRIPT_DIR/tests/shell"
TIMEOUT_SEC=5

# Parse flags
VERBOSE=false
FILTER=""
for arg in "$@"; do
  case "$arg" in
    --verbose|-v) VERBOSE=true ;;
    --filter=*)   FILTER="${arg#--filter=}" ;;
    --filter)     shift; FILTER="$1" ;;
  esac
done

# Build if needed
if [ ! -f "$BIN" ]; then
  echo "Building smoosh-test..."
  (cd "$SCRIPT_DIR" && lake build smoosh-test)
fi

# Skip lists — tests requiring runtime parsing (eval) or async signal delivery
SKIP_EVAL="builtin.eval builtin.eval.break builtin.eval.trap semantics.eval.makeadder semantics.traps.async semantics.traps.inherit"

is_skipped() {
  local name="$1"
  for s in $SKIP_EVAL; do
    [ "$name" = "$s" ] && return 0
  done
  return 1
}

# Counters
pass=0 fail=0 skip=0 timeout_count=0 total=0
failed_tests=""

for f in "$JSON_DIR"/*.json; do
  bn=$(basename "$f" .json)

  # Apply filter
  if [ -n "$FILTER" ] && [[ "$bn" != *"$FILTER"* ]]; then
    continue
  fi

  total=$((total + 1))

  # Skip eval/async tests
  if is_skipped "$bn"; then
    skip=$((skip + 1))
    continue
  fi

  # Run with timeout — capture exit code properly
  set +e
  got_out=$(timeout "$TIMEOUT_SEC" "$BIN" "$f" 2>/tmp/smoosh_test_stderr.txt)
  got_ec=$?
  set -e
  got_err=$(cat /tmp/smoosh_test_stderr.txt 2>/dev/null || true)

  # Handle timeout
  if [ "$got_ec" -eq 124 ]; then
    timeout_count=$((timeout_count + 1))
    failed_tests="$failed_tests $bn(timeout)"
    $VERBOSE && echo "TIMEOUT: $bn"
    continue
  fi

  # Load expected values
  exp_out="" ; exp_ec=0 ; exp_err="" ; has_expected=0 ; has_exp_err=0
  [ -f "$TEST_DIR/$bn.out" ] && { exp_out=$(cat "$TEST_DIR/$bn.out"); has_expected=1; }
  [ -f "$TEST_DIR/$bn.ec" ]  && { exp_ec=$(cat "$TEST_DIR/$bn.ec" | tr -d '[:space:]'); has_expected=1; }
  [ -f "$TEST_DIR/$bn.err" ] && { exp_err=$(cat "$TEST_DIR/$bn.err"); has_expected=1; has_exp_err=1; }

  # Compare
  if [ "$has_expected" -eq 0 ]; then
    # No .out/.ec/.err file: pass if ec=0 and stdout is empty
    if [ "$got_ec" -eq 0 ] && [ -z "$got_out" ]; then
      pass=$((pass + 1))
    else
      fail=$((fail + 1))
      failed_tests="$failed_tests $bn"
      $VERBOSE && echo "FAIL: $bn (no expected files; got ec=$got_ec, stdout='$(echo "$got_out" | head -1)')"
    fi
  else
    out_match=true ; ec_match=true ; err_match=true
    [ "$got_out" != "$exp_out" ] && out_match=false
    [ "$got_ec" != "$exp_ec" ]   && ec_match=false
    [ "$has_exp_err" -eq 1 ] && [ "$got_err" != "$exp_err" ] && err_match=false

    if $out_match && $ec_match && $err_match; then
      pass=$((pass + 1))
    else
      fail=$((fail + 1))
      failed_tests="$failed_tests $bn"
      if $VERBOSE; then
        echo "FAIL: $bn"
        $out_match || echo "  stdout diff (expected ${#exp_out} chars, got ${#got_out} chars)"
        $ec_match  || echo "  ec expected=$exp_ec got=$got_ec"
        $err_match || echo "  stderr diff (expected ${#exp_err} chars, got ${#got_err} chars)"
      fi
    fi
  fi
done

# Summary
echo ""
echo "=========================================="
echo "  Results: $pass passed, $fail failed, $skip skipped, $timeout_count timeouts"
echo "  Total:   $total tests ($((pass + fail + skip + timeout_count)) executed)"
echo "  Pass rate: $(( pass * 100 / (pass + fail + timeout_count) ))%"
echo "=========================================="

if [ -n "$failed_tests" ]; then
  echo ""
  echo "Failed tests:$failed_tests"
fi

# Cleanup
rm -f /tmp/smoosh_test_stderr.txt

# Exit code
[ "$fail" -eq 0 ] && [ "$timeout_count" -eq 0 ]
