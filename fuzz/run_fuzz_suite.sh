#!/usr/bin/env bash
#
# run_fuzz_suite.sh — Sequentially execute all fuzz targets in the suite.
#
# Defaults to a short sanity-check run per target (15 seconds) to verify 
# correctness and lack of regression. Can be customized via options.

set -euo pipefail

# ANSI color codes
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Default values
DURATION=15
ADDITIONAL_ARGS=()

show_help() {
    cat << EOF
Usage: $0 [OPTIONS] [-- [LIBFUZZER_ARGS]]

Runs all fuzz targets in the EML fuzz suite sequentially.

Options:
  -d, --duration <seconds>   Maximum time in seconds to run each target (default: $DURATION).
                             Set to 0 to run indefinitely (manual interruption required).
  -h, --help                 Show this help message.

Examples:
  $0 -d 30                   Run each target for 30 seconds.
  $0 -- -runs=1000           Run each target for 1000 iterations.
EOF
}

# Parse command line options
while [[ $# -gt 0 ]]; do
    case "$1" in
        -d|--duration)
            DURATION="$2"
            shift 2
            ;;
        -h|--help)
            show_help
            exit 0
            ;;
        --)
            shift
            ADDITIONAL_ARGS=("$@")
            break
            ;;
        *)
            echo -e "${RED}Error: Unknown option $1${NC}" >&2
            show_help >&2
            exit 1
            ;;
    esac
done

# Locate workspace root and navigate to fuzz directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" &>/dev/null && pwd)"
cd "$SCRIPT_DIR"

# Ensure cargo-fuzz is available
if ! command -v cargo-fuzz &> /dev/null; then
    echo -e "${RED}Error: 'cargo-fuzz' is not installed or not in PATH.${NC}" >&2
    echo -e "Install it using: ${YELLOW}cargo install cargo-fuzz${NC}" >&2
    exit 1
fi

# Find all targets
TARGETS=()
for file in fuzz_targets/*.rs; do
    if [[ -f "$file" ]]; then
        basename=$(basename "$file" .rs)
        TARGETS+=("$basename")
    fi
done

if [[ ${#TARGETS[@]} -eq 0 ]]; then
    echo -e "${RED}Error: No fuzz targets found in fuzz_targets/${NC}" >&2
    exit 1
fi

echo -e "${BLUE}======================================================================${NC}"
echo -e "${BLUE}                  EML Asynchronous Fuzz Suite                         ${NC}"
echo -e "${BLUE}======================================================================${NC}"
echo -e "Found ${#TARGETS[@]} fuzz target(s): ${TARGETS[*]}"
if [[ "$DURATION" -gt 0 ]]; then
    echo -e "Each target will run for up to ${YELLOW}${DURATION} seconds${NC}."
else
    echo -e "Each target will run ${YELLOW}indefinitely${NC} (Ctrl+C to stop/next)."
fi
if [[ ${#ADDITIONAL_ARGS[@]} -gt 0 ]]; then
    echo -e "Extra arguments: ${ADDITIONAL_ARGS[*]}"
fi
echo -e "${BLUE}----------------------------------------------------------------------${NC}"

FAILED_TARGETS=()
SUCCESS_TARGETS=()

for target in "${TARGETS[@]}"; do
    echo -e "\n${BLUE}[*] Running target:${NC} ${YELLOW}${target}${NC}..."
    
    # Assemble fuzz command
    # If duration is specified, add -max_total_time parameter to libFuzzer
    cmd=(cargo fuzz run "$target")
    if [[ "$DURATION" -gt 0 ]]; then
        cmd+=("--" "-max_total_time=${DURATION}")
    else
        cmd+=("--")
    fi
    
    # Append any user additional arguments
    cmd+=("${ADDITIONAL_ARGS[@]}")
    
    # Execute the fuzz target
    if "${cmd[@]}"; then
        echo -e "${GREEN}[+] Target ${target} completed successfully without crashes.${NC}"
        SUCCESS_TARGETS+=("$target")
    else
        echo -e "${RED}[-] Target ${target} failed or encountered a crash!${NC}" >&2
        FAILED_TARGETS+=("$target")
    fi
done

echo -e "\n${BLUE}======================================================================${NC}"
echo -e "${BLUE}                            Fuzzing Summary                           ${NC}"
echo -e "${BLUE}======================================================================${NC}"
echo -e "Successful: ${GREEN}${#SUCCESS_TARGETS[@]} / ${#TARGETS[@]}${NC}"
if [[ ${#FAILED_TARGETS[@]} -gt 0 ]]; then
    echo -e "Failed:     ${RED}${#FAILED_TARGETS[@]} / ${#TARGETS[@]}${NC} (${FAILED_TARGETS[*]})"
    echo -e "${RED}Fuzz suite execution failed.${NC}"
    exit 1
else
    echo -e "${GREEN}Fuzz suite execution completed successfully! All targets clean.${NC}"
    exit 0
fi
