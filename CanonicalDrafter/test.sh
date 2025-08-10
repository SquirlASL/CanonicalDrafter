#!/bin/bash

# Define the paths
TEST_DIR="Test"
EXPECTED_DIR="Test"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "Building Dependencies"
lake exe cache get
lake build Mathlib

TOOLCHAIN_DIR=$(lean --print-prefix)
TARGET_DIR=".lake/packages/lean4"

mkdir -p "$TARGET_DIR"
cp -r "$TOOLCHAIN_DIR"/* "$TARGET_DIR"

if [ $? -ne 0 ]; then
    echo -e "${RED}Build failed!${NC}"
    exit 1
fi

echo -e "${YELLOW}Running ExtractData tests...${NC}"

# Track test results
passed=0
failed=0

# Iterate over each .lean file in the Test directory
for leanfile in $TEST_DIR/*.lean; do
    # Extract the base filename without the extension
    base=$(basename "$leanfile" .lean)
    
    # Skip if not a test file
    if [[ ! -f "$leanfile" ]]; then
        continue
    fi

    echo -n "Testing $base: "
    
    # Define the path for the expected output file
    expectedfile="$EXPECTED_DIR/$base.ast.json"
    
    # Define the path where ExtractData actually outputs the file
    producedfile=".lake/build/ir/Test/$base.ast.json"

    # Run ExtractData (output goes to .lake/build/ir/Test/)
    lake env lean --run ExtractData.lean "$leanfile" > /dev/null 2>&1
    
    if [ $? -ne 0 ]; then
        echo -e "${RED}FAILED (execution error)${NC}"
        echo "ExtractData failed to process $leanfile"
        ((failed++))
        continue
    fi

    # Check if the produced file was actually created
    if [[ ! -f "$producedfile" ]]; then
        echo -e "${RED}FAILED (no output file generated)${NC}"
        echo "Expected output at: $producedfile"
        ((failed++))
        continue
    fi

    # Check if expected output file exists
    if [[ ! -f $expectedfile ]]; then
        echo -e "${YELLOW}SKIPPED (no expected output file)${NC}"
        echo "Generated output available at: $producedfile"
        echo "Copy to: $expectedfile"
        continue
    fi

    # Compare the output with the expected output
    if diff "$producedfile" "$expectedfile" > /dev/null 2>&1; then
        echo -e "${GREEN}PASSED${NC}"
        ((passed++))
    else
        echo -e "${RED}FAILED${NC}"
        echo "Differences found:"
        diff "$producedfile" "$expectedfile"
        # Save the produced output for inspection
        mv "$producedfile" "$EXPECTED_DIR/$base.produced.json"
        echo "Produced output saved to: $EXPECTED_DIR/$base.produced.json"
        ((failed++))
    fi
done

# Print summary
echo
echo "Test Summary:"
echo -e "  ${GREEN}Passed: $passed${NC}"
echo -e "  ${RED}Failed: $failed${NC}"
echo -e "  Total:  $((passed + failed))"

# Exit with error code if any tests failed
if [ $failed -gt 0 ]; then
    echo
    echo -e "${RED}Some tests failed!${NC}"
    exit 1
else
    echo
    echo -e "${GREEN}All tests passed!${NC}"
    exit 0
fi
