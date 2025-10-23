#!/usr/bin/env bash

successes=0
failures=0

while IFS= read -r file; do
    output=$(lean "$file" 2>&1)
    status=$?
    if [ $status -ne 0 ]; then
        echo "=== Failed: $file"
        echo "$output"
        ((failures++))
    else
        echo "=== Succeeded: $file"
        ((successes++))
    fi
done < <(find _out/extracted-examples -name '*lean')

echo
echo "Summary:"
echo "  Succeeded: $successes"
echo "  Failed:    $failures"

if [ $failures -ne 0 ]; then
    exit 1
else
    exit 0
fi
