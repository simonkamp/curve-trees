#!/bin/bash


function estimate_info() {
    WHOLE_NAME="$1"
    DIR_NAME=$(dirname "$1")
    MEAN=$(jq '.mean.point_estimate' "$WHOLE_NAME" | awk '{printf "%.2f", $1/1000000;}')

    # Division for batch
    if echo "$DIR_NAME" | grep -q "100"; then
        MEAN=$(echo "scale=2; $MEAN / 100" | bc)
    fi


    if echo "$DIR_NAME" | grep -q "base"; then
        FMTTED_DIR=$(echo -n "$DIR_NAME" | cut -d / -f 4-5)
        if echo "$DIR_NAME" | grep -q -i "$2"; then
            printf "%-80s %s\n" "${FMTTED_DIR}" "${MEAN}ms"
        fi
    fi
}

export -f estimate_info

function estimate_info_acc() {
    estimate_info "$1" "acc"
}
export -f estimate_info_acc

function estimate_info_selrand() {
    estimate_info "$1" "selrand"
}
export -f estimate_info_selrand

function estimate_info_pour() {
    estimate_info "$1" "pour"
}
export -f estimate_info_pour

# Main code

echo
echo

echo "--- Table 1 (Accumulator)----"
echo "- Proof sizes and constraints -"
grep -i acc proof_constraints.txt 
echo "- Timing -"
find . -type f -name "estimates.json" -exec bash -c "estimate_info_acc \"{}\"" \;
echo 

echo "--- Table 2 (SelectAndRerand)----"
echo "- Proof sizes and constraints -"
grep -i selrand proof_constraints.txt
echo "- Timing -"
find . -type f -name "estimates.json" -exec bash -c "estimate_info_selrand \"{}\"" \;
echo

echo "--- Table 3 (Pour)----"
echo "- Proof sizes and constraints -"
grep -i pour proof_constraints.txt
echo "- Timing -"
find . -type f -name "estimates.json" -exec bash -c "estimate_info_pour \"{}\"" \;
echo

