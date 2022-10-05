#!/bin/bash

function estimate_info() {
    WHOLE_NAME="$1"
    DIR_NAME=$(dirname "$1")
    MEAN=$(jq '.Mean.point_estimate' $WHOLE_NAME | awk '{printf "%.2f", $1;}')
    echo "$DIR_NAME $MEAN"
    }

export -f estimate_info

find . -type f -name "estimates.json" -exec bash -c "estimate_info \"{}\"" \;
