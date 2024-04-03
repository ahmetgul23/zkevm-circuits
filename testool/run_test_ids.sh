#!/bin/bash
set -x
cd /home/ubuntu/zkevm-circuits/testool
[ -f /home/ubuntu/tool/export ] && . /home/ubuntu/tool/export || :
export RUST_BACKTRACE=1
export RUST_LOG=debug

cargo run --features "parallel_syn scroll"  --release -- --suite nightly --circuits sc --test-ids test_ids.txt --report
