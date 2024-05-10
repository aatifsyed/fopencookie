#!/usr/bin/env bash

(cd cstream && cargo rdme)
(cd sys && cargo rdme)
cargo rdme
RUSTDOCFLAGS="--cfg do_doc_cfg" cargo +nightly doc --all-features
cargo build-all-features
