#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_DIR="${ROOT_DIR}/docs"

mkdir -p "${OUT_DIR}"

cd "${ROOT_DIR}"

N="${N:-64}"
STEP="${STEP:-0.35}"
PITCH="${PITCH:-0.15}"
OUT="${OUT:-${OUT_DIR}/spiral_points.json}"

lake exe modal_thesis_spiral_dump -- --n "${N}" --step "${STEP}" --pitch "${PITCH}" > "${OUT}"
echo "Wrote ${OUT}"
