#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "${ROOT_DIR}"

python3 -m venv .venv >/dev/null 2>&1 || true
source .venv/bin/activate

python -m pip install -r requirements.txt

./scripts/gen_spiral_data.sh
python ./scripts/viz_spiral.py --in docs/spiral_points.json --out-dir docs
python ./scripts/umap_import_graph.py --out-dir docs
python ./scripts/tactic_graph.py --out-dir docs

echo "Artifacts written under docs/"
