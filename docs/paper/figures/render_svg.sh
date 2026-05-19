#!/usr/bin/env bash
set -euo pipefail

# Render TikZ figures to SVG for HTML output.
# Run from the project root inside nix-shell:
#   nix-shell --run 'cd docs/paper && bash figures/render_svg.sh'
#
# Requires standalone.cls (add 'standalone' to texlive.combine in shell.nix).

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PAPER_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
TMPDIR="$(mktemp -d)"
trap 'rm -rf "$TMPDIR"' EXIT

FIGURES=(
  fig-topology
  fig-projection
  fig-epoch-timeline
  fig-elision
  fig-complexity
)

for fig in "${FIGURES[@]}"; do
  printf "Rendering %s... " "$fig"

  cat > "$TMPDIR/$fig.tex" <<EOF
\\documentclass[tikz,border=4pt]{standalone}
\\usepackage{amsmath}
\\usepackage{amssymb}
\\usetikzlibrary{calc,decorations.pathreplacing,patterns}
\\definecolor{algA}{HTML}{2563EB}
\\definecolor{algB}{HTML}{D97706}
\\definecolor{nullc}{HTML}{9CA3AF}
\\usepackage{pgfplots}
\\pgfplotsset{compat=1.18}
\\setlength{\\columnwidth}{242pt}  % USENIX two-column width
\\begin{document}
\\input{$SCRIPT_DIR/$fig.tex}
\\end{document}
EOF

  # Compile from paper dir so relative paths (e.g. figures/data/*.csv) resolve.
  if ! (cd "$PAPER_DIR" && pdflatex -interaction=nonstopmode \
      -output-directory="$TMPDIR" "$TMPDIR/$fig.tex") > "$TMPDIR/$fig.stdout" 2>&1; then
    echo "FAILED (pdflatex)"
    tail -10 "$TMPDIR/$fig.stdout"
    exit 1
  fi

  # Convert to SVG with text as paths for maximum portability.
  dvisvgm --pdf "$TMPDIR/$fig.pdf" \
    --no-fonts --exact-bbox \
    -o "$SCRIPT_DIR/$fig.svg" > /dev/null 2>&1

  echo "ok → figures/$fig.svg"
done

echo "Done."
