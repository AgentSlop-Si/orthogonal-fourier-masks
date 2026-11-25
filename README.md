# Paper 2: Degree Classification, Block Rigidity, and Labeled Enumeration for Orthogonal Binary Fourier Masks

## Files
- `main.tex` — Submission-ready `amsart` LaTeX manuscript.
- `references.bib` — Clean BibTeX bibliography.
- `verify_fourier_masks.py` — Standalone Python 3 (stdlib only) verifier checking divisor-block masks, CRT & cross-character identities, exact labeled count formula at `N=6, 10, 15`, exhaustive arbitrary-mask backtracking at `N=6` (`d=2,3`) and `N=10` (`d=5`), the `N=m q^b` local block iff at `N=18`, and exhaustive absence of `4x4` one-hole weight-3 blocks for `N <= 18`.

## How to Compile PDF
1. Upload `main.tex` and `references.bib` to Overleaf (or compile locally with `latexmk -pdf main.tex`).
2. Edit `\author`, `\email`, and `\address` at the top of `main.tex` if desired.

## Suggested Submission Metadata
- **arXiv primary / secondary:** `math.CO` (Combinatorics) / `math.NT` (Number Theory), `math.CA` (Classical Analysis)
- **MSC 2020:** Primary `05B20`, `15B10`; Secondary `11R18`, `42A99`, `15A60`
- **Target journals (zero-fee):** *Linear Algebra and its Applications*, *Discrete Mathematics*, *INTEGERS*.

## Verify Computations
```bash
python3 verify_fourier_masks.py
```
