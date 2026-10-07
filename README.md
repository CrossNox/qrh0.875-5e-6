# A perturbation of the seven-eighths zero-free half-plane

`paper.tex` presents a proposed deduction of a zero-free region
`Re(s) > 0.874995` from the analytic estimates in OpenAI's
[seven-eighths manuscript](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex).

Run `uv run verify_bounds.py` to check the rational margins. `Bounds.lean`
checks the corresponding integer identities and two scaled linear bounds.
It compiles with Lean 4.10.0 using `lean Bounds.lean`. Run
`pdflatex -interaction=nonstopmode -halt-on-error paper.tex` twice to build
the PDF and resolve references.

These checks verify arithmetic and the document build. The Lean file does
not formalize the map from the manuscript's real parameters to its scaled
integers. It does not certify the cited number-theoretic estimates or the
extension of their contour arguments. The proposed stronger theorem is not
formalized.
