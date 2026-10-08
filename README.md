# A perturbation of the seven-eighths zero-free half-plane

`paper.tex` presents a proposed deduction of a zero-free region
`Re(s) > 0.874995` from the analytic estimates in OpenAI's
[seven-eighths manuscript](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex).

Run `uv run verify_bounds.py` to check the rational margins. The Mathlib files
`BoundsReal.lean`, `EndpointCertificate.lean`, and `ReflectedExponent.lean`
prove the geometry, endpoint, and reflected-exponent inequalities for real
parameters. They compile with Lean 4.27.0 and
Mathlib in `ghcr.io/ldct/mathlib4:v4.27.0`:

```sh
docker run --rm -v "$PWD:/project/rh:ro" --workdir /project ghcr.io/ldct/mathlib4:v4.27.0 bash -lc 'lake env lean rh/BoundsReal.lean'
docker run --rm -v "$PWD:/project/rh:ro" --workdir /project ghcr.io/ldct/mathlib4:v4.27.0 bash -lc 'lake env lean rh/EndpointCertificate.lean'
docker run --rm -v "$PWD:/project/rh:ro" --workdir /project ghcr.io/ldct/mathlib4:v4.27.0 bash -lc 'lake env lean rh/ReflectedExponent.lean'
```

Run
`pdflatex -interaction=nonstopmode -halt-on-error paper.tex` twice to build
the PDF and resolve references.

These checks verify the numerical part of the proposed argument and the
document build. They do not certify the cited number-theoretic estimates or
the extension of their contour arguments. The proposed stronger theorem is
not formalized. See [FORMALIZATION.md](FORMALIZATION.md) for the remaining
proof obligations.
