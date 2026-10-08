# A perturbation of the seven-eighths zero-free half-plane

`paper.tex` presents a proposed deduction of a zero-free region
`Re(s) > 0.874995` from the analytic estimates in OpenAI's
[seven-eighths manuscript](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex).

Run `uv run verify_bounds.py` to check the rational margins. The Mathlib files
`BoundsReal.lean`, `EndpointCertificate.lean`, `ReflectedExponent.lean`, and
`LowGramScale.lean` prove the geometry, endpoint, reflected-exponent, and
perturbed Gram-scale inequalities for real
parameters. The project pins Lean 4.34.1 and the Mathlib revision used by the
upstream seven-eighths formalization. Run `lake exe cache get` and `lake build`
from this directory. A Docker environment is also available:

```sh
docker run --rm --cpuset-cpus 0-3 --cpus 4 --memory 8g \
  --entrypoint /bin/bash \
  --mount "type=bind,src=$PWD,dst=/home/lean/project" \
  --mount type=volume,src=rh-lean-toolchains,dst=/home/lean/.elan/toolchains \
  --workdir /home/lean/project \
  ghcr.io/leanprover-community/mathlib4/lean:latest \
  -lc 'lake exe cache get && lake build'
```

The `OAILow*.lean` files connect the perturbed reflected exponent to the
upstream OAI normalized sector-energy theorem. Check them with
`uv run verify_oai.py OAILowSector` from this directory. This requires the
adjacent `rh-upstream` checkout and Docker. The physical low-probe bound and
zero-free theorem remain unproved.

Run
`pdflatex -interaction=nonstopmode -halt-on-error paper.tex` twice to build
the PDF and resolve references.

These checks verify the numerical part of the proposed argument and the
document build. They do not certify the cited number-theoretic estimates or
the extension of their contour arguments. The proposed stronger theorem is
not formalized. See [FORMALIZATION.md](FORMALIZATION.md) for the remaining
proof obligations.
