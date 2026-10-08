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

The `OAILow*.lean` files prove the normalized compensated low estimate for
the perturbed physical probe against upstream OAI. Check the full chain and
its axioms with `uv run verify_oai.py OAILowAudit`. This requires the
adjacent `rh-upstream` checkout and Docker. The `OAIHigh*.lean` files prove
the local Euler bounds and principal and global Euler product extensions at
the new boundary. They also prove source-multiplier analyticity, finite
complex-weight bounds, the `w` and `z` source contour shifts, and the
ordered principal double shift, uniform contour tails, and principal
triple-contour transport. Check them with
`uv run verify_oai.py OAIHighAudit`. The
row-dependent high-side contour estimates and zero-free theorem remain
unproved.

Run
`pdflatex -interaction=nonstopmode -halt-on-error paper.tex` twice to build
the PDF and resolve references.

These checks verify the stated partial results and the document build.
They do not certify the high-side contour arguments or the proposed stronger
theorem. See [FORMALIZATION.md](FORMALIZATION.md) for the remaining proof
obligations.
