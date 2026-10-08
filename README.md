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
ordered principal double shift, uniform contour tails, principal
triple-contour transport, selected high-row local bounds, and row-dependent
tuple, dyad, and Mellin-integral bounds. Check them with
`uv run verify_oai.py OAIHighAudit`. The conditional central-bin dyadic
bound, changed floor-row bound, canonical ray-cube decomposition, principal
transport, and detector assembly are also formalized.
`OAIHighAssemblyFinal.lean` proves the stronger Hecke, Dirichlet, and zeta
zero-free statements from an explicit `ChosenPerturbedMomentInput` and the
prior bound `beta ≤ 7/8`. It also provides versions using the stronger
`RawPerturbedMomentInput`. Fine slot data can be selected for any positive
moment mesh. The changed fourth-moment input has not been proved.
The certified energy band and its field bounds at `κ=3/4` are formalized.
Their transport to the perturbed source moments remains open.

Run
`pdflatex -interaction=nonstopmode -halt-on-error paper.tex` twice to build
the PDF and resolve references.

These checks verify the conditional high-side detector argument and the
document build. They do not certify an unconditional stronger theorem.
See [FORMALIZATION.md](FORMALIZATION.md) for the remaining proof obligation.
