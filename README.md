# The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\Re(s)>7/8-5\times10^{-6}$

`paper.tex` proves nonvanishing for `Re(s) > 174999/200000 = 0.874995`
for finite-order Hecke L-functions over `Q(sqrt(-3))` and Dirichlet
L-functions, including the Riemann zeta function, with the principal pole
allowed. It extends the analytic estimates in OpenAI's
[seven-eighths manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex).

`OAIHighUnconditional.lean` proves the final statements without an assumed
moment estimate or prior zero-free bound. It obtains the prior `beta ≤ 7/8`
theorem from upstream and proves the perturbed source moments through
`OAIHighMomentTransport.lean`. The theorem names are
`OAI.SevenEighths.PerturbedZeroFree.bound_zero_supremum`,
`prove_hecke_nonvanishing`, `prove_dirichlet_nonvanishing`, and
`prove_zeta_nonvanishing` in that namespace.

Run `uv run verify_bounds.py` to check the rational margins. The Mathlib files
`BoundsReal.lean`, `EndpointCertificate.lean`, `ReflectedExponent.lean`, and
`LowGramScale.lean` prove the geometry, endpoint, reflected-exponent, and
perturbed Gram-scale inequalities for real
parameters. The project pins Lean 4.34.1 and the Mathlib revision used by the
upstream seven-eighths formalization. Run `lake exe cache get` and `lake build`
from this directory to check these four arithmetic modules. A Docker
environment is also available:

```sh
docker run --rm --cpuset-cpus 0-3 --cpus 4 --memory 8g \
  --entrypoint /bin/bash \
  --mount "type=bind,src=$PWD,dst=/home/lean/project" \
  --mount type=volume,src=rh-lean-toolchains,dst=/home/lean/.elan/toolchains \
  --workdir /home/lean/project \
  ghcr.io/leanprover-community/mathlib4/lean:latest \
  -lc 'lake exe cache get && lake build'
```

For the full proof, use an adjacent `rh-upstream` checkout of
`https://github.com/openai/math` at revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, with its Lean dependencies
installed. The verification script requires Docker and uses the toolchain
volume shown above.

```sh
uv run verify_oai.py OAIHighAudit
```

This builds the required upstream imports, recompiles every local dependency
in import order, and prints the final theorem types and their axioms.
The unconditional results use only `propext`, `Classical.choice`, and
`Quot.sound`. To resume an interrupted build, add `--resume`. Successfully
compiled modules are retained as proof objects and reused when newer than
their sources and direct imports. `--only` checks one module using existing
local proof objects. A separate low estimate audit is available through
`uv run verify_oai.py OAILowAudit`.

Run
`pdflatex -interaction=nonstopmode -halt-on-error paper.tex` twice to build
the PDF and resolve references.

See [FORMALIZATION.md](FORMALIZATION.md) for the proof dependencies and the
transport from the certified energy bounds to the perturbed moments.
