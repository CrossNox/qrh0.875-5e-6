# Formalization status

The target theorem is nonvanishing for `Re(s) > 174999/200000`. It is not
proved in Lean.

`BoundsReal.lean` proves the changed geometry, signal exponent, low margin,
low scale conditions, reflected-row loss inequality, and Euler-region
numerical margins over real numbers. `ReflectedExponent.lean` generalizes
the source's reflected-exponent calculation to the new slot length and proves
the extra positive-part loss. `EndpointCertificate.lean` proves the
source endpoint polynomial identity, its lower bound, its equality with the
high-bin exponent at the original geometry, and the perturbed high-endpoint
margin `2611/110160000`. All three files compile without `sorry` or new
axioms.

The local project now uses Lean 4.34.1 and the upstream Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. All three certificate
files compile together with `lake build` on this toolchain.

`LowGramScale.lean` proves the compensated Gram-factor inequality at the
changed physical scales. It also proves that a fixed slot-product cap
`L ≤ B Z^slotLength` eventually meets the required Gram condition
`L ≤ Z^(2*xLength-yLength)`.

The normalized compensated low estimate for the changed physical probe is
now proved in Lean. `OAIHighEulerRegion.lean` proves the unramified local
Euler defect bound at `Re(s) ≥ 174999/200000`, with decay
`240 Q^(-363/200+3/100000)`. `OAIHighPrincipalProduct.lean` proves that,
after excluding finitely many small primes, the actual principal Euler
correction is analytic and within `1/2` of `1` on the larger open region.
`OAIHighRamifiedBound.lean` proves the corresponding `193` bound for the
row-dependent ramified local factor at the new boundary. This carries the
changed lower bound through the marked-term, finite-sum, and closed-factor
estimates. `OAIHighHolomorphic.lean` proves that the unramified and
ramified local factors are analytic in each contour variable on the
corresponding enlarged region.
Run `uv run verify_oai.py OAIHighAudit` to check this chain against upstream
OAI and audit its axioms. The audited results report only `propext`,
`Classical.choice`, and `Quot.sound`.

The remaining proof requires row-dependent Euler correction bounds and
contour transport at the new boundary. The detector and high-row assembly
must use the prior 7/8 theorem with `κ = 3/4` and a positive gap
`β* - 174999/200000`.

The upstream low-side declaration that was strengthened is
[`compensatedPhysicalProbe_low`](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/LowCommonBound.lean).
It assumes the total slot length is at most `1/6` and concludes with the
fixed exponent `3/16`. The new probe has total length `1/6 + 3/100000`.
Its caller in `LowNormalized.lean` also fixes the original physical scales
`17/48` and `23/48`. The existing theorem cannot be applied to the new
probe, even though `BoundsReal.lean` proves the required numerical margins.
The `OAILow*.lean` files compile against upstream OAI with Lean 4.34.1.
They carry the changed parent exponent and surviving slot length through
reflected row energy, physical dyads, slot choices, completed rows, and
detector selected-row energy. The changed physical scale `Z^(5/6-t)/L²`
cancels the matching row-energy exponent after taking square roots. A sharper
slot-mass estimate retains a factor `Z^(-d)` for a rescaled subset of length
`d`. This absorbs the reflected-row loss in the central tuple. The central
and remote Gaussian dyads, common physical probe, original ray pools, and
normalizer are all proved for `0 ≤ t ≤ 1/30` and total slot length
`1/6+t`. `OAILowNormalized.lean` concludes with normalized bound
`Z^(3/16-t/4+loss)` for every positive `loss`. Run
`uv run verify_oai.py OAILowAudit` to rebuild the source-connected chain
and audit its axioms. The audit reports only `propext`, `Classical.choice`,
and `Quot.sound`.
The upstream `Reflection/LowOriginalEnergy.lean` assumes both `d ≤ 1/6`
and `ell0 ≤ 1/6-d+η`, and bounds parent norms using `5/6-2*d`. The new
probe needs `d ≤ 1/6+3/100000`, surviving length
`ell0 ≤ 1/6+3/100000-d`, and parent exponent
`5/6-3/100000-2*d`. The old theorem cannot yield the needed power saving
by setting its loss parameter `η` as large as the slot-length increase.

The [existing final assembly](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/FinalAssembly.lean)
starts with the assumption `7/8 < β*`. Its
[fixed high bound](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/FinalAssemblyFixedHigh.lean)
uses the original row scale `13/16` and boundary `7/8`. Those declarations
cannot prove the new theorem by changing only its concluding inequality.
