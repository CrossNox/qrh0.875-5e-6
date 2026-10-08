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

The remaining proof requires the actual analytic estimates for the changed
physical probe. In particular, its reflected-row and additive Gram bounds
must yield the new low estimate, and its full Euler correction must support
the contour moves to `Re(s) > 174999/200000`. The detector and high-row
assembly must use the prior 7/8 theorem with `κ = 3/4` and a positive gap
`β* - 174999/200000`.

The first low-side declaration that must be strengthened is
[`compensatedPhysicalProbe_low`](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/LowCommonBound.lean).
It assumes the total slot length is at most `1/6` and concludes with the
fixed exponent `3/16`. The new probe has total length `1/6 + 3/100000`.
Its caller in `LowNormalized.lean` also fixes the original physical scales
`17/48` and `23/48`. The existing theorem cannot be applied to the new
probe, even though `BoundsReal.lean` proves the required numerical margins.
The new reflected-exponent lemma is standalone arithmetic. It has not been
connected to the upstream row-energy theorem or the probe norm estimate.

The [existing final assembly](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/FinalAssembly.lean)
starts with the assumption `7/8 < β*`. Its
[fixed high bound](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/FinalAssemblyFixedHigh.lean)
uses the original row scale `13/16` and boundary `7/8`. Those declarations
cannot prove the new theorem by changing only its concluding inequality.
