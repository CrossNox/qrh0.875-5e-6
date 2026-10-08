# Formalization status

The target theorem is nonvanishing for `Re(s) > 174999/200000`. It is not
proved in Lean.

`BoundsReal.lean` proves the changed geometry, signal exponent, low margin,
low scale conditions, reflected-row loss inequality, and Euler-region
numerical margins over real numbers. `EndpointCertificate.lean` proves the
source endpoint polynomial identity, its lower bound, its equality with the
high-bin exponent at the original geometry, and the perturbed high-endpoint
margin `2611/110160000`. Both files compile without `sorry` or new axioms.

The remaining proof requires the actual analytic estimates for the changed
physical probe. In particular, its reflected-row and additive Gram bounds
must yield the new low estimate, and its full Euler correction must support
the contour moves to `Re(s) > 174999/200000`. The detector and high-row
assembly must use the prior 7/8 theorem with `κ = 3/4` and a positive gap
`β* - 174999/200000`.

The [existing final assembly](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/FinalAssembly.lean)
starts with the assumption `7/8 < β*`. Its
[fixed high bound](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/FinalAssemblyFixedHigh.lean)
uses the original row scale `13/16` and boundary `7/8`. Those declarations
cannot prove the new theorem by changing only its concluding inequality.
