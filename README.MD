# Mechanized Privacy Proofs for Linear Regression

Dafny mechanization of sensitivity, exact leakage, and calibrated noise
non-interference for linear regression. Proven results feed into a
pen-and-paper derivation of MIA resistance via DP.

---

## What Dafny proves vs. what stays on paper

**Dafny proves** — deterministic properties of `w`, `d`, and `Predict(w, x)`:
- Output sensitivity bound (squared form, no sqrt needed) — for any `w`, no zero-weight assumption
- Exact leakage formula: when inputs differ only on feature `s`, the squared
  noisy prediction difference equals exactly `(w[s]-d[s])² · (x[s]-x'[s])²`
  for any value of `w[s]`
- Zero leakage under calibrated noise: when `d[s] = w[s]`, leakage is zero
  regardless of what `w[s]` is — this is the general DP guarantee
- Noise does not inflate the sensitivity bound (NoiseCancelsInDiff)
- Zero-weight special cases (NonInterference, NoisyNonInterference) are
  contained in `linreg_base_case.dfy` and `linreg_noisy.dfy` as unit tests,
  not carried into the general proof

**Pen-and-paper derives** — using Dafny results as verified premises:
- Sensitivity bound `Delta` → Gaussian mechanism is `(ε,δ)`-DP
  (Dwork & Roth 2014, Theorem A.1)
- `CauchySchwarzSq` is axiomatized — Z3's nonlinear real arithmetic cannot
  verify polynomial identities of this form; pen-and-paper proof in Appendix A

---

## File dependency chain
```
linreg_base_case.dfy
│  Predict, NonInterference, NonInterferenceAux
│  zero-weight unit tests only — not carried into general proof
│
├── linreg_noisy.dfy
│      NoisyResult datatype (clean + delta), PredictWithNoise
│      NoisyDecomposition: Observed() = Predict(w,x) - Predict(d,x)
│      NoisyNonInterference: w[s]=d[s]=0 → Observed() equal [unit test]
│      NoisyLeakageDemo: d[s]≠0 breaks fairness [unit test]
│
└── vector_math.dfy
NormSq, VectorDiff, SqAbs — all squared, no sqrt
CauchySchwarzSq: (w·x)² ≤ ||w||²·||x||²  [axiom see write up]
DotProductDiff: (w-w')·x = w·x - w'·x
│
└── sensitivity.dfy
OutputSensitivity: sensitivity bound for any w
BoundedSensitiveLeakage: exact leakage (w[s]-d[s])²·(x[s]-x'[s])²
BoundedSensitiveLeakageAux: isolates index-s contribution
BoundedSensitiveLeakageAuxInductive: inductive engine
│
└── dp_mechanism.dfy
CalibratedNoise: predicate d[s] = w[s]
CalibratedNoisyModel: zero leakage for any w[s]
NoiseCancelsInDiff: noise does not inflate sensitivity
NoisyOutputSensitivity: noisy bound identical to clean bound
GaussianMechanismIsDP: axiom, Dwork & Roth 2014 Theorem A.1
DPGuarantee: axiom, probability condition inexpressible in Dafny
│
└── privacy_summary.dfy
DafnyContribution: ties together all three conclusions
for arbitrary w[s] — the top-level mechanized result
```
---

## Key design decisions

**Squared norms throughout.** Dafny's `real` has no `sqrt` and Z3 cannot
handle it reliably. Every sensitivity statement uses `x * x ≤ y * y` form.
The standard bound `|·| ≤ Delta·||x||` follows on paper by taking square roots.

**`Delta` is a precondition, not computed.** Dafny does not verify the
training algorithm or adjacent datasets. `NormSq(VectorDiff(w, w')) ≤ Delta²`
is assumed (Chaudhuri et al. 2011).

**`CalibratedNoise` requires `d[s] = w[s]` exactly.** In practice Gaussian
noise is continuous and this condition holds in expectation, not exactly.
The mechanized result is algebraically exact — the gap between this and the
probabilistic reality of the mechanism is noted but not mechanized, as it
requires a probability monad Dafny does not have.

**`GaussianNoise` and `DPGuarantee` are axiomatized.** Dafny cannot express
probability distributions or measurable sets. These predicates exist so that
`GaussianMechanismIsDP` has a well-typed postcondition that downstream lemmas
can consume as a verified premise for the pen-and-paper argument.

**`Epsilon` and `DeltaDP` are fixed constants, not random variables.**
The randomness lives in the noise draw. `ε` and `δ` are mechanism design
choices fixed before deployment.

**Zero-weight cases are unit tests, not the general result.** `linreg_base_case.dfy`
and `linreg_noisy.dfy` contain the `w[s] = 0` special cases deliberately as
contained tests. The general proof in `sensitivity.dfy` and `dp_mechanism.dfy`
makes no zero-weight assumption — `w[s]` is unconstrained throughout.

---

## References

- Dwork & Roth (2014) — `(ε,δ)`-DP definition, Gaussian mechanism Theorem A.1
- Chaudhuri, Monteleoni & Sarwate (2011) — sensitivity of linear regression
- de Medeiros et al. / SampCert (2024) — closest mechanized DP work (Lean, no attacker model)