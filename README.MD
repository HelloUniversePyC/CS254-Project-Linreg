# Mechanized Privacy Proofs for Linear Regression

Dafny mechanization of sensitivity and non-interference for linear regression.
Proven results feed into a pen-and-paper derivation of MIA resistance via DP.

---

## What Dafny proves vs. what stays on paper

**Dafny proves** — deterministic properties of `w` and `Predict(w, x)`:
- Output sensitivity bound (squared form, no sqrt needed)
- Non-interference under zero sensitive weight
- Noise preserves both properties when `d[s] == 0`

**Pen-and-paper derives** — using Dafny results as verified premises:
- Sensitivity bound `Delta` → Gaussian mechanism is `(ε,δ)`-DP
  (Dwork & Roth 2014, Theorem A.1)
- `(ε,δ)`-DP → `AdvM(A) ≤ (e^ε − 1)/2 + δ` for any PPT adversary A
  (Yeom et al. 2018, Theorem 1)

---

## File dependency chain

```
linreg_base_case.dfy
│  Predict, NonInterference, NonInterferenceAux
│  i: nat throughout — avoids "decreases might not decrease"
│
├── noisy_noninterference.dfy
│      NoisyResult datatype (clean + delta), PredictWithNoise
│      NoisyNonInterference: w[s]=d[s]=0 → Observed() equal
│      NoisyLeakageDemo: d[s]≠0 breaks fairness → motivates FairNoise
│
└── vector_math.dfy
       NormSq, VectorDiff, SqAbs — all squared, no sqrt
       CauchySchwarzSq: (w·x)² ≤ ||w||²·||x||²  [hardest lemma]
       CauchySchwarzSqAux: inductive engine, decreases |w| - i
       DotProductDiff: (w-w')·x = w·x - w'·x
       │
       └── sensitivity.dfy
              │
              └── dp_mechanism.dfy  (also includes noisy_noninterference.dfy)
                     │
                     └── privacy_summary.dfy- Ties together all results to prove attacker bound
                          
```

---

## Key design decisions

**Squared norms throughout.** Dafny's `real` has no `sqrt` and Z3 cannot
handle it reliably. Every sensitivity statement uses `x * x ≤ y * y` form.
The standard bound `|·| ≤ Delta·||x||` follows on paper by taking square
roots — one sentence in the writeup.

**`Delta` is a precondition, not computed.** Dafny does not verify the
training algorithm or adjacent datasets. `NormSq(VectorDiff(w, w')) ≤ Delta²`
is assumed. The pen-and-paper argument justifies this via Chaudhuri et al. 2011.

**`Epsilon` and `DeltaDP` are fixed constants, not random variables.**
The randomness lives in the attacker `A` and the noise draw. `ε` and `δ`
are mechanism design choices, fixed before deployment.

---

## References

- Yeom et al. (2018) — membership advantage definition, Theorem 1
- Dwork & Roth (2014) — `(ε,δ)`-DP definition, Gaussian mechanism Theorem A.1
- Chaudhuri, Monteleoni & Sarwate (2011) — sensitivity of linear regression
- de Medeiros et al. / SampCert (2024) — closest mechanized DP work (Lean, no attacker model)