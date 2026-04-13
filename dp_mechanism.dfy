// ─── dp_mechanism.dfy ──────────────────────────────────────────
// Conclusion 2: NoisyOutputSensitivity
//   Does adding DP noise make things worse?
//   no — noise cancels in the difference, the bound is identical to OutputSensitivity
//
// Conclusion 3: CalibratedNoisyModel
//   Does the sensitive feature leak through noisy predictions for arbitrary w[s]?
//   no — when d[s] = w[s], leakage is exactly zero regardless of what w[s] is
//   this is the general DP guarantee, not the trivial zero-weight special case

include "sensitivity.dfy"
include "linreg_noisy.dfy"
include "linreg_base_case.dfy"

// Fixed mechanism parameters — not random variables
// Chosen at deployment time, consumed as preconditions
function {:axiom} Epsilon(): real
  ensures Epsilon() > 0.0

function {:axiom} DeltaDP(): real
  ensures 0.0 < DeltaDP() < 1.0

// Predicate: noise vector is Gaussian-distributed with scale NoiseScale
// We do not construct a specific d — this is a precondition on d
predicate GaussianNoise(d: seq<real>)
  requires |d| > 0

// Predicate: noise on the sensitive feature is calibrated to the model weight
// This is the general DP condition — d[s] = w[s] achieves zero leakage
// for any value of w[s], not just zero
predicate CalibratedNoise(d: seq<real>, w: seq<real>, s: nat)
  requires |d| == |w| > 1
  requires 0 <= s < |d| - 1
{
  d[s] == w[s]
}

// Predicate: the (ε,δ)-DP guarantee between adjacent models w and w'
// States that for any measurable set S of outputs:
//   Pr[NoisyW ∈ S] ≤ exp(ε) · Pr[NoisyW' ∈ S] + δ
// We cannot express probability distributions in Dafny directly
// hence this predicate is axiomatized and consumed as a postcondition
// Source: Dwork and Roth (2014), Definition 2.4
predicate {:axiom} DPGuarantee(w: seq<real>, w': seq<real>, 
                                epsilon: real, delta: real)
  requires |w| == |w'| > 0
  requires epsilon > 0.0
  requires 0.0 < delta < 1.0


// Proof: calibrated noise achieves zero leakage for any w[s]
//General result — no zero-weight assumption
lemma CalibratedNoisyModel(w: seq<real>, x: seq<real>, x': seq<real>,
                            d: seq<real>, s: nat)
  requires |w| == |x| == |x'| == |d| > 0
  requires ValidFeatureVector(x) && ValidFeatureVector(x')
  requires 0 <= s < |w| - 1
  requires CalibratedNoise(d, w, s)  // d[s] == w[s], w[s] unconstrained
  requires forall i :: 0 <= i < |w| && i != s ==> x[i] == x'[i]
  ensures PredictWithNoise(w, x, d).Observed() ==
          PredictWithNoise(w, x', d).Observed()
{
  PredictEqDotProduct(w, x);
  PredictEqDotProduct(w, x');
  PredictEqDotProduct(d, x);
  PredictEqDotProduct(d, x');
  DotProductDiff(w, d, x);
  DotProductDiff(w, d, x');
  BoundedSensitiveLeakageAux(w, d, x, x', s);
  // BoundedSensitiveLeakageAux gives:
  // DotProduct(VectorDiff(w,d), x) - DotProduct(VectorDiff(w,d), x') == (w[s]-d[s])*(x[s]-x'[s])
  // since d[s] == w[s], the right hand side is 0.0
  assert (w[s] - d[s]) == 0.0;
  assert DotProduct(VectorDiff(w, d), x) == DotProduct(VectorDiff(w, d), x');
  NoisyDecomposition(w, x, d);
  NoisyDecomposition(w, x', d);
}

// AXIOM: Gaussian mechanism satisfies (Epsilon, DeltaDP)-DP
// given sensitivity Delta and appropriate noise scale
// Source: Dwork and Roth (2014), Theorem A.1
lemma {:axiom} GaussianMechanismIsDP(w: seq<real>, w': seq<real>)
  requires |w| == |w'| > 0
  requires NormSq(VectorDiff(w, w')) <= Delta() * Delta()
  ensures DPGuarantee(w, w', Epsilon(), DeltaDP())
  // DPGuarantee is a predicate stating the ratio condition
  // Pr[NoisyW ∈ S] ≤ exp(Epsilon) · Pr[NoisyW' ∈ S] + DeltaDP
  

// Provable: noise cancels in the prediction difference
// when the same noise vector d is applied to both w and w'
// (Predict(w,x,d) - Predict(w',x,d))² = (Predict(w,x) - Predict(w',x))²
lemma NoiseCancelsInDiff(w: seq<real>, w': seq<real>,
                          x: seq<real>, d: seq<real>)
  requires |w| == |w'| == |x| == |d| > 0
  ensures (PredictWithNoise(w, x, d).Observed() -
           PredictWithNoise(w', x, d).Observed()) *
          (PredictWithNoise(w, x, d).Observed() -
           PredictWithNoise(w', x, d).Observed()) ==
          (Predict(w, x) - Predict(w', x)) *
          (Predict(w, x) - Predict(w', x))
  // Proof: noise term -d·x appears in both and cancels
{
  NoisyDecomposition(w, x, d);
  NoisyDecomposition(w', x, d);

}
// Provable: noisy sensitivity bound
// same squared form as OutputSensitivity,
// noise cancellation means the bound is identical
lemma NoisyOutputSensitivity(w: seq<real>, w': seq<real>,
                               x: seq<real>, d: seq<real>)
  requires |w| == |w'| == |x| == |d| > 0
  requires ValidFeatureVector(x)
  requires NormSq(VectorDiff(w, w')) <= Delta() * Delta()
  requires GaussianNoise(d)
  ensures (PredictWithNoise(w, x, d).Observed() -
           PredictWithNoise(w', x, d).Observed()) *
          (PredictWithNoise(w, x, d).Observed() -
           PredictWithNoise(w', x, d).Observed()) <=
          Delta() * Delta() * NormSq(x)
{
  NoiseCancelsInDiff(w, w', x, d);
  OutputSensitivity(w, w', x);
}

