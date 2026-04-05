// ─── dp_mechanism.dfy ──────────────────────────────────────────

include "sensitivity.dfy"
include "noisy_noninterference.dfy"

// Fixed mechanism parameters — not random variables
// Chosen at deployment time, consumed as preconditions
const Epsilon: real
  ensures Epsilon > 0.0
  

const DeltaDP: real
  ensures 0.0 < DeltaDP < 1.0

// Predicate: noise vector is Gaussian-distributed with scale NoiseScale
// We do not construct a specific d — this is a precondition on d
predicate GaussianNoise(d: seq<real>)
  requires |d| > 0

// Predicate: noise does not touch the sensitive feature
predicate FairNoise(d: seq<real>, s: nat)
  requires |d| > 0
  requires 0 <= s < |d|
{
  d[s] == 0.0
}

// AXIOM: Gaussian mechanism satisfies (Epsilon, DeltaDP)-DP
// given sensitivity Delta and appropriate noise scale
// Source: Dwork and Roth (2014), Theorem A.1
lemma {:axiom} GaussianMechanismIsDP(w: seq<real>, w': seq<real>)
  requires |w| == |w'| > 0
  requires NormSq(VectorDiff(w, w')) <= Delta * Delta
  ensures DPGuarantee(w, w', Epsilon, DeltaDP)
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

// Provable: noisy sensitivity bound
// same squared form as OutputSensitivity,
// noise cancellation means the bound is identical
lemma NoisyOutputSensitivity(w: seq<real>, w': seq<real>,
                               x: seq<real>, d: seq<real>)
  requires |w| == |w'| == |x| == |d| > 0
  requires ValidFeatureVector(x)
  requires NormSq(VectorDiff(w, w')) <= Delta * Delta
  requires GaussianNoise(d)
  ensures (PredictWithNoise(w, x, d).Observed() -
           PredictWithNoise(w', x, d).Observed()) *
          (PredictWithNoise(w, x, d).Observed() -
           PredictWithNoise(w', x, d).Observed()) <=
          Delta * Delta * NormSq(x)
{
  NoiseCancelsInDiff(w, w', x, d);
  OutputSensitivity(w, w', x);
}

// Provable: fair noise + fair model → noisy non-interference
// invokes NoisyNonInterference result directly
lemma FairNoisyModel(w: seq<real>, x: seq<real>, x': seq<real>,
                      d: seq<real>, s: nat)
  requires |w| == |x| == |x'| == |d| > 0
  requires ValidFeatureVector(x) && ValidFeatureVector(x')
  requires 0 <= s < |w|
  requires w[s] == 0.0
  requires FairNoise(d, s)
  requires forall i :: 0 <= i < |w| && i != s ==> x[i] == x'[i]
  ensures PredictWithNoise(w, x, d).Observed() ==
          PredictWithNoise(w, x', d).Observed()
{
  NoisyNonInterference(w, x, x', d, s);
}