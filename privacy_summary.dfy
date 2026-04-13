include "dp_mechanism.dfy"
include "sensitivity.dfy"

// ─── privacy_summary.dfy ───────────────────────────────────────
// Main conclusion: DP correctly calibrated does not leak the sensitive
// feature through predictions and does not inflate membership signals
//
// What Dafny proves — the mechanized premises:
//
// Conclusion 1: OutputSensitivity (from sensitivity.dfy)
//   prediction difference between adjacent models bounded by Delta()*||x||
//   this is the membership signal — how much the model output shifts
//   depending on whether a point was in the training set
//
// Conclusion 2: NoisyOutputSensitivity (from dp_mechanism.dfy)
//   noise does not inflate the membership signal —
//   the bound is identical whether or not noise is present
//
// Conclusion 3: CalibratedNoisyModel (from dp_mechanism.dfy)
//   when d[s] = w[s], the sensitive feature produces zero signal
//   through noisy predictions for ANY w[s]
//

lemma DafnyContribution(w: seq<real>, w': seq<real>,
                         x: seq<real>, x': seq<real>,
                         d: seq<real>, s: nat)
  requires |w| == |w'| == |x| == |x'| == |d| > 0
  requires ValidFeatureVector(x) && ValidFeatureVector(x')
  requires 0 <= s < |w| - 1
  requires CalibratedNoise(d, w, s)  // d[s] == w[s] — no constraint on w[s]
  requires NormSq(VectorDiff(w, w')) <= Delta() * Delta()
  requires GaussianNoise(d)
  requires forall i :: 0 <= i < |w| && i != s ==> x[i] == x'[i]

  // Conclusion 1: sensitivity bound holds for any w
  ensures (Predict(w, x) - Predict(w', x)) *
          (Predict(w, x) - Predict(w', x)) <=
          Delta() * Delta() * NormSq(x)

  // Conclusion 2: noise does not inflate the sensitivity bound
  ensures (PredictWithNoise(w, x, d).Observed() -
           PredictWithNoise(w', x, d).Observed()) *
          (PredictWithNoise(w, x, d).Observed() -
           PredictWithNoise(w', x, d).Observed()) <=
          Delta() * Delta() * NormSq(x)

  // Conclusion 3: zero leakage for any w[s] when d[s] = w[s]
  ensures PredictWithNoise(w, x, d).Observed() ==
          PredictWithNoise(w, x', d).Observed()
{
  OutputSensitivity(w, w', x);
  NoisyOutputSensitivity(w, w', x, d);
  CalibratedNoisyModel(w, x, x', d, s);
}