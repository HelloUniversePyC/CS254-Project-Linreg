include "dp_mechanism.dfy"

//how the ensures clauses feed into Yeom Theorem 1
lemma DafnyContribution(w: seq<real>, w': seq<real>,
                          x: seq<real>, x': seq<real>,
                          d: seq<real>, s: nat)
  requires |w| == |w'| == |x| == |x'| == |d| > 0
  requires ValidFeatureVector(x) && ValidFeatureVector(x')
  requires 0 <= s < |w|
  requires w[s] == 0.0                               // model is fair on s
  requires FairNoise(d, s)                           // noise is fair on s
  requires NormSq(VectorDiff(w, w')) <= Delta * Delta // weights differ by at most Delta
  requires GaussianNoise(d)
  requires forall i :: 0 <= i < |w| && i != s ==> x[i] == x'[i]

  // Conclusion 1: squared sensitivity bound
  // feeds into GaussianMechanismIsDP (axiom) →
  // then into Yeom Theorem 1 →
  // gives AdvM(A) ≤ (e^Epsilon - 1)/2 + DeltaDP
  ensures (Predict(w, x) - Predict(w', x)) *
          (Predict(w, x) - Predict(w', x)) <=
          Delta * Delta * NormSq(x)

  // Conclusion 2: noisy sensitivity (same bound, noisy outputs)
  // confirms noise does not inflate the sensitivity
  ensures (PredictWithNoise(w, x, d).Observed() -
           PredictWithNoise(w', x, d).Observed()) *
          (PredictWithNoise(w, x, d).Observed() -
           PredictWithNoise(w', x, d).Observed()) <=
          Delta * Delta * NormSq(x)

  // Conclusion 3: noisy non-interference
  // fairness holds end-to-end under noise
  // independent of the DP argument
  ensures PredictWithNoise(w, x, d).Observed() ==
          PredictWithNoise(w, x', d).Observed()
{
  OutputSensitivity(w, w', x);
  NoisyOutputSensitivity(w, w', x, d);
  FairNoisyModel(w, x, x', d, s);
}