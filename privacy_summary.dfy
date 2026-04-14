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
//   this is the general case — w[s] need not be zero

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

  // Conclusion 3: zero leakage for any w[s] when d[s] == w[s]
  ensures PredictWithNoise(w, x, d).Observed() ==
          PredictWithNoise(w, x', d).Observed()
{
  OutputSensitivity(w, w', x);
  NoisyOutputSensitivity(w, w', x, d);
  CalibratedNoisyModel(w, x, x', d, s);
}

//Concrete demonstration 
// Feature layout: [income, race, credit_score, bias]
//
// The KEY difference from the base case demo:
// here w[1] = 0.7 (nonzero race weight) — the model DOES use race.
// DP noise d[1] = w[1] = 0.7 calibrated to cancel the race signal.
// Alice and Bob get identical noisy scores despite:
//   (a) the model having a nonzero race coefficient
//   (b) Alice and Bob having different race values
// This is what DP buys you beyond simple feature removal.
//
// Compare to NoisyLoanScoringDemo in noisy_noninterference.dfy
// where w[1] = 0 (trivial case) — here w[1] = 0.7 (general case).

method CalibratedDPLoanDemo()
{
  // Model DOES use race — w[1] = 0.7, not zero
  // This is the realistic case where the model learned a race coefficient
  var w     := [0.5, 0.7, 0.3, 1.0];

  // Adjacent model — same as w except one training point differs
  // weight difference satisfies the sensitivity precondition
  var w'    := [0.5, 0.7, 0.3, 1.0];  // same weights for demo clarity
                                        // in practice w' differs by ≤ Delta()

  // DP noise: d[s] = w[s] = 0.7 on the race feature (index 1)
  // noise on other features is small (calibrated to Delta())
  // noise on bias slot is zero
  var d     := [0.01, 0.7, 0.02, 0.0];

  // Alice: race = 0, Bob: race = 1 — differ ONLY on race
  var alice := [80000.0, 0.0, 720.0, 1.0];
  var bob   := [80000.0, 1.0, 720.0, 1.0];

  // Clean predictions ARE different — the model uses race
  var score_alice_clean := Predict(w, alice);
  var score_bob_clean   := Predict(w, bob);
  // score_alice_clean = 0.5*80000 + 0.7*0.0 + 0.3*720 + 1.0 = 40217.0
  // score_bob_clean   = 0.5*80000 + 0.7*1.0 + 0.3*720 + 1.0 = 40217.7
  // these are NOT equal — the model is not fair on its own
  assert score_alice_clean != score_bob_clean;

  // Noisy predictions ARE equal — DP noise cancels the race signal
  // noisy_alice = Predict(w,alice) - Predict(d,alice)
  //             = (w-d)·alice
  //             = [0.49, 0.0, 0.28, 1.0]·[80000, 0.0, 720, 1.0]
  //             = 0.49*80000 + 0.0*0.0 + 0.28*720 + 1.0
  // noisy_bob   = (w-d)·bob
  //             = [0.49, 0.0, 0.28, 1.0]·[80000, 1.0, 720, 1.0]
  //             = 0.49*80000 + 0.0*1.0 + 0.28*720 + 1.0
  // since (w[1]-d[1]) = 0.7-0.7 = 0.0, the race term vanishes in both
  var noisy_alice := PredictWithNoise(w, alice, d);
  var noisy_bob   := PredictWithNoise(w, bob, d);
  assert noisy_alice.Observed() == noisy_bob.Observed();

  // Invoke the general lemma — works for any w[s], not just w[s]=0
  // This is what makes this demo stronger than NoisyLoanScoringDemo
  CalibratedNoisyModel(w, alice, bob, d, 1);
}

// ─── Counter-example: uncalibrated noise still leaks ──────────
// Even with DP noise present, if d[s] ≠ w[s] the race signal leaks.
// This shows calibration of d[s] to w[s] is necessary, not just sufficient.
// Compare to NoisyLeakageDemo in noisy_noninterference.dfy which showed
// the same for the zero-weight case.

method UncalibratedDPLeakageDemo()
{
  // Same nonzero race weight as above
  var w     := [0.5, 0.7, 0.3, 1.0];

  // Noise is present but NOT calibrated to w[s]:
  // d[1] = 0.3 ≠ w[1] = 0.7 — partial cancellation only
  var d     := [0.01, 0.3, 0.02, 0.0];

  var alice := [80000.0, 0.0, 720.0, 1.0];
  var bob   := [80000.0, 1.0, 720.0, 1.0];

  var noisy_alice := PredictWithNoise(w, alice, d);
  var noisy_bob   := PredictWithNoise(w, bob, d);

  // (w[1] - d[1]) = 0.7 - 0.3 = 0.4 ≠ 0
  // so race still contributes 0.4 * (x[1] - x'[1]) = 0.4 * 1.0 = 0.4
  // to the prediction difference — partial leakage remains
 assert noisy_alice.Observed() != noisy_bob.Observed();  // leakage exists
 assert noisy_bob.Observed() - noisy_alice.Observed() == 
       (w[1] - d[1]) * (bob[1] - alice[1]);             // = 0.4 * 1.0 = 0.4
}