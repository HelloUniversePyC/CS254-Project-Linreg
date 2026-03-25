

include "linreg_base_case.dfy"

// data type to add noise to linear regression 
// Keeps clean prediction and noise delta separate so we can reason about each
// Observed() gives the actual output (what attacker sees)
datatype NoisyResult = NoisyResult(clean: real, delta: real)
{
  function Observed(): real { clean + delta }
}
//clean = the true prediction w·x (no noise)
// delta = the noise term -d·x

// noise vector d disturbs the weights: noisy output = w·x - d·x
// we store the noise contribution separately as delta = -d·x
function PredictWithNoise(w: seq<real>, x: seq<real>, d: seq<real>): NoisyResult
  requires |w| == |x| == |d|
{
  NoisyResult(Predict(w, x), -Predict(d, x))
}

// the observed noisy prediction equals the clean prediction minus the noise dot product.
lemma NoisyDecomposition(w: seq<real>, x: seq<real>, d: seq<real>)
  requires |w| == |x| == |d|
  ensures PredictWithNoise(w, x, d).Observed() == Predict(w, x) - Predict(d, x)
{
  // follows directly from the datatype definition
}

// Noisy Non-Interference 

// If both the model weight w[s] and the noise component d[s] are zero,
// then the noisy prediction still satisfies non-interference.
// noise can breatk fairness if d[s] != 0,
// even when the model itself is fair (w[s] == 0).
lemma NoisyNonInterference(w: seq<real>, x: seq<real>, x': seq<real>,
                            d: seq<real>, s: int)
  requires |w| == |x| == |x'| == |d|
  requires 0 <= s < |w|
  requires w[s] == 0.0 && d[s] == 0.0
  requires forall i :: 0 <= i < |w| && i != s ==> x[i] == x'[i]
  ensures PredictWithNoise(w, x, d).Observed() ==
          PredictWithNoise(w, x', d).Observed()
{
  // the clean predictions are equal (by base case non-interference)
  NonInterference(w, x, x', s);
  // The noise contributions are equal
  NonInterference(d, x, x', s);
}

// noise preserves fairness when d[s] == 0

method NoisyLoanScoringDemo()
{
  // Feature layout: [income, race, credit_score]
  var w     := [0.5, 0.0, 0.3];   // race weight zeroed for fairness
  var d     := [0.01, 0.0, 0.02]; // noise on income and credit, but not race
  var alice := [80000.0, 0.0, 720.0];
  var bob   := [80000.0, 1.0, 720.0];

  // provimng noisy predictions are still fair
  NoisyNonInterference(w, alice, bob, d, 1);

  var noisy_alice := PredictWithNoise(w, alice, d);
  var noisy_bob   := PredictWithNoise(w, bob, d);
  assert noisy_alice.Observed() == noisy_bob.Observed();
}

// Counter-example: Noise can break fairness

// When d[s] != 0, the noise leaks information about the sensitive feature.
// We demonstrate this by showing the predictions diverge.
method NoisyLeakageDemo()
{
  var w     := [0.5, 0.0, 0.3];    // model is fair (w[1] == 0)
  var d     := [0.0, 0.05, 0.0];   // but noise touches the sensitive feature!
  var alice := [80000.0, 0.0, 720.0];
  var bob   := [80000.0, 1.0, 720.0];

  var noisy_alice := PredictWithNoise(w, alice, d);
  var noisy_bob   := PredictWithNoise(w, bob, d);

  // The noise on the sensitive feature causes different outputs:
  // alice noise = -d·alice =  = 0.0
  // bob noise   = -d·bob   = -0.05
  // since alice.Observed() != bob.Observed(), fairness is broken by noise.
  assert noisy_alice.delta == 0.0;
  assert noisy_bob.delta == -0.05;
  assert noisy_alice.Observed() != noisy_bob.Observed();
}
