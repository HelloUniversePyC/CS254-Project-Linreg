

//  Real-world framing: loan scoring where x[s] =  as sensitive feature (like race or gender).
//dot product of weights and features.
function Predict(w: seq<real>, x: seq<real>): real
  requires |w| == |x| //the cardinality of w is the same as the number of predictor variables
{
  PredictAux(w, x, 0)
}

// recursive helper accumulating the partial dot product.
function PredictAux(w: seq<real>, x: seq<real>, i: int): real
  requires |w| == |x|
  requires 0 <= i <= |w|
  decreases |w| - i        
{
  if i == |w| then 0.0 //base case, we stop when we get the total number of elements in w
  else w[i] * x[i] + PredictAux(w, x, i + 1) //otherwise we continue computing the dot product and increment i
}
// Zeroing a weight makes that feature irrelevant.
//
//  If w[s] == 0.0, and two feature vectors agree everywhere
//  except possibly at index s, then their predictions are equal.
// The sensitive feature index s must not be the bias term.
// The bias trick appends x[|x|-1] = 1.0 — that weight must stay nonzero.
// The bias trick: the last entry is always 1.0.
// This slot is reserved for the bias weight and is never a sensitive index.
predicate ValidFeatureVector(x: seq<real>)
{
  |x| > 1 &&                  // at least one real feature plus the bias slot
  x[|x| - 1] == 1.0           // bias slot
}
lemma NonInterference(w: seq<real>, x: seq<real>, x': seq<real>, s: nat)
  requires |w| == |x| == |x'|
  requires ValidFeatureVector(x) && ValidFeatureVector(x')  // x[|x|-1] == 1.0
  requires 0 <= s < |w| - 1    // s cannot be the last index — that's the bias<- have to apply bias trick correctly
  requires w[s] == 0.0
  requires forall i :: 0 <= i < |w| && i != s ==> x[i] == x'[i]
  ensures Predict(w, x) == Predict(w, x')
{
  NonInterferenceAux(w, x, x', s, 0);
}

//  We generalize NonInterference to partial sums starting at i.
// s: nat throughout — consistent with NonInterference
lemma NonInterferenceAux(w: seq<real>, x: seq<real>, x': seq<real>, 
                          s: nat, i: nat)
  requires |w| == |x| == |x'|
  requires 0 <= s < |w|        // aux doesn't need s < |w|-1 —
                                // that constraint lives in NonInterference
  requires i <= |w|
  requires w[s] == 0.0
  requires forall j :: 0 <= j < |w| && j != s ==> x[j] == x'[j]
  ensures PredictAux(w, x, i) == PredictAux(w, x', i)
  decreases |w| - i
{
  if i == |w| {
  } else if i == s {
    NonInterferenceAux(w, x, x', s, i + 1);
  } else {
    NonInterferenceAux(w, x, x', s, i + 1);
  }
}

//  lemma applies in a concrete scenario.
//  Three features: [income, race, credit_score]
//Assume race is a binary variable <- 0-> white, 1<- black, for simplicity
//  The model zeros out race (index 1) to satisfy non-interference.
method LoanScoringDemo()
{
  // Feature layout: [income, race, credit_score, bias]
  // bias slot is always 1.0 — required by ValidFeatureVector
  // w[3] is the learned intercept (bias weight)
  var w     := [0.5, 0.0, 0.3, 1.0];   // race weight (index 1) is 0
                                         // bias weight (index 3) is 1.0
  var alice := [80000.0, 0.0, 720.0, 1.0];  // race = 0, bias = 1.0
  var bob   := [80000.0, 1.0, 720.0, 1.0];  // race = 1, bias = 1.0

  // s = 1 (race), which satisfies s < |w| - 1 = 3
  NonInterference(w, alice, bob, 1);

  var score_alice := Predict(w, alice);
  var score_bob   := Predict(w, bob);
  assert score_alice == score_bob;
}