

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
lemma NonInterference(w: seq<real>, x: seq<real>, x': seq<real>, s: int) //seq<real> <- sequence of real numbers<- models the weights
  requires |w| == |x| == |x'| //have same number of predictors
  requires 0 <= s < |w| // the zeroed out weight is a valid index
  // The sensitive weight is zeroed out
  requires w[s] == 0.0 // the weight is zeroed out 
  // The two feature vectors agree on everything except the sensitive index
  requires forall i :: 0 <= i < |w| && i != s ==> x[i] == x'[i] //non-inference lemma
  decreases |w| -1 // We eventually terminate
  // Conclusion: predictions are identical
  ensures Predict(w, x) == Predict(w, x')
{
  NonInterferenceAux(w, x, x', s, 0);
}

//  We generalize NonInterference to partial sums starting at i.
lemma NonInterferenceAux(w: seq<real>, x: seq<real>, x': seq<real>, s: int, i: int) //proving interference requires reasoning about 2 executions, x and x'
  requires |w| == |x| == |x'|
  requires 0 <= s < |w|
  requires 0 <= i <= |w|
  requires w[s] == 0.0
  requires forall j :: 0 <= j < |w| && j != s ==> x[j] == x'[j]
  ensures PredictAux(w, x, i) == PredictAux(w, x', i)
  decreases |w| - i        // <-- added
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
method LoanScoringDemo() //Linear regression to generate scalar "credit score" of applicants
{
  // Feature layout: [income, race, credit_score]
  var w  := [0.5, 0.0, 0.3];  // race weight is 0<- allows for trival case
  var alice := [80000.0, 0.0, 720.0];  // race = 0
  var bob   := [80000.0, 1.0, 720.0];  // race = 1 
  // Invoke the lemma
  NonInterference(w, alice, bob, 1);
  // At runtime, confirm predictions match
  var score_alice := Predict(w, alice);
  var score_bob   := Predict(w, bob);
  assert score_alice == score_bob;  
}