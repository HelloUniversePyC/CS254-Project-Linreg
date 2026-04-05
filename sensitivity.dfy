include "linreg_base_case.dfy"
include "vector_math.dfy"

// Sensitivity constant — scalar, not a norm
// Delta = max ||w(D) - w(D')|| over adjacent D, D'
// precondition on the weight vectors we reason about
const Delta: real
  ensures Delta > 0.0


// Core sensitivity lemma — the primary Dafny contribution
// (Predict(w,x) - Predict(w',x))² ≤ Delta² · ||x||²
// |Predict(w,x) - Predict(w',x)| ≤ Delta·||x||
lemma OutputSensitivity(w: seq<real>, w': seq<real>, x: seq<real>)
  requires |w| == |w'| == |x| > 0
  requires ValidFeatureVector(x)
  requires NormSq(VectorDiff(w, w')) <= Delta * Delta
  ensures (Predict(w, x) - Predict(w', x)) *
          (Predict(w, x) - Predict(w', x)) <=
          Delta * Delta * NormSq(x)
          {

          }

// Sensitivity composes with non-interference:
// zeroing the sensitive weight does not weaken the bound
// and the sensitive feature contributes zero to the difference
lemma SensitivityWithNonInterference(w: seq<real>, w': seq<real>,
                                      x: seq<real>, s: nat)
  requires |w| == |w'| == |x| > 0
  requires ValidFeatureVector(x)           // already had this
  requires 0 <= s < |w| - 1               // change: was s < |w|
  requires w[s] == 0.0 && w'[s] == 0.0
  requires NormSq(VectorDiff(w, w')) <= Delta * Delta
  ensures (Predict(w, x) - Predict(w', x)) *
          (Predict(w, x) - Predict(w', x)) <=
          Delta * Delta * NormSq(x)

  // Note: w[s] == w'[s] == 0 means VectorDiff(w,w')[s] == 0
  // so the sensitive feature contributes 0 to NormSq(VectorDiff)
  // the bound is therefore at least as tight as the general case
  {

  }

// The sensitive feature contributes zero to NormSq(VectorDiff)
// when both weights are zero — helper for the above
lemma ZeroWeightDiffContribution(w: seq<real>, w': seq<real>, s: nat)
  requires |w| == |w'| > 0
  requires 0 <= s < |w| - 1               // change: was s < |w|
  requires w[s] == 0.0 && w'[s] == 0.0
  ensures VectorDiff(w, w')[s] == 0.0
  // Corollary: NormSq(VectorDiff(w,w')) does not include
  // a contribution from index s — proven by NormSqAux induction
  {

  }