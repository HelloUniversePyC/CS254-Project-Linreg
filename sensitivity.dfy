include "linreg_base_case.dfy"
include "vector_math.dfy"
include "linreg_noisy.dfy"

//Claim(s):
// Conclusion 1: OutputSensitivity
//   How much can predictions shift between adjacent models?
//   bounded by Delta() * ||x|| for any weight vector w — no zero-weight assumption
//   this is what DP noise must overcome to hide membership
//
// Conclusion 2: BoundedSensitiveLeakage
//   How much does the sensitive feature leak through noisy predictions?
//   exactly (w[s] - d[s])^2 * (x[s] - x'[s])^2 for any w[s] <- we show a specific value for what the leakage is
//   when d[s] = w[s]: leakage is zero regardless of what w[s] is —the DP guarantee <- DP noise eqaul to sensitive weight
//   when d[s] = 0:    leakage is w[s]^2 * (x[s]-x'[s])^2 — full exposure, no protection<- no DP noise
//   the zero-weight case (w[s] = 0) is a trivial corollary, not the general result

// Sensitivity constant: axiomatized as a function so we can
// express Delta() > 0 as a postcondition without committing to
// a specific value->Justified by Chaudhuri et al. 2011<- this article says its a property of the training algorithm not a specific weight
function {:axiom} Delta(): real
  ensures Delta() > 0.0

// Predict(w, x) == DotProduct(w, x)
// Dafny can't see this automatically because Predict uses PredictAux
// and DotProduct uses DotProductAux — they need to be connected explicitly
//Inference IS a Dot product
lemma PredictEqDotProduct(w: seq<real>, x: seq<real>)
  requires |w| == |x|
  ensures Predict(w, x) == DotProduct(w, x)
{
  PredictEqDotProductAux(w, x, 0);
}

lemma PredictEqDotProductAux(w: seq<real>, x: seq<real>, i: nat)
  requires |w| == |x|
  requires i <= |w|
  decreases |w| - i

  ensures PredictAux(w, x, i) == DotProductAux(w, x, i)
{
  if i == |w| {
  } else {
    PredictEqDotProductAux(w, x, i + 1);
  }
}

// (Predict(w,x) - Predict(w',x))^2 ≤ Delta()^2 · ||x||^2
// pen-and-paper reads as: |Predict(w,x) - Predict(w',x)| ≤ Delta()·||x||
// the sqrt step is noted in the writeup, not mechanized
//Note that we no longer have to zero the sensitive weight, any weight can be used
lemma OutputSensitivity(w: seq<real>, w': seq<real>, x: seq<real>)
  requires |w| == |w'| == |x| > 0
  requires ValidFeatureVector(x)
  requires NormSq(VectorDiff(w, w')) <= Delta() * Delta()
  ensures (Predict(w, x) - Predict(w', x)) *
          (Predict(w, x) - Predict(w', x)) <=
          Delta() * Delta() * NormSq(x)
{
  var diff := VectorDiff(w, w');

  // Step 1: connect Predict to DotProduct for all three vectors
  PredictEqDotProduct(w, x);
  PredictEqDotProduct(w', x);
  PredictEqDotProduct(diff, x);

  // Step 2: now Dafny knows Predict(w,x) == DotProduct(w,x) etc.
  // so the difference equals DotProduct(diff, x)
  DotProductDiff(w, w', x);
  assert Predict(w, x) - Predict(w', x) == DotProduct(diff, x);

  // Step 3: Cauchy-Schwarz
  CauchySchwarzSq(diff, x);

  // Step 4: chain the inequalities
  // DotProduct(diff,x)² ≤ NormSq(diff) * NormSq(x) ≤ Delta()² * NormSq(x)
}

// When two inputs differ only on feature s, the squared noisy
// prediction difference equals exactly (w[s]-d[s])^2 * (x[s]-x'[s])^2.
// This holds for ANY w[s], not just zero.
lemma BoundedSensitiveLeakage(w: seq<real>, x: seq<real>, x': seq<real>,
                               d: seq<real>, s: nat)
  requires |w| == |x| == |x'| == |d| > 0
  requires ValidFeatureVector(x) && ValidFeatureVector(x')
  requires 0 <= s < |w| - 1
  requires forall i :: 0 <= i < |w| && i != s ==> x[i] == x'[i]
  ensures (PredictWithNoise(w, x, d).Observed() -
           PredictWithNoise(w, x', d).Observed()) *
          (PredictWithNoise(w, x, d).Observed() -
           PredictWithNoise(w, x', d).Observed()) ==
          (w[s] - d[s]) * (w[s] - d[s]) *
          (x[s] - x'[s]) * (x[s] - x'[s])
{
  // 1)connect Predict to DotProduct so Z3 SMT solver can reason about the algebra
  PredictEqDotProduct(w, x);
  PredictEqDotProduct(w, x');
  PredictEqDotProduct(d, x);
  PredictEqDotProduct(d, x');

  // 2) (w-d)·x = w·x - d·x, and same for x'
  // lets us rewrite Observed() differences in terms of VectorDiff(w,d)
  DotProductDiff(w, d, x);
  DotProductDiff(w, d, x');

  // 3) since x and x' agree everywhere except s,
  // the dot product difference collapses to a single scalar term:
  // DotProduct(VectorDiff(w,d), x) - DotProduct(VectorDiff(w,d), x') == (w[s]-d[s])*(x[s]-x'[s])
  BoundedSensitiveLeakageAux(w, d, x, x', s);

  //4) expand Observed() = clean + delta = Predict(w,x) - Predict(d,x)
  // and rewrite the difference of noisy predictions as a difference of dot products
  var lhs := PredictWithNoise(w, x, d).Observed() - PredictWithNoise(w, x', d).Observed();
  assert lhs == Predict(w, x) - Predict(d, x) - (Predict(w, x') - Predict(d, x'));

  // 5) substitute Predict == DotProduct (established in Step 1)
  assert lhs == DotProduct(w, x) - DotProduct(d, x) - (DotProduct(w, x') - DotProduct(d, x'));

  // 6) regroup into VectorDiff(w,d) dot products — sets up Step 3's result
  assert lhs == DotProduct(VectorDiff(w, d), x) - DotProduct(VectorDiff(w, d), x');

  // 7) apply Step 3 — only the s-th term survives since x and x' agree elsewhere
  assert lhs == (w[s] - d[s]) * (x[s] - x'[s]);

  // 8) square both sides to get the final ensures
  // this is the exact leakage: zero when d[s]=w[s], full when d[s]=0
  assert lhs * lhs == (w[s] - d[s]) * (w[s] - d[s]) * (x[s] - x'[s]) * (x[s] - x'[s]);
}
// Aux: isolates the single-index contribution of (w-d)·(x-x')
// when x and x' agree everywhere except s
//Everything cancels via precondition except the term where x[s] and x[s'] differ
lemma BoundedSensitiveLeakageAux(w: seq<real>, d: seq<real>,
                                  x: seq<real>, x': seq<real>, s: nat)
  requires |w| == |d| == |x| == |x'| > 0
  requires 0 <= s < |w|
  requires forall i :: 0 <= i < |w| && i != s ==> x[i] == x'[i]
  ensures DotProduct(VectorDiff(w, d), x) - DotProduct(VectorDiff(w, d), x') ==
          (w[s] - d[s]) * (x[s] - x'[s])
{
  BoundedSensitiveLeakageAuxInductive(w, d, x, x', s, 0);
}

lemma BoundedSensitiveLeakageAuxInductive(w: seq<real>, d: seq<real>,
                                           x: seq<real>, x': seq<real>,
                                           s: nat, i: nat)
  requires |w| == |d| == |x| == |x'|
  requires 0 <= s < |w|
  requires i <= |w|
  requires forall j :: 0 <= j < |w| && j != s ==> x[j] == x'[j]
  decreases |w| - i
  ensures DotProductAux(VectorDiff(w, d), x, i) - DotProductAux(VectorDiff(w, d), x', i) ==
          (if i <= s < |w| then (w[s] - d[s]) * (x[s] - x'[s]) else 0.0)
{
  if i == |w| {
  } else if i == s {
    BoundedSensitiveLeakageAuxInductive(w, d, x, x', s, i + 1);
  } else {
    assert x[i] == x'[i];
    BoundedSensitiveLeakageAuxInductive(w, d, x, x', s, i + 1);
  }
}

//Documentation
// Variables:
//   w  — model weight vector, w[s] is how much the model relies on the sensitive feature (ex: race, gender)
//   x, x' — two feature vectors that agree everywhere except at index s (secret index)
//   d  — DP noise vector, added deliberately to the prediction to obscure w
//        d[s] is the noise component on the sensitive feature specifically
//        when d[s] = w[s]: noise exactly cancels w[s]*x[s] in the output — zero leakage
//        when d[s] = 0:    no noise on the sensitive feature — full leakage
//   s  — index of the sensitive feature in the weight and feature vectors
//        constrained to s < |w| - 1 to exclude the bias term (last index)
//   Delta() — sensitivity bound on the model: ||w - w'|| <= Delta()
//             justified by Chaudhuri et al. 2011 as a property of the training algorithm
//             not a property of any individual weight — holds for any w