// Sum of squares — the only norm concept we need
function NormSq(v: seq<real>): real
  requires |v| > 0
  decreases |v|
  ensures NormSq(v) >= 0.0
  {

  }

function NormSqAux(v: seq<real>, i: nat): real
  requires i <= |v|
  decreases |v| - i
  ensures NormSqAux(v, i) >= 0.0
  {

  }

// Element-wise difference
function VectorDiff(w: seq<real>, w': seq<real>): seq<real>
  requires |w| == |w'|
  ensures |VectorDiff(w, w')| == |w|
  {

  }

// Squared absolute value — just x*x, but named for clarity
function SqAbs(x: real): real
  ensures SqAbs(x) >= 0.0
  ensures SqAbs(x) == x * x
  {

  }

// Cauchy-Schwarz: (w·x)² ≤ ||w||² · ||x||²
// Everything is a product of reals — no sqrt anywhere
lemma CauchySchwarzSq(w: seq<real>, x: seq<real>)
  requires |w| == |x| > 0
  ensures DotProduct(w, x) * DotProduct(w, x) <=
          NormSq(w) * NormSq(x)
          {

          }

// Supporting inductive lemma for CauchySchwarzSq
// Dafny will likely need this broken out explicitly
lemma CauchySchwarzSqAux(w: seq<real>, x: seq<real>, i: nat)
  requires |w| == |x| > 0
  requires i <= |w|
  decreases |w| - i
  ensures DotProductAux(w, x, i) * DotProductAux(w, x, i) <=
          NormSqAux(w, i) * NormSqAux(x, i)
          {

          }

// NormSq of a difference expands cleanly
// ||w - w'||² = ||w||² - 2(w·w') + ||w'||²
// Useful for bounding VectorDiff without computing it explicitly
lemma NormSqDiffExpansion(w: seq<real>, w': seq<real>)
  requires |w| == |w'| > 0
  ensures NormSq(VectorDiff(w, w')) ==
          NormSq(w) - 2.0 * DotProduct(w, w') + NormSq(w')
          {

          }

// DotProduct distributes over VectorDiff
// (w - w')·x = w·x - w'·x
lemma DotProductDiff(w: seq<real>, w': seq<real>, x: seq<real>)
  requires |w| == |w'| == |x| > 0
  ensures DotProduct(VectorDiff(w, w'), x) ==
          DotProduct(w, x) - DotProduct(w', x)
          {

          }