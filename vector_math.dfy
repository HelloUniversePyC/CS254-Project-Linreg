// Dot product of two vectors: w·x = sum of w[i] * x[i]
function DotProduct(w: seq<real>, x: seq<real>): real
  requires |w| == |x|
{
  DotProductAux(w, x, 0)
}

// recursive helper that gets the partial dot product starting at index i
function DotProductAux(w: seq<real>, x: seq<real>, i: nat): real
  requires |w| == |x|
  requires i <= |w|
  decreases |w| - i
{
  if i == |w| then 0.0
  else w[i] * x[i] + DotProductAux(w, x, i + 1)
}

// Sum of squares — the only norm concept we need
function NormSq(v: seq<real>): real
  requires |v| > 0
  ensures NormSq(v) >= 0.0
{
  NormSqAux(v, 0)
}

function NormSqAux(v: seq<real>, i: nat): real
  requires i <= |v|
  decreases |v| - i
  ensures NormSqAux(v, i) >= 0.0
{
  if i == |v| then 0.0
  else v[i] * v[i] + NormSqAux(v, i + 1)
}

// Element-wise difference
function VectorDiff(w: seq<real>, w': seq<real>): seq<real>
  requires |w| == |w'|
  ensures |VectorDiff(w, w')| == |w|
  ensures forall i :: 0 <= i < |w| ==> VectorDiff(w, w')[i] == w[i] - w'[i]
{
  seq(|w|, i requires 0 <= i < |w| => w[i] - w'[i])
}

// Squared absolute value — just x*x, but named for clarity
function SqAbs(x: real): real
  ensures SqAbs(x) >= 0.0
  ensures SqAbs(x) == x * x
{
  x * x
}

// Cauchy-Schwarz: (w·x)² ≤ ||w||² · ||x||²
// Everything is a product of reals — no sqrt anywhere
lemma {:axiom} CauchySchwarzSq(w: seq<real>, x: seq<real>)
  requires |w| == |x| > 0
  ensures DotProduct(w, x) * DotProduct(w, x) <=
          NormSq(w) * NormSq(x)

// Supporting inductive lemma for CauchySchwarzSq
// Dafny will likely need this broken out explicitly
lemma {:axiom} CauchySchwarzSqAux(w: seq<real>, x: seq<real>, i: nat)
  requires |w| == |x| > 0
  requires i <= |w|
  decreases |w| - i
  ensures DotProductAux(w, x, i) * DotProductAux(w, x, i) <=
          NormSqAux(w, i) * NormSqAux(x, i)

// NormSq of a difference expands cleanly
// ||w - w'||² = ||w||² - 2(w·w') + ||w'||²
// Useful for bounding VectorDiff without computing it explicitly
lemma NormSqDiffExpansion(w: seq<real>, w': seq<real>)
  requires |w| == |w'| > 0
  ensures NormSq(VectorDiff(w, w')) ==
          NormSq(w) - 2.0 * DotProduct(w, w') + NormSq(w')
{
  NormSqDiffExpansionAux(w, w', 0);
}

lemma NormSqDiffExpansionAux(w: seq<real>, w': seq<real>, i: nat)
  requires |w| == |w'|
  requires i <= |w|
  decreases |w| - i
  ensures NormSqAux(VectorDiff(w, w'), i) ==
          NormSqAux(w, i) - 2.0 * DotProductAux(w, w', i) + NormSqAux(w', i)
{
  if i == |w| {
  } else {
    NormSqDiffExpansionAux(w, w', i + 1);
  }
}

// DotProduct distributes over VectorDiff
// (w - w')·x = w·x - w'·x
lemma DotProductDiff(w: seq<real>, w': seq<real>, x: seq<real>)
  requires |w| == |w'| == |x| > 0
  ensures DotProduct(VectorDiff(w, w'), x) ==
          DotProduct(w, x) - DotProduct(w', x)
{
  DotProductDiffAux(w, w', x, 0);
}

lemma DotProductDiffAux(w: seq<real>, w': seq<real>, x: seq<real>, i: nat)
  requires |w| == |w'| == |x|
  requires i <= |w|
  decreases |w| - i
  ensures DotProductAux(VectorDiff(w, w'), x, i) ==
          DotProductAux(w, x, i) - DotProductAux(w', x, i)
{
  if i == |w| {
  } else {
    DotProductDiffAux(w, w', x, i + 1);
  }
}