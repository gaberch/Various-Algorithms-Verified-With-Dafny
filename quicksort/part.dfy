include "preds.dfy"

method choose(l:nat, u:nat) returns (rv: nat)
  requires l <= u;
  ensures l <= rv <= u;
{assume(l <= rv <= u);}

method partition(a:array<int>, l:nat, u:nat) returns (pivot:int)
  modifies a;
  requires a != null && a.Length > 0
  requires 0 <= l <= u < a.Length;
  requires 0 < l <= u <= a.Length - 1 ==> partitioned(a, 0, l-1, l, a.Length - 1);
  requires 0 <= l <= u < a.Length - 1 ==> partitioned(a, l, u, u+1, a.Length-1);

  ensures 0 <= l <= pivot <= u < a.Length;

  ensures l > 0 ==> beq(old(a[..]), a[..], 0, l-1);
  ensures 0 < l <= u <= a.Length - 1 ==> partitioned(a, 0, l-1, l, a.Length - 1);

  ensures u < a.Length - 1 ==> beq(old(a[..]), a[..], u+1, a.Length - 1);
  ensures 0 <= l <= u < a.Length - 1 ==> partitioned(a, l, u, u+1, a.Length-1);

  ensures pivot > l ==> partitioned(a, 0, pivot-1, pivot, pivot);
  ensures pivot < u ==> partitioned(a, 0, pivot, pivot+1, a.Length - 1);


{
  var pi := choose(l, u);
  var pv := a[pi];

  a[pi] := a[u];
  a[u] := pv;

  var i:int := l - 1;
  var j := l;
  while (j < u)

    invariant l - 1 <= i < j <= u;
    invariant 0 < l <= u <= a.Length - 1 ==> partitioned(a,0,l-1,l,u);
    invariant l > 0 ==> beq(old(a[..]), a[..], 0, l-1);
    invariant 0 <= l <= u < a.Length - 1 ==> partitioned(a, l, u, u+1, a.Length-1);
    invariant u < a.Length - 1 ==> beq(old(a[..]), a[..], u+1, a.Length - 1);
    invariant pv == a[u];
    invariant forall k :: l <= k <= i ==> a[k] <= pv;
    invariant forall k :: i < k < j ==> pv < a[k];

    decreases u - j
    
  {
    if (a[j] <= pv)
    {
      i := i + 1;
      var t := a[i];
      a[i] := a[j];
      a[j] := t;
    }
    j := j + 1;
  }

  pivot := i + 1;
  var t := a[pivot];
  a[pivot] := a[u];
  a[u] := t;
}
