// flips (i.e., reverses) array elements in the range [0..num]
method flip (a: array<int>, num: int)

requires 0 <= num < a.Length;
requires a.Length > 0;
requires a != null;

modifies a;

ensures forall i :: 0 <= i <= num ==> a[i] == old(a[num-i]);
ensures forall j :: num < j < a.Length ==> a[j] == old(a[j]);
ensures multiset(a[..]) == multiset(old(a[..]));


{
  var tmp:int;

  var i := 0;
  var j := num;
  while (i < j)

  invariant multiset(a[..]) == multiset(old(a[..]));
  invariant i + j == num;
  invariant forall k :: i <= k <= j ==> a[k] == old(a[k]);
  invariant forall k :: num < k < a.Length ==> a[k] == old(a[k]);
  invariant forall k :: 0 <= k < i ==> a[k] == old(a[num-k]);
  invariant forall k :: j < k <= num ==> a[k] == old(a[num-k]);

  decreases num - i;
  decreases j - i;

  {
    tmp := a[i];
    a[i] := a[j];
    a[j] := tmp;
    i := i + 1;
    j := j - 1;
  }
}
