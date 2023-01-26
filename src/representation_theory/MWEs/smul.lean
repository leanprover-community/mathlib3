import algebra.monoid_algebra.basic
noncomputable theory
namespace ITP

variables {k : Type*} [semiring k]

/- We try and extend a `G`-action on `M` to the `k[G]`-action sending
`∑ nᵢgᵢ ⬝ m := ∑ nᵢ ⬝ (gᵢ ⬝ m)`, in the maximum generality possible. -/
instance {k : Type*} [semiring k] {G : Type*} {M : Type*}
  [add_comm_monoid M] [has_smul G M] [module k M] :
  has_smul (monoid_algebra k G) M :=
{ smul := λ g m, finsupp.total G _ k (λ g, g • m) g }
/- (The type `monoid_algebra k G` is a nickname for `finsupp G k`, aka `k[G]`, but which
knows about the multiplication in `k[G]` induced by the multiplication in `G`) -/

/- But the assumptions in our instance are weak enough to allow `G := k, M := k[k]`, and the
resulting action of `k[k]` on itself is different from multiplication. -/

/- Considering `r, s : k` as elements of `k[k]`, `r * s` is the function supported at
`r * s` with the value 1. Meanwhile, our instance would declare `r • s` to be the function
supported at `s` with value `r`. Let's see which instance Lean picks. -/
example (r s : k) :
  monoid_algebra.of k k r • monoid_algebra.of k k s
    = monoid_algebra.of k k r * monoid_algebra.of k k s :=
sorry -- `rfl' fails; Lean didn't synthesise the multiplication instance!

-- Instead let's evaluate the expression at s:
example (r s : k) :
  (monoid_algebra.of k k r • monoid_algebra.of k k s) s = r :=
begin
  show finsupp.total k _ k (λ x, x • monoid_algebra.of k k s) _ _ = _,
  simp,
end

/- Of course, we could avoid this particular conflict by strengthening the assumptions, but this
will not always be possible. Moreover, this demonstrates that the "make definitions as general as
possible" has exceptions. -/

end ITP
