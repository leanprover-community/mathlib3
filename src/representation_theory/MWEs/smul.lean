import algebra.monoid_algebra.basic
noncomputable theory
namespace ITP

variables {k : Type*} [comm_ring k] {G : Type*} [group G]

/- Suppose we were to do group cohomology with `k[G]`-modules. We would want to use, for example,
the `k[G]`-action on a `k`-module `M` induced by a `G`-action on `M`, defined by
`(∑ rᵢ⬝gᵢ)⬝m := ∑ rᵢ⬝(gᵢ⬝m).` -/
instance {k : Type*} [comm_ring k] {G : Type*} [group G] {M : Type*}
  [add_comm_group M] [has_smul G M] [module k M] :
  has_smul (monoid_algebra k G) M :=
{ smul := λ g m, finsupp.total G _ k (λ g, g • m) g }
/- (The type `monoid_algebra k G` is a nickname for `finsupp G k`, aka `k[G]`, but which
knows about the multiplication in `k[G]` induced by the multiplication in `G`). -/

/- We make a lemma unfolding the above definition. -/
lemma smul_def {M : Type*} [add_comm_group M] [has_smul G M] [module k M]
  (g : monoid_algebra k G) (m : M) :
  g • m = finsupp.total G _ k (λ g, g • m) g := rfl

/- However, when `G = kˣ` and `M = k[kˣ]`, for instance, the resulting action of `k[kˣ]` on
itself is different from the one induced by multiplication in `k[kˣ].` -/

/- Considering `r, s : kˣ` as elements of `k[kˣ]`, `r * s` is the function supported at
`r * s` with the value 1. Meanwhile, our instance would declare `r • s` to be the function
supported at `s` with value `r`. Let's see which instance Lean picks. -/
example (r s : kˣ) :
  monoid_algebra.of k kˣ r • monoid_algebra.of k kˣ s
    = monoid_algebra.of k kˣ r * monoid_algebra.of k kˣ s :=
sorry -- `rfl' fails; Lean didn't synthesise the multiplication instance!

-- Instead let's evaluate the expression at s:
example (r s : kˣ) :
  (monoid_algebra.of k kˣ r • monoid_algebra.of k kˣ s) s = r :=
begin
  simp only [smul_def, monoid_algebra.of_apply, finsupp.smul_single, finsupp.total_single,
    finsupp.smul_single', mul_smul_one, finsupp.single_eq_same, units.smul_def, mul_one, one_mul],
end

end ITP
