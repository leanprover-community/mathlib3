import algebra.direct_sum_graded

namespace add_monoid_algebra

noncomputable theory
open_locale direct_sum

variables (k G : Type*) [semiring k] [add_monoid G] [decidable_eq G]

variables {G}

/-- A shorthand for the `add_monoid_hom.mrange` of `finsupp.single` -/
@[derive add_comm_monoid]
abbreviation single_mrange (i : G) : add_submonoid (add_monoid_algebra k G) :=
(finsupp.single_add_hom i).mrange

/-- Typeclass resolution can't find this for some reason, it is needed by the `≃+` to state
`finsupp.equiv_dfinsupp_single_submonoid`. -/
instance single_mrange.to_add_comm_monoid :
  add_comm_monoid (Π₀ (i : G), single_mrange k i) :=
@dfinsupp.add_comm_monoid G (λ i, single_mrange k i) _

instance single_mrange.gmonoid : direct_sum.gmonoid (λ i : G, single_mrange k i) :=
direct_sum.gmonoid.of_add_submonoids _ ⟨1, rfl⟩ $ λ i j gi gj, begin
  obtain ⟨_, gi, rfl⟩ := gi,
  obtain ⟨_, gj, rfl⟩ := gj,
  refine ⟨gi * gj, single_mul_single.symm⟩,
end

/-- An intermediate result before getting to `direct_sum_mrange`. -/
def to_direct_sum_mrange' : add_monoid_algebra k G ≃+ ⨁ i : G, single_mrange k i :=
begin
  letI : add_zero_class (Π₀ (i : G), k) := @dfinsupp.add_zero_class G (λ _, k) _,
  letI : add_zero_class (Π₀ (i : G), single_mrange k i) := @dfinsupp.add_zero_class G (λ i, single_mrange k i) _,
  have : (G →₀ k) ≃+ Π₀ i : G, k := finsupp.to_dfinsupp_add_equiv,
  refine (finsupp.to_dfinsupp_add_equiv : (G →₀ k) ≃+ Π₀ i : G, k).trans _,
  refine @dfinsupp.map_range.add_equiv G (λ _, k) (λ i, single_mrange k i) _ _ _,
  exact λ i, {
    to_fun := (finsupp.single_add_hom i).mrange_restrict,
    inv_fun := λ x, x.1 i,
    left_inv := λ x, finsupp.single_eq_same,
    right_inv := λ x, subtype.coe_injective $ begin
      obtain ⟨_, xi, rfl⟩ := x,
      simp [finsupp.single_eq_same],
    end,
    ..(finsupp.single_add_hom i).mrange_restrict
  },
end

lemma to_direct_sum_mrange'_single (i : G) (x : k):
  to_direct_sum_mrange' k (show add_monoid_algebra k G, from finsupp.single i x) =
    direct_sum.of _ i (⟨finsupp.single i x, x, rfl⟩ : single_mrange k i) :=
begin
  classical,
  simp [to_direct_sum_mrange', finsupp.to_dfinsupp_add_equiv_apply,
      finsupp.to_dfinsupp_single, direct_sum.of],
  congr,
end

/-- There is a ring equivalence between an `add_monoid_algebra` (e.g. a `polnomial`) and
the direct sum of `single_mrange k i` (e.g. the monomials of degree `i`). -/
def to_direct_sum_mrange : add_monoid_algebra k G ≃+* ⨁ i : G, single_mrange k i :=
{ to_fun := to_direct_sum_mrange' k,
  map_mul' := λ f g, begin
    -- nasty `change` tricks to get things to a point where we can use `ext`. `induction` on `f`
    -- and `g` may be easier.
    change (to_direct_sum_mrange' k).to_add_monoid_hom.comp (add_monoid_hom.mul_left f) g =
      (add_monoid_hom.mul_left $
        (to_direct_sum_mrange' k) f).comp (to_direct_sum_mrange' k).to_add_monoid_hom g,
    apply add_monoid_hom.congr_fun,
    ext gi gx: 2,
    let g : add_monoid_algebra k G:= finsupp.single gi gx,
    change (to_direct_sum_mrange' k).to_add_monoid_hom.comp (add_monoid_hom.mul_right g) f =
      (add_monoid_hom.mul_right $
        (to_direct_sum_mrange' k) g).comp (to_direct_sum_mrange' k).to_add_monoid_hom f,
    apply add_monoid_hom.congr_fun,
    ext fi fx : 2,
    let f : add_monoid_algebra k G := finsupp.single fi fx,
    change (to_direct_sum_mrange' k) (f * g) =
      (to_direct_sum_mrange' k) f * (to_direct_sum_mrange' k) g,

    -- now that we just have to prove the result on `single` its easy!
    simp only [f, g, single_mul_single, to_direct_sum_mrange'_single, direct_sum.of_mul_of],
    congr,
    simp only [subtype.coe_mk, single_mul_single],
  end,
  ..to_direct_sum_mrange' k}

end add_monoid_algebra
