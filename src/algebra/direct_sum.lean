/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

-/
import data.dfinsupp

/-!
# Direct sum

This file defines the direct sum of abelian groups, indexed by a discrete type.

## Notation

`⨁ i, β i` is the n-ary direct sum `direct_sum`.
This notation is in the `direct_sum` locale, accessible after `open_locale direct_sum`.

## References

* https://en.wikipedia.org/wiki/Direct_sum
-/

open_locale big_operators

universes u v w u₁

variables (ι : Type v) [dec_ι : decidable_eq ι] (β : ι → Type w) [Π i, add_comm_group (β i)]

/-- `direct_sum β` is the direct sum of a family of additive commutative groups `β i`.

Note: `open_locale direct_sum` will enable the notation `⨁ i, β i` for `direct_sum β`. -/
def direct_sum : Type* := Π₀ i, β i

localized "notation `⨁` binders `, ` r:(scoped f, direct_sum _ f) := r" in direct_sum

namespace direct_sum

variables {ι β}

instance : add_comm_group (⨁ i, β i) :=
dfinsupp.add_comm_group

instance : inhabited (⨁ i, β i) := ⟨0⟩

variables β

include dec_ι

/-- `mk β s x` is the element of `⨁ i, β i` that is zero outside `s`
and has coefficient `x i` for `i` in `s`. -/
def mk (s : finset ι) : (Π i : (↑s : set ι), β i.1) →+ ⨁ i, β i :=
{ to_fun := dfinsupp.mk s,
  map_add' := λ _ _, dfinsupp.mk_add,
  map_zero' := dfinsupp.mk_zero, }

/-- `of i` is the natural inclusion map from `β i` to `⨁ i, β i`. -/
def of (i : ι) : β i →+ ⨁ i, β i :=
{ to_fun := dfinsupp.single i,
  map_add' := λ _ _, dfinsupp.single_add,
  map_zero' := dfinsupp.single_zero }

variables {β}

theorem mk_injective (s : finset ι) : function.injective (mk β s) :=
dfinsupp.mk_injective s

theorem of_injective (i : ι) : function.injective (of β i) :=
λ x y H, congr_fun (mk_injective _ H) ⟨i, by simp⟩

@[elab_as_eliminator]
protected theorem induction_on {C : (⨁ i, β i) → Prop}
  (x : ⨁ i, β i) (H_zero : C 0)
  (H_basic : ∀ (i : ι) (x : β i), C (of β i x))
  (H_plus : ∀ x y, C x → C y → C (x + y)) : C x :=
begin
  apply dfinsupp.induction x H_zero,
  intros i b f h1 h2 ih,
  solve_by_elim
end

variables {γ : Type u₁} [add_comm_group γ]
variables (φ : Π i, β i →+ γ)

variables (φ)
/-- `to_group φ` is the natural homomorphism from `⨁ i, β i` to `γ`
induced by a family `φ` of homomorphisms `β i → γ`. -/
def to_group : (⨁ i, β i) →+ γ :=
{ to_fun := (λ f,
    quotient.lift_on f (λ x, ∑ i in x.2.to_finset, φ i (x.1 i)) $ λ x y H,
    begin
      have H1 : x.2.to_finset ∩ y.2.to_finset ⊆ x.2.to_finset, from finset.inter_subset_left _ _,
      have H2 : x.2.to_finset ∩ y.2.to_finset ⊆ y.2.to_finset, from finset.inter_subset_right _ _,
      refine (finset.sum_subset H1 _).symm.trans ((finset.sum_congr rfl _).trans (finset.sum_subset H2 _)),
      { intros i H1 H2, rw finset.mem_inter at H2, rw H i,
        simp only [multiset.mem_to_finset] at H1 H2,
        rw [(y.3 i).resolve_left (mt (and.intro H1) H2), add_monoid_hom.map_zero] },
      { intros i H1, rw H i },
      { intros i H1 H2, rw finset.mem_inter at H2, rw ← H i,
        simp only [multiset.mem_to_finset] at H1 H2,
        rw [(x.3 i).resolve_left (mt (λ H3, and.intro H3 H1) H2), add_monoid_hom.map_zero] }
    end),
  map_add' := assume f g,
  begin
    refine quotient.induction_on f (λ x, _),
    refine quotient.induction_on g (λ y, _),
    change ∑ i in _, _ = (∑ i in _, _) + (∑ i in _, _),
    simp only, conv { to_lhs, congr, skip, funext, rw add_monoid_hom.map_add },
    simp only [finset.sum_add_distrib],
    congr' 1,
    { refine (finset.sum_subset _ _).symm,
      { intro i, simp only [multiset.mem_to_finset, multiset.mem_add], exact or.inl },
      { intros i H1 H2, simp only [multiset.mem_to_finset, multiset.mem_add] at H2,
        rw [(x.3 i).resolve_left H2, add_monoid_hom.map_zero] } },
    { refine (finset.sum_subset _ _).symm,
      { intro i, simp only [multiset.mem_to_finset, multiset.mem_add], exact or.inr },
      { intros i H1 H2, simp only [multiset.mem_to_finset, multiset.mem_add] at H2,
        rw [(y.3 i).resolve_left H2, add_monoid_hom.map_zero] } }
  end,
  map_zero' := rfl
}

@[simp] lemma to_group_of (i) (x : β i) : to_group φ (of β i x) = φ i x :=
(add_zero _).trans $ congr_arg (φ i) $ show (if H : i ∈ ({i} : finset _) then x else 0) = x,
from dif_pos $ finset.mem_singleton_self i

variables (ψ : (⨁ i, β i) →+ γ)

theorem to_group.unique (f : ⨁ i, β i) :
  ψ f = to_group (λ i, ψ.comp (of β i)) f :=
direct_sum.induction_on f
  (by rw [add_monoid_hom.map_zero, add_monoid_hom.map_zero])
  (λ i x, by rw [to_group_of, add_monoid_hom.comp_apply])
  (λ x y ihx ihy, by rw [add_monoid_hom.map_add, add_monoid_hom.map_add, ihx, ihy])

variables (β)
/-- `set_to_set β S T h` is the natural homomorphism `⨁ (i : S), β i → ⨁ (i : T), β i`,
where `h : S ⊆ T`. -/
-- TODO: generalize this to remove the assumption `S ⊆ T`.
def set_to_set (S T : set ι) (H : S ⊆ T) :
  (⨁ (i : S), β i) →+ (⨁ (i : T), β i) :=
to_group $ λ i, of (β ∘ @subtype.val _ T) ⟨i.1, H i.2⟩
variables {β}

omit dec_ι

/-- The natural equivalence between `⨁ _ : punit, M` and `M`. -/
-- TODO: generalize this to a sum over any type `ι` that is `unique ι`.
protected def id (M : Type v) [add_comm_group M] : (⨁ (_ : punit), M) ≃ M :=
{ to_fun := direct_sum.to_group (λ _, add_monoid_hom.id M),
  inv_fun := of (λ _, M) punit.star,
  left_inv := λ x, direct_sum.induction_on x
    (by rw [add_monoid_hom.map_zero, add_monoid_hom.map_zero])
    (λ ⟨⟩ x, by rw [to_group_of]; refl)
    (λ x y ihx ihy, by rw [add_monoid_hom.map_add, add_monoid_hom.map_add, ihx, ihy]),
  right_inv := λ x, to_group_of _ _ _ }

instance : has_coe_to_fun (⨁ i, β i) :=
dfinsupp.has_coe_to_fun

end direct_sum
