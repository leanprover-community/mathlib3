/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning and Patrick Lutz
-/

import field_theory.subfield
import field_theory.separable
import linear_algebra.finite_dimensional
import field_theory.tower

/-!
# Adjoining Elements to Fields

In this file we introduce the notion of adjoining elements to fields.
This isn't quite the same as adjoining elements to rings.
For example, `algebra.adjoin K {x}` might not include `x⁻¹`.

## Main results

(This is just a start; we've got more to add, including a proof of the Primitive Element Theorem.)

- `adjoin_adjoin_left`: adjoining S and then T is the same as adjoining S ∪ T.

## Notation

 - `F⟮α⟯`: adjoin a single element `α` to `F`.
-/

namespace field
variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (S : set E)

/--
`adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`.
-/
def adjoin : subalgebra F E :=
{ carrier :=
  { carrier := field.closure (set.range (algebra_map F E) ∪ S),
    one_mem' := is_submonoid.one_mem,
    mul_mem' := λ x y, is_submonoid.mul_mem,
    zero_mem' := is_add_submonoid.zero_mem,
    add_mem' := λ x y, is_add_submonoid.add_mem },
  algebra_map_mem' := λ x, field.mem_closure (or.inl (set.mem_range.mpr ⟨x,rfl⟩)) }

lemma adjoin.algebra_map_mem (x : F) : algebra_map F E x ∈ adjoin F S :=
field.mem_closure (or.inl (set.mem_range_self x))

lemma subset_adjoin_of_subset_left {F : set E} {HF : is_subfield F} {T : set E} (HT : T ⊆ F) :
  T ⊆ adjoin F S :=
λ x hx, adjoin.algebra_map_mem F S ⟨x, HT hx⟩

lemma adjoin.range_algebra_map_subset : set.range (algebra_map F E) ⊆ adjoin F S :=
begin
  intros x hx,
  cases hx with f hf,
  rw ← hf,
  exact adjoin.algebra_map_mem F S f,
end

instance adjoin.field_coe : has_coe_t F (adjoin F S) :=
{coe := λ x, ⟨algebra_map F E x, adjoin.algebra_map_mem F S x⟩}

lemma subset_adjoin : S ⊆ adjoin F S :=
λ x hx, field.mem_closure (or.inr hx)

instance adjoin.set_coe : has_coe_t S (adjoin F S) :=
{coe := λ x, ⟨x,subset_adjoin F S (subtype.mem x)⟩}

lemma adjoin.mono (T : set E) (h : S ⊆ T) : (adjoin F S : set E) ⊆ adjoin F T :=
field.closure_mono (set.union_subset (set.subset_union_left _ _) (set.subset_union_of_subset_right h _))

instance adjoin.is_subfield : is_subfield (adjoin F S : set E) := field.closure.is_subfield

--Lean has trouble figuring this out on its own
instance adjoin.is_field : field (adjoin F S) := @is_subfield.field E _ ((adjoin F S) : set E) _

lemma adjoin_contains_field_as_subfield (F : set E) {HF : is_subfield F} : F ⊆ adjoin F S :=
λ x hx, adjoin.algebra_map_mem F S ⟨x, hx⟩

lemma subset_adjoin_of_subset_right {T : set E} (H : T ⊆ S) : T ⊆ adjoin F S :=
begin
  intros x hx,
  exact subset_adjoin F S (H hx),
end

/-- If `K` is a field with `F ⊆ K` and `S ⊆ K` then `adjoin F S ⊆ K`. -/
lemma adjoin_subset_subfield {K : set E} [is_subfield K] (HF : set.range (algebra_map F E) ⊆ K)
  (HS : S ⊆ K) : (adjoin F S : set E) ⊆ K :=
begin
  apply field.closure_subset,
  rw set.union_subset_iff,
  exact ⟨HF, HS⟩,
end

/-- `S ⊆ adjoin F T` if and only if `adjoin F S ⊆ adjoin F T`. -/
lemma adjoin_subset_iff {T : set E} : S ⊆ adjoin F T ↔ (adjoin F S : set E) ⊆ adjoin F T :=
⟨λ h, adjoin_subset_subfield F S (adjoin.range_algebra_map_subset F T) h,
  λ h, set.subset.trans (subset_adjoin F S) h⟩

lemma subfield_subset_adjoin_self {F : set E} {HF : is_subfield F} {T : set E} {HT : T ⊆ F} :
  T ⊆ adjoin F S :=
λ x hx, adjoin.algebra_map_mem F S ⟨x,HT hx⟩

lemma adjoin_subset_adjoin_iff {F' : Type*} [field F'] [algebra F' E]
  {S S' : set E} : (adjoin F S : set E) ⊆ adjoin F' S' ↔
  set.range (algebra_map F E) ⊆ adjoin F' S' ∧ S ⊆ adjoin F' S' :=
⟨λ h, ⟨trans (adjoin.range_algebra_map_subset _ _) h, trans (subset_adjoin _ _) h⟩,
  λ ⟨hF, hS⟩, field.closure_subset (set.union_subset hF hS)⟩

/-- `F[S][T] = F[S ∪ T]` -/
lemma adjoin_adjoin_left (T : set E) : (adjoin (adjoin F S : set E) T : set E) = adjoin F (S ∪ T) :=
begin
  apply set.eq_of_subset_of_subset; rw adjoin_subset_adjoin_iff; split,
  { exact algebra.set_range_subset (adjoin.mono _ _ _ (set.subset_union_left _ _)) },
  { exact subset_adjoin_of_subset_right _ _ (set.subset_union_right _ _) },
  { exact subset_adjoin_of_subset_left _ (adjoin.range_algebra_map_subset _ _) },
  { exact set.union_subset
            (subset_adjoin_of_subset_left _ (subset_adjoin _ _))
            (subset_adjoin _ _) },
end

--this definition of notation is courtesy of Kyle Miller on zulip
class fancy_insert {α : Type*} (s : set α) :=
(insert : α → set α)

@[priority 1000]
instance fancy_insert_empty {α : Type*} : fancy_insert (∅ : set α) :=
{ insert := λ x, @singleton _ _ set.has_singleton x }

@[priority 900]
instance fancy_insert_nonempty {α : Type*} (s : set α) : fancy_insert s :=
{ insert := λ x, set.insert x s }

notation K`⟮`:std.prec.max_plus l:(foldr `, ` (h t, fancy_insert.insert t h) ∅) `⟯` := adjoin K l

variables (α : E)

lemma mem_adjoin_simple_self : α ∈ F⟮α⟯ :=
 subset_adjoin F {α} (set.mem_singleton α)

/-- generator of `F⟮α⟯` -/
def adjoin_simple.gen : F⟮α⟯ := ⟨α, mem_adjoin_simple_self F α⟩

lemma adjoin_simple.algebra_map_gen : algebra_map F⟮α⟯ E (adjoin_simple.gen F α) = α := rfl

section
open finite_dimensional

/-- If a subset of a set is infinite then the set is infinite. -/
lemma inf_of_subset_inf {X : Type*} {s : set X} {t : set X} (hst : s ⊆ t) (hs : s.infinite) : t.infinite :=
mt (λ ht, ht.subset hst) hs

def submodule_restrict_field (S : set E) (p : submodule (adjoin F S) E) : submodule F E := {
    carrier := p.carrier,
    zero_mem' := p.zero_mem',
    add_mem' := p.add_mem',
    smul_mem' :=
    begin
        intros c x hx,
        rw algebra.smul_def,
        rw is_scalar_tower.algebra_map_eq F (adjoin F S) E,
        rw ring_hom.comp_apply,
        rw ←algebra.smul_def,
        exact p.smul_mem' _ hx,
    end
}

/-- If the generator is not in the inclusion of F in E then it's also not in the inclusion of
    F in F[α]. -/
lemma adjoin_simple_gen_nontrivial {α : E} (hα : α ∉ set.range (algebra_map F E)) :
    adjoin_simple.gen F α ∉ set.range (algebra_map F F⟮α⟯) :=
begin
    revert hα,
    contrapose!,
    rintros ⟨x, hx⟩,
    injections_and_clear,
    use x, assumption,
end

/-- If E is a finite extension of F then it is also a finite extension of F adjoin alpha. -/
instance adjoin_findim_of_findim [F_findim : finite_dimensional F E] (α : E) :
    finite_dimensional F⟮α⟯ E :=
begin
    rw iff_fg,
    rw submodule.fg_iff_finite_dimensional,
    cases (finite_dimensional.exists_is_basis_finite F E) with B hB,
    have key : submodule.span F⟮α⟯ B = ⊤,
    {   ext,
        simp only [submodule.mem_top, iff_true],
        have hx : x ∈ submodule.span F (set.range coe),
        {   rw hB.1.2,
            exact submodule.mem_top, },
        rw submodule.mem_span,
        intros p hp,
        rw submodule.mem_span at hx,
        apply hx (submodule_restrict_field F {α} p),
        rw subtype.range_coe,
        exact hp, },
    rw ← key,
    apply finite_dimensional.span_of_finite F⟮α⟯ hB.2,
end

instance adjoin_findim_of_findim_base [F_findim : finite_dimensional F E] (α : E) :
    finite_dimensional F F⟮α⟯ :=
finite_dimensional.finite_dimensional_submodule (F⟮α⟯ : submodule F E)

/-- If the field extension E has an element not in the base field F then the degree of E over F is
    greater than 1. -/
lemma algebra_findim_lt [hF : finite_dimensional F E] : (∃ x : E, x ∉ set.range (algebra_map F E)) →
    1 < findim F E :=
begin
    contrapose!,
    intros E_dim x,
    have : 0 < findim F E := findim_pos_iff_exists_ne_zero.mpr ⟨1, one_ne_zero⟩,
    replace E_dim : findim F E = 1 := by omega,
    set s : set E := {1} with hs,
    have : fintype s := unique.fintype,
    have s_lin_ind : linear_independent F (coe : s → E) := linear_independent_singleton one_ne_zero,
    have s_card : s.to_finset.card = findim F E := by change s.to_finset.card with 1; rw E_dim,
    obtain ⟨_, s_spans⟩ := set_is_basis_of_linear_independent_of_card_eq_findim s_lin_ind s_card,
    have x_in_span_one : x ∈ submodule.span F s :=
    begin
        rw subtype.range_coe at s_spans,
        rw s_spans,
        exact submodule.mem_top,
    end,
    obtain ⟨a, ha⟩ := submodule.mem_span_singleton.mp x_in_span_one,
    exact ⟨a, by rw [← ha, algebra.smul_def, mul_one]⟩,
end

/-- Adjoining an element from outside of F strictly decreases the degree of a finite extension. -/
lemma adjoin_dim_lt [hF : finite_dimensional F E] {α : E} (hα : α ∉ set.range (algebra_map F E)) :
    findim F⟮α⟯ E < findim F E :=
begin
  rw ← findim_mul_findim F F⟮α⟯ E,
  have : 0 < findim F⟮α⟯ E := findim_pos_iff_exists_ne_zero.mpr ⟨1, one_ne_zero⟩,
  have : adjoin_simple.gen F α ∉ set.range (algebra_map F F⟮α⟯) := adjoin_simple_gen_nontrivial F hα,
  have : findim F F⟮α⟯ > 1 := algebra_findim_lt F (by tauto),
  nlinarith,
end

/-- If F is infinite then its inclusion into E is infinite. -/
lemma inclusion.infinite (hF : infinite F) : (set.range (algebra_map F E)).infinite :=
begin
  apply set.infinite_coe_iff.mp,
  apply infinite.of_injective (set.range_factorization (algebra_map F E)),
  exact subtype.coind_injective (λ (a : F), set.mem_range_self a) ((algebra_map F E).injective),
end

lemma adjoin_inf_of_inf (S : set E) (hF : infinite F) : infinite (adjoin F S) :=
set.infinite_coe_iff.mpr (inf_of_subset_inf (adjoin.range_algebra_map_subset F S) (inclusion.infinite F hF))

end

end field
