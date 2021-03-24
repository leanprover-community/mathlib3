/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import algebraic_topology.simplicial_object
import category_theory.yoneda
import category_theory.limits.types
import topology.basic

/-!
A simplicial set is just a simplicial object in `Type`,
i.e. a `Type`-valued presheaf on the simplex category.

(One might be tempted to all these "simplicial types" when working in type-theoretic foundations,
but this would be unnecessarily confusing given the existing notion of a simplicial type in
homotopy type theory.)

We define the standard simplices `Δ[n]` as simplicial sets,
and their boundaries `∂Δ[n]` and horns `Λ[n, i]`.
(The notations are available via `open_locale simplicial`.)

## Future work

There isn't yet a complete API for simplices, boundaries, and horns.
As an example, we should have a function that constructs
from a non-surjective order preserving function `fin n → fin n`
a morphism `Δ[n] ⟶ ∂Δ[n]`.
-/

universes v u

open category_theory

open_locale simplicial

/-- The category of simplicial sets.
This is the category of contravariant functors from
`simplex_category` to `Type u`. -/
@[derive [large_category, limits.has_limits, limits.has_colimits]]
def sSet : Type (u+1) := simplicial_object (Type u)

namespace sSet

/-- The `n`-th standard simplex `Δ[n]` associated with a nonempty finite linear order `n`
is the Yoneda embedding of `n`. -/
def standard_simplex : simplex_category ⥤ sSet := yoneda

localized "notation `Δ[`n`]` := sSet.standard_simplex.obj (simplex_category.mk n)" in simplicial

instance : inhabited sSet := ⟨Δ[0]⟩

section

/-- The `m`-simplices of the `n`-th standard simplex are
the monotone maps from `fin (m+1)` to `fin (n+1)`. -/
def as_preorder_hom (n) (m) (α : Δ[n].obj m) :
  preorder_hom (fin (m.unop.len+1)) (fin (n+1)) := α.to_preorder_hom
end

@[simp]
lemma preorder_hom_of_mk_hom_of_preorder_hom {n m} {f : (fin (n+1)) →ₘ (fin (m+1))} :
  as_preorder_hom m (opposite.op [n]) (simplex_category.mk_hom f) = f := rfl

/-- The boundary `∂Δ[n]` of the `n`-th standard simplex consists of
all `m`-simplices of `standard_simplex n` that are not surjective
(when viewed as monotone function `m → n`). -/
def boundary (n : ℕ) : sSet :=
{ obj := λ m, {α : Δ[n].obj m // ¬ function.surjective (as_preorder_hom _ _ α)},
  map := λ m₁ m₂ f α, ⟨f.unop ≫ (α : Δ[n].obj m₁),
  by { intro h, apply α.property, exact function.surjective.of_comp h }⟩ }

localized "notation `∂Δ[`n`]` := sSet.boundary n" in simplicial

/-- The inclusion of the boundary of the `n`-th standard simplex into that standard simplex. -/
def boundary_inclusion (n : ℕ) :
  ∂Δ[n] ⟶ Δ[n] :=
{ app := λ m (α : {α : Δ[n].obj m // _}), α }

/-- `horn n i` (or `Λ[n, i]`) is the `i`-th horn of the `n`-th standard simplex, where `i : n`.
It consists of all `m`-simplices `α` of `Δ[n]`
for which the union of `{i}` and the range of `α` is not all of `n`
(when viewing `α` as monotone function `m → n`). -/
def horn (n) (i) : sSet :=
{ obj := λ m,
  { α : Δ[n].obj m // set.range (as_preorder_hom _ _ α) ∪ {i} ≠ set.univ },
  map := λ m₁ m₂ f α, ⟨f.unop ≫ (α : Δ[n].obj m₁),
  begin
    intro h, apply α.property,
    rw set.eq_univ_iff_forall at h ⊢, intro j,
    apply or.imp _ id (h j),
    intro hj,
    exact set.range_comp_subset_range _ _ hj,
  end⟩ }

localized "notation `Λ[`n`, `i`]` := sSet.horn n i" in simplicial

def horn_face {n} {i j} (h: i ≠ j) : Λ[n+1,i].obj (opposite.op [n]) :=
⟨simplex_category.δ j,
  begin
    erw preorder_hom_of_mk_hom_of_preorder_hom,
    simp only [order_embedding.to_preorder_hom_coe, ne.def, set.union_singleton],
    rw [fin.range_succ_above j, set.eq_univ_iff_forall, not_forall],
    use j,
    rw set.mem_insert_iff,
    apply not_or,
    { exact (ne.symm h).elim },
    { simp }
  end ⟩

def simplices_of_horn_hom {S} {n} {i} (f : Λ[n+1,i] ⟶ S) :
  set.range i.succ_above → S _[n] :=
begin
  intro j,
  rw fin.range_succ_above i at j,
  have h := j.property,
  simp only [ne.def, set.mem_set_of_eq, subtype.val_eq_coe] at h,
  exact f.app _ (horn_face (ne.symm h)),
end

/-- The inclusion of the `i`-th horn of the `n`-th standard simplex into that standard simplex. -/
def horn_inclusion (n) (i) :
  Λ[n, i] ⟶ Δ[n] :=
{ app := λ m (α : {α : Δ[n].obj m // _}), α }

section examples

open_locale simplicial

/-- The simplicial circle. -/
noncomputable def S1 : sSet :=
limits.colimit $ limits.parallel_pair
  ((standard_simplex.map $ simplex_category.δ 0) : Δ[0] ⟶ Δ[1])
  (standard_simplex.map $ simplex_category.δ 1)

end examples

/-- Truncated simplicial sets. -/
@[derive [large_category, limits.has_limits, limits.has_colimits]]
def truncated (n : ℕ) := simplicial_object.truncated (Type u) n

/-- The skeleton functor on simplicial sets. -/
def sk (n : ℕ) : sSet ⥤ sSet.truncated n := simplicial_object.sk n

instance {n} : inhabited (sSet.truncated n) := ⟨(sk n).obj $ Δ[0]⟩

class fibration {S T : sSet} (f : S ⟶ T) : Prop :=
(lifting :
  ∀ (n : ℕ) (i : fin (n+1)) (a : Λ[n,i] ⟶ S)
    (b : Δ[n] ⟶ T) (h : a ≫ f = horn_inclusion n i ≫ b),
  ∃ g : Δ[n] ⟶ S, g ≫ f = b ∧ horn_inclusion n i ≫ g = a)

lemma is_fibration_iff {S T : sSet} (f : S ⟶ T) :
  fibration f ↔ ∀ ∀ n (k : fin (n+3)) (x : (set.range k.succ_above) → S _[n+1])
    (h1 : ∀ (i j : set.range k.succ_above), i < j → S.δ i (x j) = S.δ (j-1) (x i))
    (h2 : ∃ y, ∀ (i : set.range k.succ_above), T.δ i y = f.app _ (x i) ),
:= begin end

instance (S : sSet) : fibration (nat_trans.id S) :=
⟨begin
  intros n i a b h,
  use b,
  split,
  { ext, simp },
  { rw ← h, ext, simp }
end⟩

end sSet
