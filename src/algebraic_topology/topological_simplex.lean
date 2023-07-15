/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Adam Topaz
-/
import algebraic_topology.simplex_category
import topology.category.Top.basic
import topology.instances.nnreal

/-!
# Topological simplices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the natural functor from `simplex_category` to `Top` sending `[n]` to the
topological `n`-simplex.
This is used to define `Top.to_sSet` in `algebraic_topology.simpliciaL_set`.
-/

noncomputable theory

namespace simplex_category

open_locale simplicial nnreal big_operators classical

local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

/-- The topological simplex associated to `x : simplex_category`.
  This is the object part of the functor `simplex_category.to_Top`. -/
def to_Top_obj (x : simplex_category) := { f : x → ℝ≥0 | ∑ i, f i = 1 }

instance (x : simplex_category) : has_coe_to_fun x.to_Top_obj (λ _, x → ℝ≥0) :=
⟨λ f, (f : x → ℝ≥0)⟩

@[ext]
lemma to_Top_obj.ext {x : simplex_category} (f g : x.to_Top_obj) :
  (f : x → ℝ≥0) = g → f = g := subtype.ext

/-- A morphism in `simplex_category` induces a map on the associated topological spaces. -/
def to_Top_map {x y : simplex_category} (f : x ⟶ y) : x.to_Top_obj → y.to_Top_obj :=
λ g, ⟨λ i, ∑ j in (finset.univ.filter (λ k, f k = i)), g j,
begin
  simp only [finset.filter_congr_decidable, finset.sum_congr, to_Top_obj, set.mem_set_of],
  rw ← finset.sum_bUnion,
  convert g.2,
  { rw finset.eq_univ_iff_forall,
    intros i,
    rw finset.mem_bUnion,
    exact ⟨f i, by simp, by simp⟩ },
  { intros i hi j hj h,
    rw [function.on_fun, disjoint_iff_inf_le],
    intros e he,
    apply h,
    simp only [true_and, finset.inf_eq_inter,
      finset.mem_univ, finset.mem_filter, finset.mem_inter] at he,
    rw [← he.1, ← he.2] }
end⟩

@[simp]
lemma coe_to_Top_map {x y : simplex_category} (f : x ⟶ y) (g : x.to_Top_obj) (i : y) :
  to_Top_map f g i = ∑ j in (finset.univ.filter (λ k, f k = i)), g j := rfl

@[continuity]
lemma continuous_to_Top_map {x y : simplex_category} (f : x ⟶ y) :
  continuous (to_Top_map f) :=
continuous.subtype_mk (continuous_pi $ λ i, continuous_finset_sum _ $
  λ j hj, (continuous_apply _).comp continuous_subtype_val) _

/-- The functor associating the topological `n`-simplex to `[n] : simplex_category`. -/
@[simps]
def to_Top : simplex_category ⥤ Top :=
{ obj := λ x, Top.of x.to_Top_obj,
  map := λ x y f, ⟨to_Top_map f⟩,
  map_id' := begin
    intros x,
    ext f i : 3,
    change (finset.univ.filter (λ k, k = i)).sum _ = _,
    simp [finset.sum_filter]
  end,
  map_comp' := begin
    intros x y z f g,
    ext h i : 3,
    dsimp,
    erw ← finset.sum_bUnion,
    apply finset.sum_congr,
    { exact finset.ext (λ j, ⟨λ hj, by simpa using hj, λ hj, by simpa using hj⟩) },
    { tauto },
    { intros j hj k hk h,
      rw [function.on_fun, disjoint_iff_inf_le],
      intros e he,
      apply h,
      simp only [true_and, finset.inf_eq_inter,
        finset.mem_univ, finset.mem_filter, finset.mem_inter] at he,
      rw [← he.1, ← he.2] },
  end }

end simplex_category
