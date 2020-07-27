/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import topology.simplicial.simplex_category
import topology.simplicial.move_this
import category_theory.yoneda

/-! # Simplicial objects and simplicial sets -/

open category_theory

universe variables u₀ v u
variables (C : Type u) [category.{v} C]

/-- The category of simplicial objects valued in a category `C`.
This is the category of contravariant functors from
`NonemptyFinLinOrd` to `C`. -/
@[derive category]
def Simplicial := NonemptyFinLinOrd.{u₀}ᵒᵖ ⥤ C

namespace Simplicial
variable {C}

/-- The functor that restricts a simplicial object to a contravariant functor
on the skeletal subcategory `simplex_category`. -/
def skeletal : Simplicial.{u₀} C ⥤ (simplex_categoryᵒᵖ ⥤ C) :=
functor.comp_left (simplex_category.skeletal_functor.op)

def δ (X : Simplicial.{u₀} C) {n} (i : fin (n+2)) :
  (skeletal.obj X).obj _ ⟶ (skeletal.obj X).obj _ :=
(skeletal.obj X).map (simplex_category.δ i).op

def σ (X : Simplicial.{u₀} C) {n} (i : fin (n+1)) :
  (skeletal.obj X).obj _ ⟶ (skeletal.obj X).obj _ :=
(skeletal.obj X).map (simplex_category.σ i).op

/-- The first simplicial identity -/
lemma δ_comp_δ (X : Simplicial.{u₀} C) {n} {i j : fin (n+2)} (H : i ≤ j) :
  X.δ j.succ ≫ X.δ i = X.δ i.cast_succ ≫ X.δ j :=
by simp only [δ, ← functor.map_comp, ← op_comp, simplex_category.δ_comp_δ H]

end Simplicial

/-- The category of simplicial types.
This is the category of contravariant functors from
`NonemptyFinLinOrd` to `Type u`. -/
@[derive small_category]
def sType : Type (u+1) := Simplicial.{u} (Type u)

namespace sType

/-- The `n`-th standard simplex associated with a nonempty finite linear order `n`
is the Yoneda embedding of `n`. -/
def standard_simplex : NonemptyFinLinOrd.{u} ⥤ sType.{u} :=
yoneda

def as_preorder_hom {n} {m} (α : (standard_simplex.obj n).obj m) :
  preorder_hom m.unop n := α

/-- The boundary of the `n`-th standard simplex consists of
all `m`-simplices of `standard_simplex n` that are not surjective
(when viewed as monotone function `m → n`). -/
@[simps]
def boundary (n : NonemptyFinLinOrd.{0}) : sType :=
{ obj := λ m, {α : (standard_simplex.obj n).obj m // ¬ function.surjective (as_preorder_hom α)},
  map := λ m₁ m₂ f α, ⟨f.unop ≫ (α : (standard_simplex.obj n).obj m₁),
  by { intro h, apply α.property, exact function.surjective.of_comp h }⟩ }

/-- The inclusion of the boundary of the `n`-th standard simplex into that standard simplex. -/
def boundary_inclusion (n : NonemptyFinLinOrd.{0}) :
  boundary n ⟶ standard_simplex.obj n :=
{ app := λ m (α : {α : (standard_simplex.obj n).obj m // _}), α }

/-- `horn n i` is the `i`-th horn of the `n`-th standard simplex, where `i : n`.
It consists of all `m`-simplices `α` of `standard_simplex n`
for which the union of `{i}` and the range of `α` is not all of `n`
(when viewing `α` as monotone function `m → n`). -/
def horn (n : NonemptyFinLinOrd.{0}) (i : n) : sType :=
{ obj := λ m, {α : (standard_simplex.obj n).obj m // set.range (as_preorder_hom α) ∪ {i} ≠ set.univ },
  map := λ m₁ m₂ f α, ⟨f.unop ≫ (α : (standard_simplex.obj n).obj m₁),
  begin
    intro h, apply α.property,
    rw set.eq_univ_iff_forall at h ⊢, intro j,
    apply or.imp _ id (h j),
    intro hj,
    exact set.range_comp_subset_range _ _ hj,
  end⟩ }

/-- The inclusion of the `i`-th horn of the `n`-th standard simplex into that standard simplex. -/
def horn_inclusion (n : NonemptyFinLinOrd.{0}) (i : n) :
  horn n i ⟶ standard_simplex.obj n :=
{ app := λ m (α : {α : (standard_simplex.obj n).obj m // _}), α }

end sType
