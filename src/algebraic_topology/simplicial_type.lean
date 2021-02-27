/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import algebraic_topology.simplicial_object
import category_theory.yoneda

/-!
A simplicial type (usually called a simplicial set, when using set theoretic foundations)
is just a simplicial object in `Type`, i.e. a `Type`-valued presheaf on the simplex category.

We define the standard simplices as simplicial types, and their boundaries and horns.
-/

universes v u

open category_theory

/-- The category of simplicial types.
This is the category of contravariant functors from
`simplex_category` to `Type u`. -/
@[derive large_category]
def sType : Type (u+1) := simplicial_object (Type u)

namespace sType

/-- The `n`-th standard simplex associated with a nonempty finite linear order `n`
is the Yoneda embedding of `n`. -/
def standard_simplex : simplex_category ⥤ sType := yoneda

instance : inhabited sType := ⟨standard_simplex.obj (0 : ℕ)⟩

/-- The `m`-simplices of the `n`-th standard simplex are
the monotone maps from `fin (m+1)` to `fin (n+1)`. -/
def as_preorder_hom {n} {m} (α : (standard_simplex.obj n).obj m) :
  preorder_hom (fin (m.unop+1)) (fin (n+1)) := α

/-- The boundary of the `n`-th standard simplex consists of
all `m`-simplices of `standard_simplex n` that are not surjective
(when viewed as monotone function `m → n`). -/
@[simps]
def boundary (n : ℕ) : sType :=
{ obj := λ m, {α : (standard_simplex.obj n).obj m // ¬ function.surjective (as_preorder_hom α)},
  map := λ m₁ m₂ f α, ⟨f.unop ≫ (α : (standard_simplex.obj n).obj m₁),
  by { intro h, apply α.property, exact function.surjective.of_comp h }⟩ }

/-- The inclusion of the boundary of the `n`-th standard simplex into that standard simplex. -/
def boundary_inclusion (n : ℕ) :
  boundary n ⟶ standard_simplex.obj n :=
{ app := λ m (α : {α : (standard_simplex.obj n).obj m // _}), α }

/-- `horn n i` is the `i`-th horn of the `n`-th standard simplex, where `i : n`.
It consists of all `m`-simplices `α` of `standard_simplex n`
for which the union of `{i}` and the range of `α` is not all of `n`
(when viewing `α` as monotone function `m → n`). -/
def horn (n : ℕ) (i : fin (n+1)) : sType :=
{ obj := λ m,
  { α : (standard_simplex.obj n).obj m // set.range (as_preorder_hom α) ∪ {i} ≠ set.univ },
  map := λ m₁ m₂ f α, ⟨f.unop ≫ (α : (standard_simplex.obj n).obj m₁),
  begin
    intro h, apply α.property,
    rw set.eq_univ_iff_forall at h ⊢, intro j,
    apply or.imp _ id (h j),
    intro hj,
    exact set.range_comp_subset_range _ _ hj,
  end⟩ }

/-- The inclusion of the `i`-th horn of the `n`-th standard simplex into that standard simplex. -/
def horn_inclusion (n : ℕ) (i : fin (n+1)) :
  horn n i ⟶ standard_simplex.obj n :=
{ app := λ m (α : {α : (standard_simplex.obj n).obj m // _}), α }

end sType
