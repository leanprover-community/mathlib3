/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import algebraic_topology.simplicial_object
import algebraic_topology.topological_simplex
import category_theory.limits.presheaf
import category_theory.limits.types
import category_theory.yoneda
import topology.category.Top.limits

/-!
A simplicial set is just a simplicial object in `Type`,
i.e. a `Type`-valued presheaf on the simplex category.

(One might be tempted to call these "simplicial types" when working in type-theoretic foundations,
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

open category_theory category_theory.limits

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

localized "notation (name := standard_simplex) `Δ[`n`]` :=
  sSet.standard_simplex.obj (simplex_category.mk n)" in simplicial

instance : inhabited sSet := ⟨Δ[0]⟩

section

/-- The `m`-simplices of the `n`-th standard simplex are
the monotone maps from `fin (m+1)` to `fin (n+1)`. -/
def as_order_hom {n} {m} (α : Δ[n].obj m) :
  order_hom (fin (m.unop.len+1)) (fin (n+1)) := α.to_order_hom
end

/-- The boundary `∂Δ[n]` of the `n`-th standard simplex consists of
all `m`-simplices of `standard_simplex n` that are not surjective
(when viewed as monotone function `m → n`). -/
def boundary (n : ℕ) : sSet :=
{ obj := λ m, {α : Δ[n].obj m // ¬ function.surjective (as_order_hom α)},
  map := λ m₁ m₂ f α, ⟨f.unop ≫ (α : Δ[n].obj m₁),
  by { intro h, apply α.property, exact function.surjective.of_comp h }⟩ }

localized "notation (name := sSet.boundary) `∂Δ[`n`]` := sSet.boundary n" in simplicial

/-- The inclusion of the boundary of the `n`-th standard simplex into that standard simplex. -/
def boundary_inclusion (n : ℕ) :
  ∂Δ[n] ⟶ Δ[n] :=
{ app := λ m (α : {α : Δ[n].obj m // _}), α }

/-- `horn n i` (or `Λ[n, i]`) is the `i`-th horn of the `n`-th standard simplex, where `i : n`.
It consists of all `m`-simplices `α` of `Δ[n]`
for which the union of `{i}` and the range of `α` is not all of `n`
(when viewing `α` as monotone function `m → n`). -/
def horn (n : ℕ) (i : fin (n+1)) : sSet :=
{ obj := λ m,
  { α : Δ[n].obj m // set.range (as_order_hom α) ∪ {i} ≠ set.univ },
  map := λ m₁ m₂ f α, ⟨f.unop ≫ (α : Δ[n].obj m₁),
  begin
    intro h, apply α.property,
    rw set.eq_univ_iff_forall at h ⊢, intro j,
    apply or.imp _ id (h j),
    intro hj,
    exact set.range_comp_subset_range _ _ hj,
  end⟩ }

localized "notation (name := sSet.horn) `Λ[`n`, `i`]` := sSet.horn (n : ℕ) i" in simplicial

/-- The inclusion of the `i`-th horn of the `n`-th standard simplex into that standard simplex. -/
def horn_inclusion (n : ℕ) (i : fin (n+1)) :
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

/-- The category of augmented simplicial sets, as a particular case of
augmented simplicial objects. -/
abbreviation augmented := simplicial_object.augmented (Type u)

namespace augmented

/-- The functor which sends `[n]` to the simplicial set `Δ[n]` equipped by
the obvious augmentation towards the terminal object of the category of sets. -/
@[simps]
noncomputable def standard_simplex : simplex_category ⥤ sSet.augmented :=
{ obj := λ Δ,
  { left := sSet.standard_simplex.obj Δ,
    right := terminal _,
    hom := { app := λ Δ', terminal.from _, }, },
  map := λ Δ₁ Δ₂ θ,
  { left := sSet.standard_simplex.map θ,
    right := terminal.from _, }, }

end augmented

end sSet

/-- The functor associating the singular simplicial set to a topological space. -/
def Top.to_sSet : Top ⥤ sSet :=
colimit_adj.restricted_yoneda simplex_category.to_Top

/-- The geometric realization functor. -/
noncomputable def sSet.to_Top : sSet ⥤ Top :=
colimit_adj.extend_along_yoneda simplex_category.to_Top

/-- Geometric realization is left adjoint to the singular simplicial set construction. -/
noncomputable def sSet_Top_adj : sSet.to_Top ⊣ Top.to_sSet :=
colimit_adj.yoneda_adjunction _

/-- The geometric realization of the representable simplicial sets agree
  with the usual topological simplices. -/
noncomputable def sSet.to_Top_simplex :
  (yoneda : simplex_category ⥤ _) ⋙ sSet.to_Top ≅ simplex_category.to_Top :=
colimit_adj.is_extension_along_yoneda _
