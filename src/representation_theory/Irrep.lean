import representation_theory.Rep representation_theory.fdRep ring_theory.simple_module
open category_theory

universes u v

variables {C : Type u} [category.{v} C]
lemma nonempty_iso_trans {X Y Z : C} : nonempty (X ≅ Y) → nonempty (Y ≅ Z) → nonempty (X ≅ Z) :=
λ f g, ⟨f.some ≪≫ g.some⟩

variables (k G : Type u) [field k] [group G]

def iso_quot : setoid { M : submodule (monoid_algebra k G) (monoid_algebra k G) |
  is_simple_module (monoid_algebra k G) ((monoid_algebra k G) ⧸ M) } := {
  r     := λ M N, nonempty $
    ((monoid_algebra k G) ⧸ (M : submodule (monoid_algebra k G) (monoid_algebra k G))) ≅
    ((monoid_algebra k G) ⧸ (N : submodule (monoid_algebra k G) (monoid_algebra k G))),
  iseqv := ⟨λ M, nonempty_of_inhabited,
  ⟨ λ M N, (iso.nonempty_iso_symm _ _).mp,
    λ M N O, nonempty_iso_trans ⟩ ⟩ }

def Irrep := quotient (iso_quot k G)
