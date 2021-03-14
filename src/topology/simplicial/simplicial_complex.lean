/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import topology.simplicial.simplicial_module
import algebra.category.Module.monoidal

/-! # The simplicial complex associated with a simplicial module -/

universe variables u

open category_theory

namespace simplicial_module
open simplicial_object opposite
variables {R : Type u} [comm_ring R] (M : simplicial_module R)

def graded_object : graded_object_with_shift (-1:ℤ) (Module R)
| -[1+n] := Module.of R punit -- this should just be 0
| (n:ℕ)  := (skeletal.obj M).obj (op n)

def graded_object_d : M.graded_object ⟶ M.graded_object⟦1⟧
| -[1+n]  := 0
| 0       := 0
| (n+1:ℕ) := M.boundary n ≫ (show M.graded_object n ⟶ M.graded_object (n+1-1), from eq_to_hom (by simp))

lemma graded_object_d_squared :
  ∀ i, (M.graded_object_d ≫ M.graded_object_d⟦1⟧') i = 0
| -[1+n]  := rfl
| 0       := rfl
| 1       := rfl
| (n+2:ℕ) :=
begin
  dsimp,
  show M.graded_object_d (n + 1 + 1) ≫ M.graded_object_d (n + 1 + 1 + -1) = 0,
  rw graded_object.hom_congr (M.graded_object_d) (show (n:ℤ) + 1 + 1 + -1 = n + 1, by simp),
  show (_ ≫ _) ≫ _ ≫ (_ ≫ _) ≫ _ = 0,
  simp only [eq_to_hom_trans, category.id_comp, eq_to_hom_refl, eq_to_hom_trans_assoc, category.assoc],
  show M.boundary ((n + 1)) ≫ M.boundary (n) ≫ eq_to_hom _ = 0,
  simp only [M.boundary_boundary_assoc n, limits.has_zero_morphisms.zero_comp]
end

def graded_object_map {M N : simplicial_module R} (f : M ⟶ N) :
  Π i, M.graded_object i ⟶ N.graded_object i
| -[1+n]  := 0
| (n:ℕ)   := (skeletal.map f).app (op n)

section
open linear_map

@[simp, reassoc] lemma boundary_graded_object_map
  {M N : simplicial_module R} (f : M ⟶ N) (n : ℕ) :
  M.boundary n ≫ graded_object_map f n = graded_object_map f (n + 1) ≫ N.boundary n :=
begin
  show llcomp R _ _ _ ((skeletal.map f).app (op n)) (M.boundary n) =
    llcomp R _ _ _ (N.boundary n) ((skeletal.map f).app (op (n+1:ℕ))),
  dsimp [boundary],
  rw [map_sum, map_sum, sum_apply],
  apply fintype.sum_congr,
  intro i,
  simp only [smul_apply, map_smul],
  congr' 1,
  show δ M i ≫ (skeletal.map f).app (op n) = (skeletal.map f).app (op (n+1:ℕ)) ≫ δ N i,
  apply (skeletal.map f).naturality,
end

end

lemma graded_object_map_comm {M N : simplicial_module R} (f : M ⟶ N) :
  M.graded_object_d ≫ (graded_object_map f)⟦1⟧' = graded_object_map f ≫ N.graded_object_d :=
funext $ λ i, match i with
| -[1+n]  := rfl
| 0       := rfl
| (n+1:ℕ) :=
  begin
    dsimp,
    rw graded_object.hom_congr (graded_object_map f) (show (n:ℤ) + 1 + -1 = n, by simp),
    show (M.boundary n ≫ eq_to_hom _) ≫ eq_to_hom _ ≫ graded_object_map f n ≫ eq_to_hom _ =
      graded_object_map f (n + 1) ≫ N.boundary n ≫ eq_to_hom _,
    simp only [category.id_comp, eq_to_hom_refl, eq_to_hom_trans_assoc, category.assoc,
      boundary_graded_object_map_assoc],
    refl,
  end
end

@[simp] lemma graded_object_map_id : Π i, graded_object_map (𝟙 M) i = 𝟙 (M.graded_object i)
| -[1+n]  := by ext
| (n:ℕ)   := by { ext, refl }

@[simp] lemma graded_object_map_comp {M₁ M₂ M₃ : simplicial_module R} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) :
  Π i, graded_object_map (f ≫ g) i = (graded_object_map f i) ≫ (graded_object_map g i)
| -[1+n]  := by ext
| (n:ℕ)   := by { ext, refl }

variables (R)

@[simps]
def simplicial_complex : simplicial_module R ⥤ chain_complex (Module R) :=
{ obj := λ M,
  { X := M.graded_object,
    d := M.graded_object_d,
    d_squared' := funext $ M.graded_object_d_squared },
  map := λ M N f,
  { f := graded_object_map f,
    comm' := graded_object_map_comm f }, }

end simplicial_module
