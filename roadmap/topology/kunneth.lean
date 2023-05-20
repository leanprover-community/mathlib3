import algebraic_topology.alternating_face_map_complex
import algebraic_topology.simplicial_set
import algebra.category.Module.abelian
import algebra.category.Module.adjunctions
import algebra.category.Module.biproducts
import algebra.category.Module.monoidal.basic
import algebra.category.Module.projective
import category_theory.abelian.projective
import algebra.homology.homology
import linear_algebra.projective_space.basic
import category_theory.monoidal.braided
import category_theory.monoidal.Tor
import category_theory.monoidal.functor_category
import algebra.homology.short_exact.abelian

open category_theory
open algebraic_topology

universe u

noncomputable theory

def Top.to_sModule (R : Type) [ring R] : Top.{0} ⥤ simplicial_object (Module R) :=
Top.to_sSet ⋙
  ((simplicial_object.whiskering _ _).obj (Module.free R))

def singular_chains (R : Type) [ring R] : Top.{0} ⥤ chain_complex (Module R) ℕ :=
Top.to_sModule R ⋙ alternating_face_map_complex _

def singular_homology (n : ℕ) (R : Type) [ring R] : Top.{0} ⥤ Module R :=
singular_chains R ⋙ homology_functor _ _ n

abbreviation H := (λ n, singular_homology n ℤ)

-- TODO this needs the correct instances!
instance (K V : Type*) [division_ring K] [add_comm_group V] [module K V] :
  topological_space (ℙ K V) :=
sorry

def ℝℙ2 : Top.{0} := Top.of (ℙ ℝ (fin 2 → ℝ))

namespace ℝℙ2

def H0 : (H 0).obj ℝℙ2 ≅ Module.of _ ℤ := sorry
def H1 : (H 1).obj ℝℙ2 ≅ Module.of _ (zmod 2) := sorry
def Hn (n : ℕ) (h : 2 ≤ n) : (H n).obj ℝℙ2 ≅ Module.of _ unit := sorry

end ℝℙ2

instance : monoidal_category Top.{u} :=
{ tensor_unit := Top.of punit.{u+1},
  tensor_obj := λ X Y, Top.of (X × Y),
  tensor_hom := λ W X Y Z f g, continuous_map.prod_map f g,
  associator := sorry,
  left_unitor := sorry,
  right_unitor := sorry, }

-- This should probably instead be by something like:
-- monoidal_of_chosen_finite_products (Top.terminal_limit_cone) (Top.binary_product_limit_cone)

instance : symmetric_category Top := sorry

-- namespace ℝℙ2xℝℙ2

-- def H0 : (H 0).obj (ℝℙ2 ⊗ ℝℙ2) ≅ Module.of _ ℤ := sorry
-- def H1 : (H 1).obj (ℝℙ2 ⊗ ℝℙ2) ≅ Module.of _ (zmod 2 × zmod 2) := sorry
-- def H2 : (H 1).obj (ℝℙ2 ⊗ ℝℙ2) ≅ Module.of _ (zmod 2) := sorry
-- def H3 : (H 1).obj (ℝℙ2 ⊗ ℝℙ2) ≅ Module.of _ (zmod 2) := sorry
-- def Hn (n : ℕ) (h : 4 ≤ n) : (H n).obj (ℝℙ2 ⊗ ℝℙ2) ≅ Module.of _ unit := sorry

-- end ℝℙ2xℝℙ2

open category_theory.limits

def kunneth_mono (k : ℕ) (X Y : Top.{0}) :
  biproduct (λ p : finset.nat.antidiagonal k, (H p.1.1).obj X ⊗ (H p.1.2).obj Y)
   ⟶ (H k).obj (X ⊗ Y) := sorry

instance : has_projective_resolutions (Module ℤ) := sorry

def kunneth_epi (k : ℕ) (X Y : Top.{0}) :
  (H k).obj (X ⊗ Y) ⟶
    biproduct (λ p : finset.nat.antidiagonal (k - 1), ((Tor _ 1).obj ((H p.1.1).obj X)).obj ((H p.1.2).obj Y)) := sorry

theorem kunneth (k : ℕ) (X Y : Top.{0}) : short_exact (kunneth_mono k X Y) (kunneth_epi k X Y) := sorry

namespace category_theory.short_exact

variables {𝒜 : Type*} [category 𝒜]

variables {A B C : 𝒜} {f : A ⟶ B} {g : B ⟶ C}
variables [has_zero_morphisms 𝒜] [has_kernels 𝒜] [has_images 𝒜]

def is_iso_left_of_is_zero_right (w : short_exact f g) (h : is_zero C) : is_iso f := sorry
def is_iso_right_of_is_zero_left (w : short_exact f g) (h : is_zero A) : is_iso g := sorry

end category_theory.short_exact

namespace ℝℙ2xℝℙ2

def H0 : (H 0).obj (ℝℙ2 ⊗ ℝℙ2) ≅ Module.of _ ℤ :=
begin
  haveI := (kunneth 0 ℝℙ2 ℝℙ2).is_iso_left_of_is_zero_right _,
  refine (as_iso (kunneth_mono 0 ℝℙ2 ℝℙ2)).symm ≪≫ _,
  -- The sum over `antidiagonal 0` gives just `(H 0).obj ℝℙ2 ⊗ (H 0).obj ℝℙ2 ≅ ℤ ⊗ ℤ ≅ ℤ`
  sorry,
  -- All the `Tor`s vanish.
  sorry
end

def H3 : (H 3).obj (ℝℙ2 ⊗ ℝℙ2) ≅ Module.of _ (zmod 2) :=
begin
  haveI := (kunneth 3 ℝℙ2 ℝℙ2).is_iso_right_of_is_zero_left _,
  refine (as_iso (kunneth_epi 3 ℝℙ2 ℝℙ2)) ≪≫ _,
  -- The sum over `antidiagonal 2` gives
  -- `Tor ℤ (zmod 2) ⊕ Tor (zmod 2) (zmod 2) ⊕ Tor (zmod 2) ℤ`.`
  -- The first and last terms are zero, the middle terms gives what we want.
  sorry,
  -- There are no interesting homology groups in degrees adding up to 3.
  sorry
end

end ℝℙ2xℝℙ2

/-
The Kunneth formula we wrote above factors into three separate idea:
* `Top.to_sModule : Top ⥤ simplicial_object (Module R)` is a monoidal functor
*
* The homological algebra Kunneth formula.
-/

instance (C : Type _) [category C] [monoidal_category C] : monoidal_category (simplicial_object C) :=
begin
  dsimp [simplicial_object],
  apply_instance,
end

instance : monoidal_category sSet :=
begin
  dsimp [sSet],
  apply_instance
end

def Top.to_sSet_monoidal : monoidal_functor Top.{0} sSet :=
{ ε :=
  { app := λ n x, by split, },
  μ := λ X Y,
  { app := λ n x, continuous_map.prod_mk x.1 x.2 },
  μ_natural' := sorry,
  associativity' := sorry,
  left_unitality' := sorry,
  right_unitality' := sorry,
  ε_is_iso := sorry,
  μ_is_iso := sorry,
  ..Top.to_sSet, }

def simplicial_object.whiskering_monoidal
  (C : Type u) [category C] [monoidal_category C] (D : Type u) [category D] [monoidal_category D] :
  (monoidal_functor C D) ⥤ monoidal_functor (simplicial_object C) (simplicial_object D) :=
sorry

def Top.to_sModule_monoidal (R : Type) [comm_ring R] :
  monoidal_functor Top.{0} (simplicial_object (Module.{0} R)) :=
Top.to_sSet_monoidal ⊗⋙
  ((simplicial_object.whiskering_monoidal _ _).obj (Module.monoidal_free R))

section
variables {V : Type*} [category V] [monoidal_category V]
  [has_zero_morphisms V] [has_finite_biproducts V]

instance : monoidal_category (graded_object ℕ V) :=
{ tensor_unit := sorry,
  tensor_obj := λ X Y k, biproduct (λ p : finset.nat.antidiagonal k, X p.1.1 ⊗ Y p.1.2),
  tensor_hom := sorry,
  associator := sorry,
  left_unitor := sorry,
  right_unitor := sorry, }

@[simp] lemma graded_object.tensor_obj_apply (X Y : graded_object ℕ V) (k : ℕ) :
  (X ⊗ Y) k = biproduct (λ p : finset.nat.antidiagonal k, X p.1.1 ⊗ Y p.1.2) :=
rfl

instance : monoidal_category (chain_complex V ℕ) :=
sorry

variables [has_equalizers V] [has_images V] [has_image_maps V] [has_cokernels V]

def graded_homology_lax_monoidal_functor : lax_monoidal_functor (chain_complex V ℕ) (graded_object ℕ V) :=
{ ε := sorry,
  μ := λ X Y n, begin
    dsimp,
    -- We need `(⨁ λ p : finset.nat.antidiagonal n, homology X p.1.1 ⊗ homology Y p.1.2)
    --   ⟶ homology (X ⊗ Y) n`
    sorry,
  end,
  ..graded_homology_functor V _ }

theorem graded_homology_tensorator_mono (X Y : chain_complex V ℕ) :
  mono (graded_homology_lax_monoidal_functor.μ X Y) := sorry

end

section
variables {R : Type} [comm_ring R] [is_domain R] [is_principal_ideal_ring R]

-- Verifying we have everything we need to do homology.
example : has_equalizers (Module.{0} R) := by apply_instance
example : has_images (Module.{0} R) := by apply_instance
example : has_image_maps (Module.{0} R) := by apply_instance
example : has_zero_morphisms (Module.{0} R) := by apply_instance
example : has_cokernels (Module.{0} R) := by apply_instance

-- Verify we have everything we need to do tensor products of chain complexes.
example : monoidal_category (Module.{0} R) := by apply_instance
example : has_finite_biproducts (Module.{0} R) := by apply_instance

-- Verify we have everything we need to do `Tor`.
example : abelian (Module.{0} R) := by apply_instance
example : enough_projectives (Module.{0} R) := by apply_instance
example : has_projective_resolutions (Module.{0} R) := by apply_instance

abbreviation H' (n : ℕ) (X : chain_complex (Module.{0} R) ℕ) : Module.{0} R :=
  (homology_functor (Module.{0} R) _ n).obj X

def cokernel_iso (k : ℕ) (X Y : chain_complex (Module.{0} R) ℕ) :
  cokernel (graded_homology_lax_monoidal_functor.μ X Y k) ≅
    biproduct (λ p : finset.nat.antidiagonal (k - 1), ((Tor _ 1).obj (H' p.1.1 X)).obj (H' p.1.2 Y)) :=
-- This is the hardest sorry so far today.
-- In fact, it's not even true without the assumption that at least one of `X` and `Y`
-- is a complex of free modules, but we'll cheat and ignore that right now.
sorry

namespace category_theory.short_exact

variables {𝒜 : Type*} [category 𝒜] [abelian 𝒜]

variables {A B C : 𝒜} {f : A ⟶ B} {g : B ⟶ C}

example : category_theory.epi (cokernel.π f) := by apply_instance

instance (w : f ≫ cokernel.π f = 0) :
  is_iso (image_to_kernel f (cokernel.π f) w) :=
begin
  use (kernel_subobject_iso (cokernel.π f)).hom ≫ (abelian.image_iso_image f).hom ≫ (image_subobject_iso f).inv,
  split,
  { ext, simp, },
  { ext, simp, }
end

theorem of_mono_cokernel [category_theory.mono f] [has_cokernel f] :
  short_exact f (cokernel.π f) :=
{ exact :=
  { epi := by apply_instance,
    w := by simp, },}

theorem comp_iso_left {A' : 𝒜} (i : A' ⟶ A) [is_iso i] (w : short_exact f g) :
  short_exact (i ≫ f) g := sorry
theorem comp_iso_middle {B' : 𝒜} (i : B ⟶ B') [is_iso i] (w : short_exact f g) :
  short_exact (f ≫ i) (inv i ≫ g) := sorry
theorem comp_iso_middle' {B' : 𝒜} (i : B' ⟶ B) [is_iso i] (w : short_exact f g) :
  short_exact (f ≫ inv i) (i ≫ g) := by simpa using w.comp_iso_middle (inv i)
theorem comp_iso_right {C' : 𝒜} (i : C ⟶ C') [is_iso i] (w : short_exact f g) :
  short_exact f (g ≫ i) := sorry

theorem of_mono_cokernel_iso [category_theory.mono f] [has_cokernel f] (i : cokernel f ≅ C) :
  short_exact f (cokernel.π f ≫ i.hom) := of_mono_cokernel.comp_iso_right _

theorem of_epi_kernel_iso [category_theory.epi g] [has_kernel g] (i : kernel g ≅ A) :
  short_exact (i.inv ≫ kernel.ι g) g :=
-- TODO dualize the above.
sorry

end category_theory.short_exact


theorem kunneth' (k : ℕ) (X Y : chain_complex (Module.{0} R) ℕ) :
  short_exact (graded_homology_lax_monoidal_functor.μ X Y k)
    (cokernel.π (graded_homology_lax_monoidal_functor.μ X Y k) ≫ (cokernel_iso k X Y).hom) :=
sorry

end
