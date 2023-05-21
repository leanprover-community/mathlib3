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

/-
Our starting point is `Top.to_sSet`, which turns a topological space into a simplicial set.

def Top.to_sSet : Top ⥤ sSet :=
colimit_adj.restricted_yoneda simplex_category.to_Top
-/

/--
Turn a topological space into a simplicial R-module, by composing the simplicial set with
the free R-module functor.
-/
def Top.to_sModule (R : Type) [ring R] : Top.{0} ⥤ simplicial_object (Module R) :=
Top.to_sSet ⋙
  ((simplicial_object.whiskering _ _).obj (Module.free R))

/-- Compute the singular chain complex of a topological space,
by using the "alternating face map" functor. -/
def singular_chains (R : Type) [ring R] : Top.{0} ⥤ chain_complex (Module R) ℕ :=
Top.to_sModule R ⋙ alternating_face_map_complex _

/-- Compute the `n`-th singular homology of a topological space,
by applying the homology functor to the singular chain complex for the space. -/
-- def singular_homology (n : ℕ) (R : Type) [ring R] : Top.{0} ⥤ Module R :=
-- singular_chains R ⋙ homology_functor _ _ n

def singular_homology (n : ℕ) (R : Type) [ring R] : Top.{0} ⥤ Module R :=
(singular_chains R ⋙ homotopy_category.quotient _ _) ⋙ homotopy_category.homology_functor _ _ n

abbreviation H := (λ n, singular_homology n ℤ)

/-!
# Let's think about computing examples!
-/

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

-- Let's fake the Kunneth formula:

def kunneth_mono (k : ℕ) (X Y : Top.{0}) :
  biproduct (λ p : finset.nat.antidiagonal k, (H p.1.1).obj X ⊗ (H p.1.2).obj Y)
   ⟶ (H k).obj (X ⊗ Y) := sorry

def finset.nat.antidiagonal_prev (k : ℕ) : finset (ℕ × ℕ) :=
if k = 0 then
  ∅
else
  finset.nat.antidiagonal (k - 1)

def kunneth_epi (k : ℕ) (X Y : Top.{0}) :
  (H k).obj (X ⊗ Y) ⟶
    biproduct (λ p : finset.nat.antidiagonal_prev k, ((Tor _ 1).obj ((H p.1.1).obj X)).obj ((H p.1.2).obj Y)) := sorry

theorem kunneth (k : ℕ) (X Y : Top.{0}) : short_exact (kunneth_mono k X Y) (kunneth_epi k X Y) := sorry

-- Some missing API about short exact sequences.
namespace category_theory.short_exact

variables {𝒜 : Type*} [category 𝒜]

variables {A B C : 𝒜} {f : A ⟶ B} {g : B ⟶ C}
variables [has_zero_morphisms 𝒜] [has_kernels 𝒜] [has_images 𝒜]

theorem is_iso_left_of_is_zero_right (w : short_exact f g) (h : is_zero C) : is_iso f := sorry
theorem is_iso_right_of_is_zero_left (w : short_exact f g) (h : is_zero A) : is_iso g := sorry

-- These may actually need stronger hypotheses to prove!
-- Certainly they are true in an abelian category.

end category_theory.short_exact

section
variables {C : Type _} [category C] [has_zero_morphisms C] [has_finite_biproducts C]
  [has_binary_biproducts C]

def biproduct_nat_antidiagonal_0 (f : ℕ → ℕ → C) :
  biproduct (λ p : finset.nat.antidiagonal 0, f p.1.1 p.1.2) ≅ f 0 0 :=
sorry

def biproduct_nat_antidiagonal_1 (f : ℕ → ℕ → C) :
  biproduct (λ p : finset.nat.antidiagonal 1, f p.1.1 p.1.2) ≅ f 0 1 ⊞ f 1 0 :=
sorry

def biproduct_nat_antidiagonal_2 (f : ℕ → ℕ → C) :
  biproduct (λ p : finset.nat.antidiagonal 2, f p.1.1 p.1.2) ≅ f 0 2 ⊞ f 1 1 ⊞ f 2 0 :=
sorry

def biproduct_nat_antidiagonal_3 (f : ℕ → ℕ → C) :
  biproduct (λ p : finset.nat.antidiagonal 3, f p.1.1 p.1.2) ≅ f 0 3 ⊞ f 1 2 ⊞ f 2 1 ⊞ f 3 0 :=
sorry

def is_zero_biproduct_nat_antidiagonal_prev_0 (f : ℕ → ℕ → C) :
  is_zero (biproduct (λ p : finset.nat.antidiagonal_prev 0, f p.1.1 p.1.2)) :=
sorry

def biproduct_nat_antidiagonal_prev_3 (f : ℕ → ℕ → C) :
  biproduct (λ p : finset.nat.antidiagonal_prev 3, f p.1.1 p.1.2) ≅ f 0 2 ⊞ f 1 1 ⊞ f 2 0 :=
sorry

end

namespace ℝℙ2xℝℙ2

def H0 : (H 0).obj (ℝℙ2 ⊗ ℝℙ2) ≅ Module.of _ ℤ :=
begin
  haveI := (kunneth 0 ℝℙ2 ℝℙ2).is_iso_left_of_is_zero_right _,
  refine (as_iso (kunneth_mono 0 ℝℙ2 ℝℙ2)).symm ≪≫ _,
  { -- The sum over `antidiagonal 0` gives just `(H 0).obj ℝℙ2 ⊗ (H 0).obj ℝℙ2 ≅ ℤ ⊗ ℤ ≅ ℤ`
    refine (biproduct_nat_antidiagonal_0 (λ i j, (H i).obj ℝℙ2 ⊗ (H j).obj ℝℙ2)) ≪≫ _,
    refine (ℝℙ2.H0 ⊗ ℝℙ2.H0) ≪≫ _,
    exact λ_ (Module.of ℤ ℤ), },
  { -- There are no `Tor`s.
    exact is_zero_biproduct_nat_antidiagonal_prev_0
      (λ i j, ((Tor _ 1).obj ((H i).obj ℝℙ2)).obj ((H j).obj ℝℙ2)), },
end

def H3 : (H 3).obj (ℝℙ2 ⊗ ℝℙ2) ≅ Module.of _ (zmod 2) :=
begin
  haveI := (kunneth 3 ℝℙ2 ℝℙ2).is_iso_right_of_is_zero_left _,
  refine (as_iso (kunneth_epi 3 ℝℙ2 ℝℙ2)) ≪≫ _,
  { -- The sum over `antidiagonal_prev 3` gives
    -- `Tor ℤ (zmod 2) ⊕ Tor (zmod 2) (zmod 2) ⊕ Tor (zmod 2) ℤ`.`
    refine (biproduct_nat_antidiagonal_prev_3
      (λ i j, ((Tor _ 1).obj ((H i).obj ℝℙ2)).obj ((H j).obj ℝℙ2))) ≪≫ _,
    -- The first and last terms are zero, the middle terms gives what we want.
    dsimp,
    sorry, },
  -- There are no interesting homology groups in degrees adding up to 3.
  sorry
end

end ℝℙ2xℝℙ2

/-!
# The plan

The Kunneth formula we wrote above factors into three separate ideas:
1. `Top.to_sModule : Top ⥤ simplicial_object (Module R)` is a monoidal functor
2. `alternating_face_map_complex : simplicial_object C ⥤ chain_complex C ℕ` is both
  * a lax monoidal functor (via the Eilenberg-Zilber map)
  * an oplax monoidal functor (via the Alexander-Whitney map)
  * and the composition
    `alternating_face_map_complex ⋙ homotopy_category.quotient :
      simplicial_object C ⥤ homotopy_category C ℕ`
    is a (strong) monoidal functor.
3. The homological algebra Kunneth formula:
  * `graded_homology_functor : chain_complex C ℕ ⥤ graded_object ℕ C`
    is a lax monoidal functor,
  * the "laxitor" `H X ⊗ H Y ⟶ H (X ⊗ Y)` is a monomorphism,
  * we can explicitly identify the cokernel of the laxitor as a sum of `Tor` groups.
-/

/-!
# Step 1, `Top.to_sModule` is a monoidal functor.
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
{ obj := λ F,
  { ε := sorry,
    μ := sorry,
    ε_is_iso := sorry,
    μ_is_iso := sorry,
    ..(simplicial_object.whiskering C D).obj F.to_functor },
  map := sorry, }

def Top.to_sModule_monoidal (R : Type) [comm_ring R] :
  monoidal_functor Top.{0} (simplicial_object (Module.{0} R)) :=
Top.to_sSet_monoidal ⊗⋙
  ((simplicial_object.whiskering_monoidal _ _).obj (Module.monoidal_free R))

/-!
# Step 3, the homological Kunneth formula. -/

section
variables {V : Type*} [category V] [monoidal_category V]
  [has_zero_object V] [has_zero_morphisms V] [has_finite_biproducts V]

open_locale zero_object

instance : monoidal_category (graded_object ℕ V) :=
{ tensor_unit := pi.single 0 (𝟙_ V),
  tensor_obj := λ X Y k, biproduct (λ p : finset.nat.antidiagonal k, X p.1.1 ⊗ Y p.1.2),
  tensor_hom := λ W X Y Z f g k, biproduct.map sorry,
  associator := sorry,
  left_unitor := sorry,
  right_unitor := sorry, }

@[simp] lemma graded_object.tensor_obj_apply (X Y : graded_object ℕ V) (k : ℕ) :
  (X ⊗ Y) k = biproduct (λ p : finset.nat.antidiagonal k, X p.1.1 ⊗ Y p.1.2) :=
rfl

end

section
variables {V : Type*} [category V] [preadditive V] [monoidal_category V]
  [has_finite_biproducts V]

/-- The morphism between a pair of objects in a family,
which is either the identity if the two objects are the same,
or zero otherwise.
 -/
def id_or_zero {β : Type*} [decidable_eq β] (X : β → V) (i j : β) : X i ⟶ X j :=
if h : i = j then
  eq_to_hom (congr_arg X h)
else
  0

def tensor_obj_X (X Y : chain_complex V ℕ) (k : ℕ) : V :=
biproduct (λ p : finset.nat.antidiagonal k, X.X p.1.1 ⊗ Y.X p.1.2)

def tensor_obj_d (X Y : chain_complex V ℕ) (i j : ℕ) : tensor_obj_X X Y i ⟶ tensor_obj_X X Y j :=
biproduct.matrix
  (λ p q, X.d p.1.1 q.1.1 ⊗ id_or_zero Y.X p.1.2 q.1.2 +
    ((-1 : ℤ)^p.1.1) • (id_or_zero X.X p.1.1 q.1.1 ⊗ Y.d p.1.2 q.1.2))

def tensor_obj (X Y : chain_complex V ℕ) : chain_complex V ℕ  :=
{ X := tensor_obj_X X Y,
  d := tensor_obj_d X Y,
  shape' := sorry,
  d_comp_d' := sorry, }

def tensor_hom {W X Y Z : chain_complex V ℕ} (f : W ⟶ X) (g : Y ⟶ Z) :
  tensor_obj W Y ⟶ tensor_obj X Z  :=
{ f := λ i, biproduct.map (λ p, f.f p.1.1 ⊗ g.f p.1.2),
  comm' := sorry, }

instance : monoidal_category (chain_complex V ℕ) :=
{ tensor_unit := (chain_complex.single₀ V).obj (𝟙_ V),
  tensor_obj := tensor_obj,
  tensor_hom := λ W X Y Z f g, tensor_hom f g,
  associator := sorry,
  left_unitor := sorry,
  right_unitor := sorry,
  tensor_id' := sorry,
  tensor_comp' := sorry, }

-- TODO this should be done generally:
-- a quotient of a monoidal category by a monoidal congruence is monoidal.
instance : monoidal_category (homotopy_category V (complex_shape.down ℕ)) :=
{ tensor_unit := sorry,
  tensor_obj := λ X Y, { as := X.as ⊗ Y.as },
  tensor_hom := sorry,
  associator := sorry,
  left_unitor := sorry,
  right_unitor := sorry, }

variables [has_equalizers V] [has_images V] [has_image_maps V] [has_cokernels V]
variables (V)

def graded_homology_lax : lax_monoidal_functor (chain_complex V ℕ) (graded_object ℕ V) :=
{ ε := sorry,
  μ := λ X Y n, biproduct.desc (λ p, begin
    dsimp,
    -- We need `homology X p.1.1 ⊗ homology Y p.1.2 ⟶ homology (X ⊗ Y) n` for `p.1.1 + p.1.2 = n`.
    -- We actually can't do this without further hypotheses!
    -- I'm not too sure what generality is best. Certainly we can do it for modules.
    -- `V` is abelian and `⊗` is biexact suffices, I think.
    -- Similarly just `V` rigid monoidal?
    -- Let's punt for now!
    sorry,
  end),
  μ_natural' := sorry,
  associativity' := sorry,
  left_unitality' := sorry,
  right_unitality' := sorry,
  ..graded_homology_functor V _ }

-- Aside: using this functor, we can push forward
-- a differential graded algebra (i.e. a `Mon_ (chain_complex V ℕ)`)
-- to an graded (associative) algebra (i.e. a `Mon_ (graded_object ℕ V))`)
-- using `lax_monoidal_functor.map_Mon`.
-- (Similarly for commutative algebras, although we do not yet have
-- `lax_braided_functor.map_CommMon`.)
-- To count as a solution to Reid's CDGA challenge
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/CDGAs
-- you still need to show that `Mon_ (chain_complex (Module R) ℕ)` really "is" a CDGA.

instance graded_homology_tensorator_mono (X Y : chain_complex V ℕ) :
  mono ((graded_homology_lax V).μ X Y) := sorry

instance graded_object.mono_apply
  {X Y : graded_object ℕ V} (f : X ⟶ Y) [mono f] (k : ℕ) : mono (f k) :=
sorry

-- instance graded_object.epi_apply
--   {X Y : graded_object ℕ V} (f : X ⟶ Y) [epi f] (k : ℕ) : epi (f k) :=
-- sorry

instance graded_object.is_iso_apply
  {X Y : graded_object ℕ V} (f : X ⟶ Y) [is_iso f] (k : ℕ) : is_iso (f k) :=
sorry

namespace homotopy_category

def graded_homology_functor {α : Type*} (c : complex_shape α) :
  (homotopy_category V c) ⥤ (graded_object α V) :=
category_theory.quotient.lift _ (graded_homology_functor V c)
  (λ C D f g ⟨h⟩, funext (homology_map_eq_of_homotopy h))

def graded_homology_factors {α : Type*} (c : complex_shape α) :
  quotient V c ⋙ graded_homology_functor V c ≅ _root_.graded_homology_functor V c :=
category_theory.quotient.lift.is_lift _ _ _

-- TODO this really should be constructed using a monoidal version of
-- `category_theory.quotient.lift`
def graded_homology_lax :
  lax_monoidal_functor (homotopy_category V (complex_shape.down ℕ)) (graded_object ℕ V) :=
{ ε := sorry,
  μ := λ X Y, (_root_.graded_homology_lax V).μ X.as Y.as,
  μ_natural' := sorry,
  associativity' := sorry,
  left_unitality' := sorry,
  right_unitality' := sorry,
  ..graded_homology_functor V _ }

@[simp] lemma graded_homology_lax_μ (X Y : chain_complex V ℕ) :
  (graded_homology_lax V).μ ((quotient _ _).obj X) ((quotient _ _).obj Y) =
    (_root_.graded_homology_lax V).μ X Y :=
rfl -- Really faking it here, as there's still a sorry inside.

instance graded_homology_tensorator_mono
  (X Y : homotopy_category V (complex_shape.down ℕ)) :
  mono ((graded_homology_lax V).μ X Y) := sorry

end homotopy_category

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
example : preadditive (Module.{0} R) := by apply_instance

-- Verify we have everything we need to do `Tor`.
example : abelian (Module.{0} R) := by apply_instance
example : enough_projectives (Module.{0} R) := by apply_instance
example : has_projective_resolutions (Module.{0} R) := by apply_instance

abbreviation H' (n : ℕ) (X : chain_complex (Module.{0} R) ℕ) : Module.{0} R :=
  (homology_functor (Module.{0} R) _ n).obj X

def chain_complex.kunneth.cokernel_iso (X Y : chain_complex (Module.{0} R) ℕ)
  (free : ∀ i, module.free R (X.X i)) (k : ℕ) :
  cokernel ((graded_homology_lax _).μ X Y k) ≅
    biproduct (λ p : finset.nat.antidiagonal_prev k, ((Tor _ 1).obj (H' p.1.1 X)).obj (H' p.1.2 Y)) :=
-- This is the hardest sorry so far today.
sorry

abbreviation H'' (n : ℕ) (X : homotopy_category (Module.{0} R) (complex_shape.down ℕ)) : Module.{0} R :=
  (homotopy_category.homology_functor (Module.{0} R) _ n).obj X

-- FIXME why does this time out?

def foo (X Y : homotopy_category (Module.{0} R) (complex_shape.down ℕ)) (k : ℕ) : Module.{0} R :=
(cokernel ((homotopy_category.graded_homology_lax (Module.{0} R)).μ X Y k))

def bar (X Y : homotopy_category (Module.{0} R) (complex_shape.down ℕ)) (k : ℕ) : Module.{0} R :=
(biproduct (λ p : finset.nat.antidiagonal_prev k, ((Tor _ 1).obj (H'' p.1.1 X)).obj (H'' p.1.2 Y)))

def homotopy_category.kunneth.cokernel_iso (X Y : homotopy_category (Module.{0} R) (complex_shape.down ℕ))
  (free : ∀ i, module.free R (X.as.X i)) (k : ℕ) :
  (foo X Y k) ≅ (bar X Y k) :=
sorry

-- Some more missing API about short exact sequences.
-- Perhaps some of this generalizes beyond abelian categories?
namespace category_theory.short_exact

variables {𝒜 : Type*} [category 𝒜] [abelian 𝒜]

variables {A B C : 𝒜} {f : A ⟶ B} {g : B ⟶ C}

example : category_theory.epi (cokernel.π f) := by apply_instance

instance (w : f ≫ cokernel.π f = 0) :
  is_iso (image_to_kernel f (cokernel.π f) w) :=
begin
  use (kernel_subobject_iso (cokernel.π f)).hom ≫ (abelian.image_iso_image f).hom ≫
    (image_subobject_iso f).inv,
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
  short_exact (i ≫ f) g :=
sorry
theorem comp_iso_middle {B' : 𝒜} {f : A ⟶ B} (i : B ⟶ B') {g : B' ⟶ C} [is_iso i] :
  short_exact (f ≫ i) g ↔ short_exact f (i ≫ g) :=
sorry
theorem comp_iso_right {C' : 𝒜} (i : C ⟶ C') [is_iso i] (w : short_exact f g) :
  short_exact f (g ≫ i) :=
sorry

theorem of_mono_cokernel_iso [category_theory.mono f] [has_cokernel f] (i : cokernel f ≅ C) :
  short_exact f (cokernel.π f ≫ i.hom) := of_mono_cokernel.comp_iso_right _

theorem of_epi_kernel_iso [category_theory.epi g] [has_kernel g] (i : kernel g ≅ A) :
  short_exact (i.inv ≫ kernel.ι g) g :=
-- TODO dualize the above.
sorry

end category_theory.short_exact

open category_theory.short_exact
open chain_complex.kunneth

theorem chain_complex.kunneth (X Y : chain_complex (Module.{0} R) ℕ)
  (free : ∀ i, module.free R (X.X i)) (k : ℕ) :
  short_exact ((graded_homology_lax _).μ X Y k)
    (cokernel.π ((graded_homology_lax _).μ X Y k) ≫ (cokernel_iso X Y free k).hom) :=
of_mono_cokernel_iso _

theorem homotopy_category.kunneth (X Y : homotopy_category (Module.{0} R) (complex_shape.down ℕ))
  (free : ∀ i, module.free R (X.as.X i)) (k : ℕ) :
  short_exact ((homotopy_category.graded_homology_lax _).μ X Y k)
    (cokernel.π ((homotopy_category.graded_homology_lax _).μ X Y k) ≫ (homotopy_category.kunneth.cokernel_iso X Y free k).hom) :=
of_mono_cokernel_iso _


end

/-!
# Step 2, Eilenberg-Zilber
-/
section
variables {V : Type*} [category V] [monoidal_category V] [preadditive V] [has_finite_biproducts V]

abbreviation C (X : simplicial_object V) := (alternating_face_map_complex V).obj X

variables (X Y : simplicial_object V)

def alexander_whitney : C (X ⊗ Y) ⟶ C X ⊗ C Y := sorry
def eilenberg_zilber : C X ⊗ C Y ⟶ C (X ⊗ Y) := sorry

def homotopy_1 : homotopy (eilenberg_zilber X Y ≫ alexander_whitney X Y) (𝟙 _) := sorry
def homotopy_2 : homotopy (alexander_whitney X Y ≫ eilenberg_zilber X Y) (𝟙 _) := sorry

instance : is_iso ((homotopy_category.quotient V _).map (eilenberg_zilber X Y)) :=
{ out := ⟨(homotopy_category.quotient V _).map (alexander_whitney X Y),
    homotopy_category.eq_of_homotopy _ _ (homotopy_1 X Y),
    homotopy_category.eq_of_homotopy _ _ (homotopy_2 X Y)⟩ }

variable (V)

def alternating_face_map_complex_monoidal :
  monoidal_functor (simplicial_object V) (homotopy_category V (complex_shape.down ℕ)) :=
{ ε := sorry,
  μ := λ X Y, (homotopy_category.quotient V _).map (eilenberg_zilber X Y),
  μ_natural' := sorry,
  associativity' := sorry,
  left_unitality' := sorry,
  right_unitality' := sorry,
  ε_is_iso := sorry,
  μ_is_iso := λ X Y, by apply_instance,
  ..(alternating_face_map_complex V ⋙ homotopy_category.quotient V _) }

end

/-!
# Putting it all together!

We now give a proof of the Kunneth formula for topological spaces
in terms of the Kunneth formula for complexes, Eilenberg-Zilber
-/

def singular_chains_monoidal (R : Type) [comm_ring R] :
  monoidal_functor Top.{0} (homotopy_category (Module.{0} R) (complex_shape.down ℕ)) :=
Top.to_sModule_monoidal R ⊗⋙ alternating_face_map_complex_monoidal _

def singular_homology_lax (R : Type) [comm_ring R] :
  lax_monoidal_functor Top.{0} (graded_object ℕ (Module.{0} R)) :=
(singular_chains_monoidal R).to_lax_monoidal_functor.comp
  (homotopy_category.graded_homology_lax (Module R))

example (X : Top.{0}) (k : ℕ) :
  (singular_homology_lax ℤ).obj X k = (singular_homology k ℤ).obj X :=
rfl
-- This might not look like much, but it's a good sign.
-- It says that we've set up the lax monoidal version of singular homology
-- so that it is definitionally equal to the usual version.

theorem singular_chains_free (X : Top.{0}) (i : ℕ) :
  module.free ℤ (((singular_chains ℤ).obj X).X i) :=
begin
  dsimp [singular_chains, Top.to_sModule],
  apply_instance,
end

def kunneth_mono' (k : ℕ) (X Y : Top.{0}) :
  biproduct (λ p : finset.nat.antidiagonal k, (H p.1.1).obj X ⊗ (H p.1.2).obj Y)
   ⟶ (H k).obj (X ⊗ Y) :=
(singular_homology_lax ℤ).μ X Y k

theorem kunneth' (k : ℕ) (X Y : Top.{0}) :
  ∃ (g : (H k).obj (X ⊗ Y) ⟶
    biproduct (λ p : finset.nat.antidiagonal_prev k,
      ((Tor _ 1).obj ((H p.1.1).obj X)).obj ((H p.1.2).obj Y))),
  short_exact (kunneth_mono' k X Y) g :=
begin
  dsimp only [kunneth_mono', singular_homology_lax],
  dsimp only [lax_monoidal_functor.comp_μ],
  split,
  { -- This postpones the choice of `g` as a second goal;
    -- it will later be solved by unification.
    { apply (category_theory.short_exact.comp_iso_middle _).mpr,
      swap, apply_instance,
      dsimp [singular_chains_monoidal, alternating_face_map_complex_monoidal],
      convert chain_complex.kunneth ((singular_chains ℤ).obj X) ((singular_chains ℤ).obj Y) _ k
        using 1,
      { apply (is_iso.eq_inv_comp _).mp,
        { -- This is where we write down `g`!
          refl, },
        apply_instance, },
      { -- Have to remember that singular chains are free.
        exact singular_chains_free X, }, },

  },
end
