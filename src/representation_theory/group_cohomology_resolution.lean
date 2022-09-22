/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import algebraic_topology.alternating_face_map_complex
import algebraic_topology.cech_nerve
import algebraic_topology.extra_degeneracy
import category_theory.abelian.exact
import representation_theory.basic
import representation_theory.Rep
import representation_theory.homology_lemmas

/-!
# The structure of the `k[G]`-module `k[Gⁿ]`

This file contains facts about an important `k[G]`-module structure on `k[Gⁿ]`, where `k` is a
commutative ring and `G` is a group. The module structure arises from the representation
`G →* End(k[Gⁿ])` induced by the diagonal action of `G` on `Gⁿ.`

In particular, we define an isomorphism of `k`-linear `G`-representations between `k[Gⁿ⁺¹]` and
`k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`).

This allows us to define a `k[G]`-basis on `k[Gⁿ⁺¹]`, by mapping the natural `k[G]`-basis of
`k[G] ⊗ₖ k[Gⁿ]` along the isomorphism.

We then define the standard resolution of `k` as a trivial representation, by
taking the alternating face map complex associated to an appropriate simplicial `k`-linear
`G`-representation. This simplicial object is the `linearization` of the simplicial `G`-set given
by the universal cover of the classifying space of `G`. We prove this `G`-set is isomorphic to the
Čech nerve of the natural arrow of `G`-sets `G ⟶ {pt}`.

## Main definitions

 * `group_cohomology.resolution.to_tensor`
 * `group_cohomology.resolution.of_tensor`
 * `Rep.of_mul_action`
 * `group_cohomology.resolution.equiv_tensor`
 * `group_cohomology.resolution.of_mul_action_basis`
 * `classifying_space_universal_cover`
 * `classifying_space_universal_cover.cech_nerve_iso`
 * `group_cohomology.resolution`

## TODO

 * Use the freeness of `k[Gⁿ⁺¹]` to build a projective resolution of the (trivial) `k[G]`-module
   `k`, and so develop group cohomology.

## Implementation notes

We express `k[G]`-module structures on a module `k`-module `V` using the `representation`
definition. We avoid using instances `module (G →₀ k) V` so that we do not run into possible
scalar action diamonds.

We also use the category theory library to bundle the type `k[Gⁿ]` - or more generally `k[H]` when
`H` has `G`-action - and the representation together, as a term of type `Rep k G`, and call it
`Rep.of_mul_action k G H.` This enables us to express the fact that certain maps are
`G`-equivariant by constructing morphisms in the category `Rep k G`, i.e., representations of `G`
over `k`.
-/

noncomputable theory

universes u

variables {k G : Type u} [comm_ring k] {n : ℕ}

open_locale tensor_product
open category_theory

local notation `Gⁿ` := fin n → G
local notation `Gⁿ⁺¹` := fin (n + 1) → G

namespace group_cohomology.resolution

open finsupp (hiding lift) fin (partial_prod) representation

section basis
variables (k G n) [group G]

/-- The `k`-linear map from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` sending `(g₀, ..., gₙ)`
to `g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. -/
def to_tensor_aux :
  ((fin (n + 1) → G) →₀ k) →ₗ[k] (G →₀ k) ⊗[k] ((fin n → G) →₀ k) :=
finsupp.lift ((G →₀ k) ⊗[k] ((fin n → G) →₀ k)) k (fin (n + 1) → G)
  (λ x, single (x 0) 1 ⊗ₜ[k] single (λ i, (x i)⁻¹ * x i.succ) 1)

/-- The `k`-linear map from `k[G] ⊗ₖ k[Gⁿ]` to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)`. -/
def of_tensor_aux :
  (G →₀ k) ⊗[k] ((fin n → G) →₀ k) →ₗ[k] ((fin (n + 1) → G) →₀ k) :=
tensor_product.lift (finsupp.lift _ _ _ $ λ g, finsupp.lift _ _ _
  (λ f, single (g • partial_prod f) (1 : k)))

variables {k G n}

lemma to_tensor_aux_single (f : Gⁿ⁺¹) (m : k) :
  to_tensor_aux k G n (single f m) = single (f 0) m ⊗ₜ single (λ i, (f i)⁻¹ * f i.succ) 1 :=
begin
  simp only [to_tensor_aux, lift_apply, sum_single_index, tensor_product.smul_tmul'],
  { simp },
end

lemma to_tensor_aux_of_mul_action (g : G) (x : Gⁿ⁺¹) :
  to_tensor_aux k G n (of_mul_action k G Gⁿ⁺¹ g (single x 1)) =
  tensor_product.map (of_mul_action k G G g) 1 (to_tensor_aux k G n (single x 1)) :=
by simp [of_mul_action_def, to_tensor_aux_single, mul_assoc, inv_mul_cancel_left]

lemma of_tensor_aux_single (g : G) (m : k) (x : Gⁿ →₀ k) :
  of_tensor_aux k G n ((single g m) ⊗ₜ x) =
  finsupp.lift (Gⁿ⁺¹ →₀ k) k Gⁿ (λ f, single (g • partial_prod f) m) x :=
by simp [of_tensor_aux, sum_single_index, smul_sum, mul_comm m]

lemma of_tensor_aux_comm_of_mul_action (g h : G) (x : Gⁿ) :
  of_tensor_aux k G n (tensor_product.map (of_mul_action k G G g)
  (1 : module.End k (Gⁿ →₀ k)) (single h (1 : k) ⊗ₜ single x (1 : k))) =
  of_mul_action k G Gⁿ⁺¹ g (of_tensor_aux k G n (single h 1 ⊗ₜ single x 1)) :=
begin
  simp [of_mul_action_def, of_tensor_aux_single, mul_smul],
end

lemma to_tensor_aux_left_inv (x : Gⁿ⁺¹ →₀ k) :
  of_tensor_aux _ _ _ (to_tensor_aux _ _ _ x) = x :=
begin
  refine linear_map.ext_iff.1 (@finsupp.lhom_ext _ _ _ k _ _ _ _ _
    (linear_map.comp (of_tensor_aux _ _ _) (to_tensor_aux _ _ _)) linear_map.id (λ x y, _)) x,
  dsimp,
  rw [to_tensor_aux_single x y, of_tensor_aux_single, finsupp.lift_apply, finsupp.sum_single_index,
    one_smul, fin.partial_prod_left_inv],
  { rw zero_smul }
end

lemma to_tensor_aux_right_inv (x : (G →₀ k) ⊗[k] (Gⁿ →₀ k)) :
  to_tensor_aux _ _ _ (of_tensor_aux _ _ _ x) = x :=
begin
  refine tensor_product.induction_on x (by simp) (λ y z, _) (λ z w hz hw, by simp [hz, hw]),
  rw [←finsupp.sum_single y, finsupp.sum, tensor_product.sum_tmul],
  simp only [finset.smul_sum, linear_map.map_sum],
  refine finset.sum_congr rfl (λ f hf, _),
  simp only [of_tensor_aux_single, finsupp.lift_apply, finsupp.smul_single',
    linear_map.map_finsupp_sum, to_tensor_aux_single, fin.partial_prod_right_inv],
  dsimp,
  simp only [fin.partial_prod_zero, mul_one],
  conv_rhs {rw [←finsupp.sum_single z, finsupp.sum, tensor_product.tmul_sum]},
  exact finset.sum_congr rfl (λ g hg, show _ ⊗ₜ _ = _, by
    rw [←finsupp.smul_single', tensor_product.smul_tmul, finsupp.smul_single_one])
end

variables (k G n)

/-- A hom of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts
by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. -/
def to_tensor : Rep.of_mul_action k G (fin (n + 1) → G) ⟶ Rep.of
  ((representation.of_mul_action k G G).tprod (1 : G →* module.End k ((fin n → G) →₀ k))) :=
{ hom := to_tensor_aux k G n,
  comm' := λ g, by ext; exact to_tensor_aux_of_mul_action _ _ }

/-- A hom of `k`-linear representations of `G` from `k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts
by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)`. -/
def of_tensor :
  Rep.of ((representation.of_mul_action k G G).tprod (1 : G →* module.End k ((fin n → G) →₀ k)))
    ⟶ Rep.of_mul_action k G (fin (n + 1) → G) :=
{ hom := of_tensor_aux k G n,
  comm' := λ g, by { ext, congr' 1, exact (of_tensor_aux_comm_of_mul_action _ _ _) }}

variables {k G n}

@[simp] lemma to_tensor_single (f : Gⁿ⁺¹) (m : k) :
  (to_tensor k G n).hom (single f m) = single (f 0) m ⊗ₜ single (λ i, (f i)⁻¹ * f i.succ) 1 :=
to_tensor_aux_single _ _

@[simp] lemma of_tensor_single (g : G) (m : k) (x : Gⁿ →₀ k) :
  (of_tensor k G n).hom ((single g m) ⊗ₜ x) =
  finsupp.lift (Rep.of_mul_action k G Gⁿ⁺¹) k Gⁿ (λ f, single (g • partial_prod f) m) x :=
of_tensor_aux_single _ _ _

lemma of_tensor_single' (g : G →₀ k) (x : Gⁿ) (m : k) :
  (of_tensor k G n).hom (g ⊗ₜ single x m) =
  finsupp.lift _ k G (λ a, single (a • partial_prod x) m) g :=
by simp [of_tensor, of_tensor_aux]

variables (k G n)

/-- An isomorphism of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on
which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. -/
def equiv_tensor : (Rep.of_mul_action k G (fin (n + 1) → G)) ≅ Rep.of
  ((representation.of_mul_action k G G).tprod (1 : representation k G ((fin n → G) →₀ k))) :=
Action.mk_iso (linear_equiv.to_Module_iso
{ inv_fun := of_tensor_aux k G n,
  left_inv := to_tensor_aux_left_inv,
  right_inv := λ x, by convert to_tensor_aux_right_inv x,
  ..to_tensor_aux k G n }) (to_tensor k G n).comm

@[simp] lemma equiv_tensor_def :
  (equiv_tensor k G n).hom = to_tensor k G n := rfl

@[simp] lemma equiv_tensor_inv_def :
  (equiv_tensor k G n).inv = of_tensor k G n := rfl

/-- The `k[G]`-linear isomorphism `k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹]`, where the `k[G]`-module structure on
the lefthand side is `tensor_product.left_module`, whilst that of the righthand side comes from
`representation.as_module`. Allows us to use `basis.algebra_tensor_product` to get a `k[G]`-basis
of the righthand side. -/
def of_mul_action_basis_aux : (monoid_algebra k G ⊗[k] ((fin n → G) →₀ k)) ≃ₗ[monoid_algebra k G]
  (of_mul_action k G (fin (n + 1) → G)).as_module :=
{ map_smul' := λ r x,
  begin
    rw [ring_hom.id_apply, linear_equiv.to_fun_eq_coe, ←linear_equiv.map_smul],
    congr' 1,
    refine x.induction_on _ (λ x y, _) (λ y z hy hz, _),
    { simp only [smul_zero] },
    { simp only [tensor_product.smul_tmul'],
      show (r * x) ⊗ₜ y = _,
      rw [←of_mul_action_self_smul_eq_mul, smul_tprod_one_as_module] },
    { rw [smul_add, hz, hy, smul_add], }
  end, .. ((Rep.equivalence_Module_monoid_algebra.1).map_iso
    (equiv_tensor k G n).symm).to_linear_equiv }

/-- A `k[G]`-basis of `k[Gⁿ⁺¹]`, coming from the `k[G]`-linear isomorphism
`k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹].` -/
def of_mul_action_basis  :
  basis (fin n → G) (monoid_algebra k G) (of_mul_action k G (fin (n + 1) → G)).as_module :=
@basis.map _ (monoid_algebra k G) (monoid_algebra k G ⊗[k] ((fin n → G) →₀ k))
  _ _ _ _ _ _ (@algebra.tensor_product.basis k _ (monoid_algebra k G) _ _ ((fin n → G) →₀ k) _ _
  (fin n → G) ⟨linear_equiv.refl k _⟩) (of_mul_action_basis_aux k G n)

lemma of_mul_action_free :
  module.free (monoid_algebra k G) (of_mul_action k G (fin (n + 1) → G)).as_module :=
module.free.of_basis (of_mul_action_basis k G n)

end basis
end group_cohomology.resolution
variables (G)

/-- The simplicial `G`-set sending `[n]` to `Gⁿ⁺¹` equipped with the diagonal action of `G`. -/
def classifying_space_universal_cover [monoid G] :
  simplicial_object (Action (Type u) $ Mon.of G) :=
{ obj := λ n, Action.of_mul_action G (fin (n.unop.len + 1) → G),
  map := λ m n f,
  { hom := λ x, x ∘ f.unop.to_order_hom,
    comm' := λ g, rfl },
  map_id' := λ n, rfl,
  map_comp' := λ i j k f g, rfl }

namespace classifying_space_universal_cover

open category_theory.limits category_theory.arrow
variables (G) [monoid G] (m : simplex_categoryᵒᵖ)

/-- The natural hom of `G`-sets `G ⟶ {pt}` as an arrow. -/
def arrow : arrow (Action (Type u) (Mon.of G)) :=
⟨Action.of_mul_action G G, default, ⟨λ x, punit.star, λ g, rfl⟩⟩

/-- The diagram `option (fin (m + 1)) ⥤ G-Set` sending `none` to `{pt}` and `some j` to `G` (with
the left regular action). -/
abbreviation wide_cospan :
  wide_pullback_shape (fin ((opposite.unop m).len + 1)) ⥤ Action (Type u) (Mon.of G) :=
wide_pullback_shape.wide_cospan default (λ (i : fin (m.unop.len + 1)), Action.of_mul_action G G)
  (λ i, ⟨λ x, punit.star, λ g, rfl⟩)

/-- The `G-Set` `Gᵐ⁺¹` (with the diagonal action) is the vertex of a cone on `wide_cospan G m`. -/
def wide_cospan.cone : cone (wide_cospan G m) :=
{ X := Action.of_mul_action G (fin (m.unop.len + 1) → G),
  π :=
  { app := λ X, option.cases_on X (⟨λ x, punit.star, λ g, rfl⟩)
      (λ i, ⟨λ x, x i, λ x, by ext; refl⟩),
    naturality' := λ X Y f, by { cases f, cases X, obviously }}}

/-- The cone on `wide_cospan G m` with `Gᵐ⁺¹` as a vertex is a limit. -/
def wide_cospan.is_limit : is_limit (wide_cospan.cone G m) :=
{ lift := λ s,
  { hom := λ x j, (s.π.app (some j)).hom x,
    comm' := λ g, by ext; convert congr_fun ((s.π.app (some j)).comm' g) i },
  fac' := λ s j, option.cases_on j (by ext) (λ j, by ext; refl),
  uniq' := λ s f h, by ext x j; simpa only [←h (some j)] }

instance has_wide_pullback : has_wide_pullback (arrow G).right
  (λ i : fin (m.unop.len + 1), (arrow G).left) (λ i, (arrow G).hom) :=
⟨⟨⟨wide_cospan.cone G m, wide_cospan.is_limit G m⟩⟩⟩

/-- The `m`th object of the Čech nerve of the `G`-set hom `G ⟶ {pt}` is isomorphic to `Gᵐ⁺¹` with
the diagonal action. -/
def cech_nerve_obj_iso :
  (cech_nerve (arrow G)).obj m ≅ Action.of_mul_action G (fin (m.unop.len + 1) → G) :=
is_limit.cone_point_unique_up_to_iso (limit.is_limit _) (wide_cospan.is_limit G m)

/-- The Čech nerve of the `G`-set hom `G ⟶ {pt}` is naturally isomorphic to `EG`, the universal
cover of the classifying space of `G` as a simplicial `G`-set. -/
def cech_nerve_iso : cech_nerve (arrow G) ≅ classifying_space_universal_cover G :=
(@nat_iso.of_components _ _ _ _ (classifying_space_universal_cover G) (cech_nerve (arrow G))
(λ n, (cech_nerve_obj_iso G n).symm) $ λ m n f,  wide_pullback.hom_ext (λ j, (arrow G).hom) _ _
(λ j, begin
  simp only [category.assoc],
  dsimp,
  rw wide_pullback.lift_π,
  erw [limit.cone_point_unique_up_to_iso_hom_comp (wide_cospan.is_limit G n),
    limit.cone_point_unique_up_to_iso_hom_comp (wide_cospan.is_limit G m)],
  refl,
end) (by ext)).symm

variables (k G)
def resolution := (algebraic_topology.alternating_face_map_complex (Rep k G)).obj
  (classifying_space_universal_cover G ⋙ (Rep.linearization k G).1.1)

def forget_resn := ((forget₂ (Rep k G) (Module.{u} k)).map_homological_complex _).obj
(resolution k G)

def to_Module := (Rep.linearization k G).1.1 ⋙ forget₂ (Rep k G) (Module.{u} k)
def to_Module2 := forget (Action (Type u) $ Mon.of G) ⋙ Module.free k

def split_epi_aux : split_epi (arrow G).hom.hom :=
{ section_ := λ x, (1 : G),
  id' := by ext }

def split_epi : split_epi ((to_Module k G).map_arrow.obj (arrow G)).hom :=
{ section_ := (split_epi.map (split_epi_aux G) ((forget _) ⋙ Module.free k)).1,
  id' := (split_epi.map (split_epi_aux G) ((forget _) ⋙ Module.free k)).2 }

def aug_nerve := ((to_Module k G).map_arrow.obj $ arrow G).augmented_cech_nerve

def cech_nerve_extra_degen :
  simplicial_object.augmented.extra_degeneracy (aug_nerve k G) :=
augmented_cech_nerve.extra_degeneracy _ (split_epi k G)

def homotopy_equiv := simplicial_object.augmented.extra_degeneracy.preadditive.homotopy_equivalence
  (cech_nerve_extra_degen k G)

def nerve_complex := (algebraic_topology.alternating_face_map_complex.obj
  (simplicial_object.augmented.drop.obj (aug_nerve k G)))

theorem nerve_complex_exact (n : ℕ) :
  exact ((nerve_complex k G).d (n + 2) (n + 1)) ((nerve_complex k G).d (n + 1) n) :=
(preadditive.exact_iff_homology_zero _ _).2 ⟨(nerve_complex k G).d_comp_d _ _ _,
  ⟨(chain_complex.succth _ _).symm.trans ((homology_obj_iso_of_homotopy_equiv
  (homotopy_equiv k G) _).trans homology_zero_zero)⟩⟩

def aux (n : simplex_categoryᵒᵖ) :
  (wide_pullback_shape.wide_cospan ((to_Module k G).obj (arrow G).right)
    (λ (i : fin ((opposite.unop n).len + 1)), (to_Module k G).obj (arrow G).left)
    (λ (i : fin ((opposite.unop n).len + 1)), (to_Module k G).map (arrow G).hom))
  ≅ (wide_pullback_shape.wide_cospan (arrow G).right (λ (i : fin ((opposite.unop n).len + 1)),
   (arrow G).left) (λ (i : fin ((opposite.unop n).len + 1)), (arrow G).hom) ⋙ to_Module k G) :=
nat_iso.of_components (λ m, option.rec_on m (iso.refl _) (λ i, iso.refl _)) $ λ i j f,
begin
  cases f,
  { cases i,
    all_goals
    { ext a b,
      show finsupp.single a (1 : k) _ = finsupp.map_domain _ _ _,
      dsimp,
      rw finsupp.map_domain_single,
      congr }},
  { refl },
end

instance hmmm (n : simplex_categoryᵒᵖ) : preserves_limit (wide_pullback_shape.wide_cospan
  (arrow G).right (λ (i : fin ((opposite.unop n).len + 1)),
  (arrow G).left) (λ (i : fin ((opposite.unop n).len + 1)), (arrow G).hom))
    (to_Module2 k G) :=
preserves_limit_of_preserves_limit_cone (wide_cospan.is_limit G n) $
sorry

def nerve_complex_iso_aux (n : simplex_categoryᵒᵖ) :
  ((to_Module k G).map_arrow.obj $ arrow G).cech_nerve.obj n ≅
  (((simplicial_object.whiskering _ _).obj (to_Module k G)).obj
  (arrow G).cech_nerve).obj n :=
(has_limit.iso_of_nat_iso (aux k G n)).trans (@preserves_limit_iso _ _ _
    _ _ _ _ (wide_pullback_shape.wide_cospan _ _ _)
    (classifying_space_universal_cover.hmmm _ _ _) _ _).symm

def nerve_complex_iso :
  nerve_complex k G ≅ forget_resn k G :=
homological_complex.hom.iso_of_components (λ i,
(nerve_complex_iso_aux k G (opposite.op $ simplex_category.mk i)).trans ((to_Module k G).map_iso
(cech_nerve_obj_iso G (opposite.op $ simplex_category.mk i)))) $
begin
  intros i j hij,
  cases hij,
  dsimp at *,
  sorry,
end

variables {k G}

lemma ffs2 {k : Type u} [comm_ring k] {C D : chain_complex (Module.{u} k) ℕ}
  (H : C ≅ D) {i j : ℕ} (hij : (complex_shape.down ℕ).rel i j) :
  H.2.1 i ≫ C.d i j ≫ H.1.1 j = D.d i j :=
begin
  rw [←category.assoc, H.2.2 i j hij, category.assoc, ←homological_complex.comp_f,
    homological_complex.congr_hom H.4 j, homological_complex.id_f, category.comp_id],
end

instance ffs1 {k : Type u} [comm_ring k] (C D : chain_complex (Module.{u} k) ℕ)
  (H : C ≅ D) (i : ℕ) : is_iso (H.1.1 i) :=
⟨⟨H.2.1 i, homological_complex.congr_hom H.3 i, homological_complex.congr_hom H.4 i⟩⟩

instance ffs4  {k : Type u} [comm_ring k] (C D : chain_complex (Module.{u} k) ℕ)
  (H : C ≅ D) (i : ℕ) : is_iso (H.2.1 i) :=
⟨⟨H.1.1 i, homological_complex.congr_hom H.4 i, homological_complex.congr_hom H.3 i⟩⟩

lemma yeugh {k : Type u} [comm_ring k] {C D : chain_complex (Module.{u} k) ℕ}
  (H : C ≅ D) (i j l : ℕ) (hij : (complex_shape.down ℕ).rel i j) (hjl : (complex_shape.down ℕ).rel j l) :
  exact (C.d i j) (C.d j l) ↔ exact (D.d i j) (D.d j l) :=
begin
  rw [←ffs2 H hij, ←ffs2 H hjl, exact_iso_comp, ←category.assoc, exact_comp_iso],
  exact (exact_comp_hom_inv_comp_iff (homological_complex.hom.iso_app H j)).symm,
end

theorem noice (n : ℕ) :
  exact ((resolution k G).d (n + 2) (n + 1)) ((resolution k G).d (n + 1) n) :=
functor.exact_of_exact_map (forget₂ (Rep k G) (Module.{u} k)) ((yeugh (nerve_complex_iso _ _).symm
  (n + 2) (n + 1) n (by simp) (by simp)).2 (nerve_complex_exact _ _ _))

end classifying_space_universal_cover
namespace group_cohomology.resolution

section differential
variables (k G)
/-- The `k`-linear map underlying the differential in the standard resolution of `k` as a trivial
`k`-linear `G`-representation. It sends `(g₀, ..., gₙ) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ)`. -/
def d (n : ℕ) : ((fin (n + 1) → G) →₀ k) →ₗ[k] ((fin n → G) →₀ k) :=
finsupp.lift ((fin n → G) →₀ k) k (fin (n + 1) → G) (λ g, (@finset.univ (fin (n + 1)) _).sum
  (λ p, finsupp.single (g ∘ p.succ_above) ((-1 : k) ^ (p : ℕ))))

variables {k G}

@[simp] lemma d_of {n : ℕ} (c : fin (n + 1) → G) :
  d k G n (finsupp.single c 1) = finset.univ.sum (λ p : fin (n + 1), finsupp.single
    (c ∘ p.succ_above) ((-1 : k) ^ (p : ℕ))) :=
by simp [d]

end differential
end group_cohomology.resolution
variables (k G) [monoid G]

/-- The standard resolution of `k` as a trivial representation, defined as the alternating
face map complex of a simplicial `k`-linear `G`-representation. -/
def group_cohomology.resolution := (algebraic_topology.alternating_face_map_complex (Rep k G)).obj
  (classifying_space_universal_cover G ⋙ (Rep.linearization k G).1.1)

namespace group_cohomology.resolution

/- Leaving this here for now - not sure it should exist or where it should go. Everything I tried
to avoid this lemma was messy or gave me weird errors. -/
lemma int_cast_smul {k V : Type*} [comm_ring k] [add_comm_group V] [module k V] (r : ℤ) (x : V) :
  (r : k) • x = r • x :=
algebra_map_smul k r x

/-- The `n`th object of the standard resolution of `k` is definitionally isomorphic to `k[Gⁿ⁺¹]`
equipped with the representation induced by the diagonal action of `G`. -/
def X_iso (n : ℕ) :
  (group_cohomology.resolution k G).X n ≅ Rep.of_mul_action k G (fin (n + 1) → G) := iso.refl _

/-- Simpler expression for the differential in the standard resolution of `k` as a
`G`-representation. It sends `(g₀, ..., gₙ₊₁) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ₊₁)`. -/
theorem d_eq (n : ℕ) :
  ((group_cohomology.resolution k G).d (n + 1) n).hom = d k G (n + 1) :=
begin
  ext x y,
  dsimp [group_cohomology.resolution],
  simpa [←@int_cast_smul k, simplicial_object.δ],
end

end group_cohomology.resolution
