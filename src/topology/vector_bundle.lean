/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sebastien Gouezel
-/

import topology.topological_fiber_bundle
import topology.algebra.module
import topology.continuous_function.algebra
import linear_algebra.dual


/-!
# Topological vector bundles

In this file we define topological vector bundles.

Let `B` be the base space. In our formalism, a topological vector bundle is by definition the type
`bundle.total_space E` where `E : B → Type*` is a function associating to
`x : B` the fiber over `x`. This type `bundle.total_space E` is just a type synonym for
`Σ (x : B), E x`, with the interest that one can put another topology than on `Σ (x : B), E x`
which has the disjoint union topology.

To have a topological vector bundle structure on `bundle.total_space E`,
one should addtionally have the following data:

* `F` should be a topological space and a module over a semiring `R`;
* There should be a topology on `bundle.total_space E`, for which the projection to `B` is
a topological fiber bundle with fiber `F` (in particular, each fiber `E x` is homeomorphic to `F`);
* For each `x`, the fiber `E x` should be a topological vector space over `R`, and the injection
from `E x` to `bundle.total_space F E` should be an embedding;
* The most important condition: around each point, there should be a bundle trivialization which
is a continuous linear equiv in the fibers.

If all these conditions are satisfied, we register the typeclass
`topological_vector_bundle R F E`. We emphasize that the data is provided by other classes, and
that the `topological_vector_bundle` class is `Prop`-valued.

The point of this formalism is that it is unbundled in the sense that the total space of the bundle
is a type with a topology, with which one can work or put further structure, and still one can
perform operations on topological vector bundles (which are yet to be formalized). For instance,
assume that `E₁ : B → Type*` and `E₂ : B → Type*` define two topological vector bundles over `R`
with fiber models `F₁` and `F₂` which are normed spaces. Then one can construct the vector bundle of
continuous linear maps from `E₁ x` to `E₂ x` with fiber `E x := (E₁ x →L[R] E₂ x)` (and with the
topology inherited from the norm-topology on `F₁ →L[R] F₂`, without the need to define the strong
topology on continuous linear maps between general topological vector spaces). Let
`vector_bundle_continuous_linear_map R F₁ E₁ F₂ E₂ (x : B)` be a type synonym for `E₁ x →L[R] E₂ x`.
Then one can endow
`bundle.total_space (vector_bundle_continuous_linear_map R F₁ E₁ F₂ E₂)`
with a topology and a topological vector bundle structure.

Similar constructions can be done for tensor products of topological vector bundles, exterior
algebras, and so on, where the topology can be defined using a norm on the fiber model if this
helps.

## Sections

In this file we also prove that sections of vector bundles inherit the algebraic structures of the
fibers. The proofs of this are the standard mathematical proofs: continuity is read through
trivializations on the fibers, where checking the continuity of algebraic operations is
straightforward.

-/

noncomputable theory

open bundle set

variables (R : Type*) {B : Type*} (F : Type*) (E : B → Type*)
  [topological_space F] [topological_space (total_space E)] [topological_space B]

section monoid

variables [semiring R] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]
  [add_comm_monoid F] [module R F]

section trivialization

/-- Local trivialization for vector bundles. -/
@[nolint has_inhabited_instance]
structure topological_vector_bundle.trivialization extends bundle_trivialization F (proj E) :=
(linear : ∀ x ∈ base_set, is_linear_map R (λ y : (E x), (to_fun y).2))

instance : has_coe_to_fun (topological_vector_bundle.trivialization R F E) :=
⟨λ _, (total_space E → B × F), λ e, e.to_bundle_trivialization⟩

instance : has_coe (topological_vector_bundle.trivialization R F E)
  (bundle_trivialization F (proj E)) :=
⟨topological_vector_bundle.trivialization.to_bundle_trivialization⟩

namespace topological_vector_bundle

variables {R F E}

lemma trivialization.mem_source (e : trivialization R F E)
  {x : total_space E} : x ∈ e.source ↔ proj E x ∈ e.base_set := bundle_trivialization.mem_source e

@[simp, mfld_simps] lemma trivialization.coe_coe (e : trivialization R F E) :
  ⇑e.to_local_homeomorph = e := rfl

@[simp, mfld_simps] lemma trivialization.coe_fst
  (e : trivialization R F E) {x : total_space E} (ex : x ∈ e.source) :
  (e x).1 = (proj E) x :=
e.proj_to_fun x ex

end topological_vector_bundle

end trivialization

variables [∀ x, topological_space (E x)]

/-- The space `total_space E` (for `E : B → Type*` such that each `E x` is a topological vector
space) has a topological vector space structure with fiber `F` (denoted with
`topological_vector_bundle R F E`) if around every point there is a fiber bundle trivialization
which is linear in the fibers. -/
class topological_vector_bundle : Prop :=
(inducing [] : ∀ (b : B), inducing (λ x : (E b), (id ⟨b, x⟩ : total_space E)))
(locally_trivial [] : ∀ b : B, ∃ e : topological_vector_bundle.trivialization R F E, b ∈ e.base_set)

variable [topological_vector_bundle R F E]

namespace topological_vector_bundle

/-- `trivialization_at R F E b` is some choice of trivialization of a vector bundle whose base set
contains a given point `b`. -/
def trivialization_at : Π b : B, trivialization R F E :=
λ b, classical.some (topological_vector_bundle.locally_trivial R F E b)

@[simp, mfld_simps] lemma mem_base_set_trivialization_at (b : B) :
  b ∈ (trivialization_at R F E b).base_set :=
classical.some_spec (topological_vector_bundle.locally_trivial R F E b)

@[simp, mfld_simps] lemma mem_source_trivialization_at (z : total_space E) :
  z ∈ (trivialization_at R F E z.1).source :=
by { rw bundle_trivialization.mem_source, apply mem_base_set_trivialization_at }

variables {R F E}

/-- In a topological vector bundle, a trivialization in the fiber (which is a priori only linear)
is in fact a continuous linear equiv between the fibers and the model fiber. -/
def trivialization.continuous_linear_equiv_at (e : trivialization R F E) (b : B)
  (hb : b ∈ e.base_set) : E b ≃L[R] F :=
{ to_fun := λ y, (e ⟨b, y⟩).2,
  inv_fun := λ z, begin
    have : ((e.to_local_homeomorph.symm) (b, z)).fst = b :=
      bundle_trivialization.proj_symm_apply' _ hb,
    have C : E ((e.to_local_homeomorph.symm) (b, z)).fst = E b, by rw this,
    exact cast C (e.to_local_homeomorph.symm (b, z)).2
  end,
  left_inv := begin
    assume v,
    rw [← heq_iff_eq],
    apply (cast_heq _ _).trans,
    have A : (b, (e ⟨b, v⟩).snd) = e ⟨b, v⟩,
    { refine prod.ext _ rfl,
      symmetry,
      exact bundle_trivialization.coe_fst' _ hb },
    have B : e.to_local_homeomorph.symm (e ⟨b, v⟩) = ⟨b, v⟩,
    { apply local_homeomorph.left_inv_on,
      rw bundle_trivialization.mem_source,
      exact hb },
    rw [A, B],
  end,
  right_inv := begin
    assume v,
    have B : e (e.to_local_homeomorph.symm (b, v)) = (b, v),
    { apply local_homeomorph.right_inv_on,
      rw bundle_trivialization.mem_target,
      exact hb },
    have C : (e (e.to_local_homeomorph.symm (b, v))).2 = v, by rw [B],
    conv_rhs { rw ← C },
    dsimp,
    congr,
    ext,
    { exact (bundle_trivialization.proj_symm_apply' _ hb).symm },
    { exact (cast_heq _ _).trans (by refl) },
  end,
  map_add' := λ v w, (e.linear _ hb).map_add v w,
  map_smul' := λ c v, (e.linear _ hb).map_smul c v,
  continuous_to_fun := begin
    refine continuous_snd.comp _,
    apply continuous_on.comp_continuous e.to_local_homeomorph.continuous_on
      (topological_vector_bundle.inducing R F E b).continuous (λ x, _),
    rw bundle_trivialization.mem_source,
    exact hb,
  end,
  continuous_inv_fun := begin
    rw (topological_vector_bundle.inducing R F E b).continuous_iff,
    dsimp,
    have : continuous (λ (z : F), (e.to_bundle_trivialization.to_local_homeomorph.symm) (b, z)),
    { apply e.to_local_homeomorph.symm.continuous_on.comp_continuous
        (continuous_const.prod_mk continuous_id') (λ z, _),
      simp only [bundle_trivialization.mem_target, hb, local_equiv.symm_source,
        local_homeomorph.symm_to_local_equiv] },
    convert this,
    ext z,
    { exact (bundle_trivialization.proj_symm_apply' _ hb).symm },
    { exact cast_heq _ _ },
  end }

@[simp] lemma trivialization.continuous_linear_equiv_at_apply (e : trivialization R F E) (b : B)
  (hb : b ∈ e.base_set) (y : E b) : e.continuous_linear_equiv_at b hb y = (e ⟨b, y⟩).2 := rfl

@[simp] lemma trivialization.continuous_linear_equiv_at_apply' (e : trivialization R F E)
  (x : total_space E) (hx : x ∈ e.source) :
  e.continuous_linear_equiv_at (proj E x) (e.mem_source.1 hx) x.2 = (e x).2 :=
by { cases x, refl }

@[simp] lemma cont_lin_equiv_at_snd_eq_triv_snd {g : right_inv (proj E)} {b : B}
  {e : trivialization R F E} (hb : b ∈ e.base_set) :
  (e.continuous_linear_equiv_at (g b).fst (g.mem_base_set_right_inv_fst hb)) (g b).snd =
  (e (g b)).snd :=
by simp only [trivialization.continuous_linear_equiv_at_apply, sigma.eta]

lemma trivialization.snd_map_add {g h : right_inv (proj E)} {e : trivialization R F E} (b : B)
  (hb : b ∈ e.base_set) :
  (e ((g + h) b)).snd = (e (g b)).snd + (e (h b)).snd :=
begin
  repeat {rw (cont_lin_equiv_at_snd_eq_triv_snd hb).symm},
  have H : ∀ f, (e.continuous_linear_equiv_at ((g + h) b).fst
    ((g + h).mem_base_set_right_inv_fst hb)) ((right_inv.to_pi R f) ((g + h) b).fst) =
    (e.continuous_linear_equiv_at (f b).fst (f.mem_base_set_right_inv_fst hb)) (f b).snd := λ f,
  begin
    simp only [trivialization.continuous_linear_equiv_at_apply],
    have : (((g + h) b).fst : B) = (f b).fst := by { simp only [right_inv.fst_eq_id], },
    rw [this, (right_inv.snd_eq_to_pi_fst R).symm], end,
  rw [(right_inv.snd_eq_to_pi_fst R).symm, linear_equiv.map_add, pi.add_apply,
   continuous_linear_equiv.map_add, H g, H h],
end

lemma trivialization.snd_map_zero {e : trivialization R F E} (b : B) (hb : b ∈ e.base_set) :
  (e ((0 : right_inv (proj E)) b)).snd = 0 :=
by { rw [(cont_lin_equiv_at_snd_eq_triv_snd hb).symm, (right_inv.snd_eq_to_pi_fst R).symm,
  linear_equiv.map_zero, pi.zero_apply, continuous_linear_equiv.map_zero], assumption }
--                                         What the heck it's going on here!?  ↑

lemma trivialization.snd_map_smul {g : right_inv (proj E)} {e : trivialization R F E} {r : R}
  (b : B) (hb : b ∈ e.base_set) :
  (e ((r • (g : right_inv (proj E))) b)).snd = r • (e ((g : right_inv (proj E)) b)).snd :=
begin
  rw [(cont_lin_equiv_at_snd_eq_triv_snd hb).symm, (right_inv.snd_eq_to_pi_fst R).symm,
    linear_equiv.map_smul, pi.smul_apply, continuous_linear_equiv.map_smul],
  simp only [trivialization.continuous_linear_equiv_at_apply],
  congr,
  have h : ((r • g) b).fst = (g b).fst := by simp only [right_inv.fst_eq_id],
  rw [h, ((right_inv.snd_eq_to_pi_fst R).symm).symm],
  exact sigma.eq rfl rfl,
end

variables (R B F)

/-- Local trivialization for trivial bundle. -/
def trivial_bundle_trivialization : trivialization R F (bundle.trivial B F) :=
{ to_fun := λ x, (x.fst, x.snd),
  inv_fun := λ y, ⟨y.fst, y.snd⟩,
  source := univ,
  target := univ,
  map_source' := λ x h, mem_univ (x.fst, x.snd),
  map_target' :=λ y h,  mem_univ ⟨y.fst, y.snd⟩,
  left_inv' := λ x h, sigma.eq rfl rfl,
  right_inv' := λ x h, prod.ext rfl rfl,
  open_source := is_open_univ,
  open_target := is_open_univ,
  continuous_to_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [prod.topological_space, induced_inf, induced_compose], exact le_refl _, },
  continuous_inv_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [bundle.total_space.topological_space, induced_inf, induced_compose],
    exact le_refl _, },
  base_set := univ,
  open_base_set := is_open_univ,
  source_eq := rfl,
  target_eq := by simp only [univ_prod_univ],
  proj_to_fun := λ y hy, rfl,
  linear := λ x hx, ⟨λ y z, rfl, λ c y, rfl⟩ }

instance trivial_bundle.topological_vector_bundle :
  topological_vector_bundle R F (bundle.trivial B F) :=
{ locally_trivial := λ x, ⟨trivial_bundle_trivialization R B F, mem_univ x⟩,
  inducing := λ b, ⟨begin
    have : (λ (x : trivial B F b), x) = @id F, by { ext x, refl },
    simp only [total_space.topological_space, induced_inf, induced_compose, function.comp, proj,
      induced_const, top_inf_eq, trivial.proj_snd, id.def, trivial.topological_space, this,
      induced_id],
  end⟩ }

variables {R B F}

/- Not registered as an instance because of a metavariable. -/
lemma is_topological_vector_bundle_is_topological_fiber_bundle :
  is_topological_fiber_bundle F (proj E) :=
λ x, ⟨(trivialization_at R F E x).to_bundle_trivialization, mem_base_set_trivialization_at R F E x⟩

end topological_vector_bundle

section sections

/-! ### Sections of topological vector bundles -/

/-- Type synonim to allow to declare instances that depend on implicit parameters containing `R`
and `F`. -/
@[reducible, nolint unused_arguments]
def topological_vector_bundle.bundle_section (R : Type*) {B : Type*} (F : Type*)
  (E : B → Type*) [topological_space F] [topological_space (total_space E)] [topological_space B] :=
continuous_section (proj E)

open topological_vector_bundle

variables {R B E F}

lemma right_inv.image_mem_trivialization_at_source (f : right_inv (proj E)) (b : B) :
  f b ∈ (trivialization_at R F E b).source :=
f.mem_base_set_image_mem_source (mem_base_set_trivialization_at R F E b)

variables (R F E)

lemma right_inv.continuous_at_iff_continuous_within_at_triv_at (f : right_inv (proj E)) (b : B) :
  continuous_at f b ↔ continuous_within_at (λ x, ((trivialization_at R F E b) (f x)).snd)
  (trivialization_at R F E b).base_set b :=
f.continuous_at_iff_continuous_within_at (trivialization_at R F E b)
  (mem_base_set_trivialization_at R F E b)

variables {E}

instance [has_continuous_add F] : has_add (bundle_section R F E) :=
⟨λ g h, { continuous_to_fun := by begin
  refine continuous_iff_continuous_at.2 (λ b, _),
  rw [right_inv.to_fun_eq_coe,
    (((g : right_inv (proj E)) + h).continuous_at_iff_continuous_within_at_triv_at R F E b)],
  refine continuous_within_at.congr _ trivialization.snd_map_add
        (trivialization.snd_map_add b (mem_base_set_trivialization_at R F E b)),
  have hg : continuous_at g.to_fun b := g.continuous_to_fun.continuous_at,
  have hh : continuous_at h.to_fun b := h.continuous_to_fun.continuous_at,
  rw [continuous_section.to_fun_eq_coe, ←continuous_section.coe_fn_coe] at hg hh,
  rw right_inv.continuous_at_iff_continuous_within_at_triv_at R F E ↑g b at hg,
  rw right_inv.continuous_at_iff_continuous_within_at_triv_at R F E ↑h b at hh,
  simp only [continuous_section.coe_fn_coe] at *,
  exact continuous_add.continuous_within_at.comp_univ (hg.prod hh),
  end,
..((g : right_inv (proj E)) + h) } ⟩

instance : has_zero (bundle_section R F E) :=
⟨ { continuous_to_fun := begin
  refine continuous_iff_continuous_at.2 (λ b, _),
  rw [right_inv.to_fun_eq_coe,
    ((0 : right_inv (proj E)).continuous_at_iff_continuous_within_at_triv_at R F E b)],
  refine continuous_within_at.congr _ trivialization.snd_map_zero
    (trivialization.snd_map_zero b (mem_base_set_trivialization_at R F E b)),
  exact continuous_within_at_const
end,
  ..(0 : right_inv (proj E))} ⟩

instance : inhabited (bundle_section R F E) := ⟨0⟩

instance [has_continuous_add F] : add_comm_monoid (bundle_section R F E) :=
{ add_assoc := λ f g h, by { apply continuous_section.ext_right_inv, exact add_assoc _ _ _ },
  zero_add := λ f, by { apply continuous_section.ext_right_inv, exact zero_add _ },
  add_zero := λ f, by { apply continuous_section.ext_right_inv, exact add_zero _ },
  add_comm := λ f g, by { apply continuous_section.ext_right_inv, exact add_comm _ _ },
  add := (+),
  zero := 0, }

variables [topological_space R] [has_continuous_smul R F]

instance : has_scalar R (bundle_section R F E) :=
⟨λ r g, { continuous_to_fun := by begin
  refine continuous_iff_continuous_at.2 (λ b, _),
  rw [right_inv.to_fun_eq_coe,
    ((r • (g : right_inv (proj E))).continuous_at_iff_continuous_within_at_triv_at R F E b)],
  refine continuous_within_at.congr _ trivialization.snd_map_smul
    (trivialization.snd_map_smul b (mem_base_set_trivialization_at R F E b)),
  have hg : continuous_at g.to_fun b := g.continuous_to_fun.continuous_at,
  rw [continuous_section.to_fun_eq_coe, ←continuous_section.coe_fn_coe] at hg,
  rw right_inv.continuous_at_iff_continuous_within_at_triv_at R F E ↑g b at hg,
  simp only [continuous_section.coe_fn_coe] at *,
  exact continuous_within_at.const_smul hg r,
  end,
..(r • (g : right_inv (proj E))) } ⟩

instance [has_continuous_add F] : module R (bundle_section R F E) :=
{ zero_smul := λ f, by { apply continuous_section.ext_right_inv, exact zero_smul R _ },
  smul_zero := λ r, by { apply continuous_section.ext_right_inv, exact smul_zero r },
  add_smul := λ r s f, by { apply continuous_section.ext_right_inv,
                exact add_smul r s (f : right_inv (proj E)) },
  smul_add := λ r f g, by { apply continuous_section.ext_right_inv, exact smul_add r _ _ },
  add_smul := λ r s g, by { apply continuous_section.ext_right_inv, exact add_smul r s _ },
  mul_smul := λ r s g, by { apply continuous_section.ext_right_inv, exact mul_smul r s _ },
  one_smul := λ f, by { apply continuous_section.ext_right_inv, exact one_smul R _ },
  ..topological_vector_bundle.bundle_section.has_scalar R F }

end sections

end monoid

section group

open topological_vector_bundle

variables {E R F} [ring R] [∀ x, add_comm_group (E x)] [∀ x, module R (E x)]
  [add_comm_group F] [module R F] [∀ x, topological_space (E x)] [topological_vector_bundle R F E]

lemma trivialization.map_neg {g : right_inv (proj E)}
  {e : trivialization R F E} (b : B) (hb : b ∈ e.base_set) :
  (e ((- (g : right_inv (proj E))) b)).snd = - (e ((g : right_inv (proj E)) b)).snd :=
begin
  rw [(cont_lin_equiv_at_snd_eq_triv_snd hb).symm, (right_inv.snd_eq_to_pi_fst R).symm],
  rw [((right_inv.to_pi R) : (right_inv (proj E)) ≃ₗ[R] (Π x, E x)).map_neg],
  /- What is going on here!?   ↑   ↑   ↑   ↑   ↑    ↑    ↑  -/
  rw [pi.neg_apply, continuous_linear_equiv.map_neg],
  simp only [trivialization.continuous_linear_equiv_at_apply],
  congr,
  have h : ((-g) b).fst = (g b).fst := by simp only [right_inv.fst_eq_id],
  rw [h, ((right_inv.snd_eq_to_pi_fst R).symm).symm],
  exact sigma.eq rfl rfl,
end

variables (R F) [topological_add_group F]

instance : has_neg (bundle_section R F E) :=
⟨λ g, { continuous_to_fun := by begin
  refine continuous_iff_continuous_at.2 (λ b, _),
  rw [right_inv.to_fun_eq_coe,
    ((-(g : right_inv (proj E))).continuous_at_iff_continuous_within_at_triv_at R F E b)],
    refine continuous_within_at.congr _ trivialization.map_neg
    (trivialization.map_neg b (mem_base_set_trivialization_at R F E b)),
  have hg : continuous_at g.to_fun b := g.continuous_to_fun.continuous_at,
  rw [continuous_section.to_fun_eq_coe, ←continuous_section.coe_fn_coe] at hg,
  rw right_inv.continuous_at_iff_continuous_within_at_triv_at R F E ↑g b at hg,
  simp only [continuous_section.coe_fn_coe] at *,
  exact continuous_within_at.neg hg,
  end,
..(-(g : right_inv (proj E))) } ⟩

instance : add_comm_group (bundle_section R F E) :=
{ add_left_neg :=  λ f, by { apply continuous_section.ext_right_inv,
                            exact add_left_neg (f : right_inv (proj E)) },
  ..topological_vector_bundle.bundle_section.has_neg R F,
  ..bundle_section.add_comm_monoid R F, }

end group
