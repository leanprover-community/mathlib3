/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import topology.algebra.uniform_ring
import topology.algebra.field

/-!
# Completion of topological fields

The goal of this file is to prove the main part of Proposition 7 of Bourbaki GT III 6.8 :

The completion `hat K` of a Hausdorff topological field is a field if the image under
the mapping `x ↦ x⁻¹` of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at `0` is a Cauchy filter
(with respect to the additive uniform structure).

Bourbaki does not give any detail here, he refers to the general discussion of extending
functions defined on a dense subset with values in a complete Hausdorff space. In particular
the subtlety about clustering at zero is totally left to readers.

Note that the separated completion of a non-separated topological field is the zero ring, hence
the separation assumption is needed. Indeed the kernel of the completion map is the closure of
zero which is an ideal. Hence it's either zero (and the field is separated) or the full field,
which implies one is sent to zero and the completion ring is trivial.

The main definition is `completable_top_field` which packages the assumptions as a Prop-valued
type class and the main results are the instances `field_completion` and
`topological_division_ring_completion`.
-/


noncomputable theory

open_locale classical uniformity topological_space

open set uniform_space uniform_space.completion filter

variables (K : Type*) [field K]  [uniform_space K]

local notation `hat` := completion

@[priority 100]
instance [separated_space K] : nontrivial (hat K) :=
⟨⟨0, 1, λ h, zero_ne_one $ (uniform_embedding_coe K).inj h⟩⟩

/--
A topological field is completable if it is separated and the image under
the mapping x ↦ x⁻¹ of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at 0 is a Cauchy filter
(with respect to the additive uniform structure). This ensures the completion is
a field.
-/
class completable_top_field extends separated_space K : Prop :=
(nice : ∀ F : filter K, cauchy F → 𝓝 0 ⊓ F = ⊥ → cauchy (map (λ x, x⁻¹) F))

variables {K}

/-- extension of inversion to the completion of a field. -/
def hat_inv : hat K → hat K := dense_inducing_coe.extend (λ x : K, (coe x⁻¹ : hat K))

lemma continuous_hat_inv [completable_top_field K] {x : hat K} (h : x ≠ 0) :
  continuous_at hat_inv x :=
begin
  haveI : regular_space (hat K) := completion.regular_space K,
  refine dense_inducing_coe.continuous_at_extend _,
  apply mem_of_superset (compl_singleton_mem_nhds h),
  intros y y_ne,
  rw mem_compl_singleton_iff at y_ne,
  apply complete_space.complete,
  rw ← filter.map_map,
  apply cauchy.map _ (completion.uniform_continuous_coe K),
  apply completable_top_field.nice,
  { haveI := dense_inducing_coe.comap_nhds_ne_bot y,
    apply cauchy_nhds.comap,
    { rw completion.comap_coe_eq_uniformity,
      exact le_rfl } },
  { have eq_bot : 𝓝 (0 : hat K) ⊓ 𝓝 y = ⊥,
    { by_contradiction h,
      exact y_ne (eq_of_nhds_ne_bot $ ne_bot_iff.mpr h).symm },
    erw [dense_inducing_coe.nhds_eq_comap (0 : K), ← comap_inf,  eq_bot],
    exact comap_bot },
end

/-
The value of `hat_inv` at zero is not really specified, although it's probably zero.
Here we explicitly enforce the `inv_zero` axiom.
-/
instance completion.has_inv : has_inv (hat K) := ⟨λ x, if x = 0 then 0 else hat_inv x⟩

variables [topological_division_ring K]

lemma hat_inv_extends {x : K} (h : x ≠ 0) : hat_inv (x : hat K) = coe (x⁻¹ : K) :=
dense_inducing_coe.extend_eq_at
    ((continuous_coe K).continuous_at.comp (topological_division_ring.continuous_inv x h))

variables [completable_top_field K]

@[norm_cast]
lemma coe_inv (x : K) : (x : hat K)⁻¹ = ((x⁻¹ : K) : hat K) :=
begin
  by_cases h : x = 0,
  { rw [h, inv_zero],
    dsimp [has_inv.inv],
    norm_cast,
    simp [if_pos] },
  { conv_lhs { dsimp [has_inv.inv] },
    norm_cast,
    rw if_neg,
    { exact hat_inv_extends h },
    { exact λ H, h (dense_embedding_coe.inj H) } }
end

variables [uniform_add_group K] [topological_ring K]

lemma mul_hat_inv_cancel {x : hat K} (x_ne : x ≠ 0) : x*hat_inv x = 1 :=
begin
  haveI : t1_space (hat K) := t2_space.t1_space,
  let f := λ x : hat K, x*hat_inv x,
  let c := (coe : K → hat K),
  change f x = 1,
  have cont : continuous_at f x,
  { letI : topological_space (hat K × hat K) := prod.topological_space,
    have : continuous_at (λ y : hat K, ((y, hat_inv y) : hat K × hat K)) x,
      from continuous_id.continuous_at.prod (continuous_hat_inv x_ne),
    exact (_root_.continuous_mul.continuous_at.comp this : _) },
  have clo : x ∈ closure (c '' {0}ᶜ),
  { have := dense_inducing_coe.dense x,
    rw [← image_univ, show (univ : set K) = {0} ∪ {0}ᶜ,
                      from (union_compl_self _).symm, image_union] at this,
    apply mem_closure_of_mem_closure_union this,
    rw image_singleton,
    exact compl_singleton_mem_nhds x_ne },
  have fxclo : f x ∈ closure (f '' (c '' {0}ᶜ)) := mem_closure_image cont clo,
  have : f '' (c '' {0}ᶜ) ⊆ {1},
  { rw image_image,
    rintros _ ⟨z, z_ne, rfl⟩,
    rw mem_singleton_iff,
    rw mem_compl_singleton_iff at z_ne,
    dsimp [c, f],
    rw hat_inv_extends z_ne,
    norm_cast,
    rw mul_inv_cancel z_ne,
    norm_cast },
  replace fxclo := closure_mono this fxclo,
  rwa [closure_singleton, mem_singleton_iff] at fxclo
end

instance field_completion : field (hat K) :=
{ exists_pair_ne := ⟨0, 1, λ h, zero_ne_one ((uniform_embedding_coe K).inj h)⟩,
  mul_inv_cancel := λ x x_ne, by { dsimp [has_inv.inv],
                                   simp [if_neg x_ne, mul_hat_inv_cancel x_ne], },
  inv_zero := show ((0 : K) : hat K)⁻¹ = ((0 : K) : hat K), by rw [coe_inv, inv_zero],
  ..completion.has_inv,
  ..(by apply_instance : comm_ring (hat K)) }

instance topological_division_ring_completion : topological_division_ring (hat K) :=
{ continuous_inv := begin
    intros x x_ne,
    have : {y | hat_inv y = y⁻¹ } ∈ 𝓝 x,
    { have : {(0 : hat K)}ᶜ ⊆ {y : hat K | hat_inv y = y⁻¹ },
      { intros y y_ne,
        rw mem_compl_singleton_iff at y_ne,
        dsimp [has_inv.inv],
        rw if_neg y_ne },
      exact mem_of_superset (compl_singleton_mem_nhds x_ne) this },
    exact continuous_at.congr (continuous_hat_inv x_ne) this
  end,
  ..completion.top_ring_compl }
