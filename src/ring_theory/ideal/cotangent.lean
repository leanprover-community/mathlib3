/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import ring_theory.ideal.operations
import algebra.module.torsion
import algebra.ring.idempotents
import linear_algebra.finite_dimensional
import ring_theory.ideal.local_ring
import ring_theory.nakayama

/-!
# The module `I ⧸ I ^ 2`

In this file, we provide special API support for the module `I ⧸ I ^ 2`. The official
definition is a quotient module of `I`, but the alternative definition as an ideal of `R ⧸ I ^ 2` is
also given, and the two are `R`-equivalent as in `ideal.cotangent_equiv_ideal`.

Additional support is also given to the cotangent space `m ⧸ m ^ 2` of a local ring.

-/

namespace ideal

variables {R S : Type*} [comm_ring R] [comm_semiring S] [algebra S R] (I : ideal R)

/-- `I ⧸ I ^ 2` as a quotient of `I`. -/
@[derive [add_comm_group, module (R ⧸ I)]]
def cotangent : Type* := I ⧸ (I • ⊤ : submodule R I)

instance : inhabited I.cotangent := ⟨0⟩

instance cotangent.module_of_tower : module S I.cotangent :=
submodule.quotient.module' _

instance : is_scalar_tower S R I.cotangent := by { delta cotangent, apply_instance }

instance [is_noetherian R I] : is_noetherian R I.cotangent := by { delta cotangent, apply_instance }

/-- The quotient map from `I` to `I ⧸ I ^ 2`. -/
@[simps apply (lemmas_only)]
def to_cotangent : I →ₗ[R] I.cotangent := submodule.mkq _

lemma map_to_cotangent_ker : I.to_cotangent.ker.map I.subtype = I ^ 2 :=
by simp [ideal.to_cotangent, submodule.map_smul'', pow_two]

lemma mem_to_cotangent_ker {x : I} : x ∈ I.to_cotangent.ker ↔ (x : R) ∈ I ^ 2 :=
begin
  rw ← I.map_to_cotangent_ker,
  simp,
end

lemma to_cotangent_eq {x y : I} : I.to_cotangent x = I.to_cotangent y ↔ (x - y : R) ∈ I ^ 2 :=
begin
  rw [← sub_eq_zero, ← map_sub],
  exact I.mem_to_cotangent_ker
end

lemma to_cotangent_eq_zero (x : I) : I.to_cotangent x = 0 ↔ (x : R) ∈ I ^ 2 :=
I.mem_to_cotangent_ker

lemma to_cotangent_surjective : function.surjective I.to_cotangent :=
submodule.mkq_surjective _

lemma to_cotangent_range : I.to_cotangent.range = ⊤ :=
submodule.range_mkq _

lemma cotangent_subsingleton_iff :
  subsingleton I.cotangent ↔ is_idempotent_elem I :=
begin
  split,
  { introI H,
    refine (pow_two I).symm.trans (le_antisymm (ideal.pow_le_self two_ne_zero) _),
    exact λ x hx, (I.to_cotangent_eq_zero ⟨x, hx⟩).mp (subsingleton.elim _ _) },
  { exact λ e, ⟨λ x y, quotient.induction_on₂' x y $ λ x y,
      I.to_cotangent_eq.mpr $ ((pow_two I).trans e).symm ▸ I.sub_mem x.prop y.prop⟩ }
end

/-- The inclusion map `I ⧸ I ^ 2` to `R ⧸ I ^ 2`. -/
def cotangent_to_quotient_square : I.cotangent →ₗ[R] R ⧸ I ^ 2 :=
submodule.mapq (I • ⊤) (I ^ 2) I.subtype
  (by { rw [← submodule.map_le_iff_le_comap, submodule.map_smul'', submodule.map_top,
    submodule.range_subtype, smul_eq_mul, pow_two], exact rfl.le })

lemma to_quotient_square_comp_to_cotangent : I.cotangent_to_quotient_square.comp I.to_cotangent =
  (I ^ 2).mkq.comp (submodule.subtype I) :=
linear_map.ext $ λ _, rfl

@[simp]
lemma to_cotangent_to_quotient_square (x : I) : I.cotangent_to_quotient_square (I.to_cotangent x) =
  (I ^ 2).mkq x := rfl

/-- `I ⧸ I ^ 2` as an ideal of `R ⧸ I ^ 2`. -/
def cotangent_ideal (I : ideal R) : ideal (R ⧸ I ^ 2) :=
begin
  haveI : @ring_hom_surjective R (R ⧸ I ^ 2) _ _ _ := ⟨ideal.quotient.mk_surjective⟩,
  exact submodule.map (ring_hom.to_semilinear_map (I ^ 2)^.quotient.mk) I,
end

lemma to_quotient_square_range :
  I.cotangent_to_quotient_square.range = I.cotangent_ideal.restrict_scalars R :=
begin
  transitivity (I.cotangent_to_quotient_square.comp I.to_cotangent).range,
  { rw [linear_map.range_comp, I.to_cotangent_range, submodule.map_top] },
  { rw [to_quotient_square_comp_to_cotangent, linear_map.range_comp, I.range_subtype], ext, refl }
end

/-- The equivalence of the two definitions of `I / I ^ 2`, either as the quotient of `I` or the
ideal of `R / I ^ 2`. -/
noncomputable
def cotangent_equiv_ideal : I.cotangent ≃ₗ[R] I.cotangent_ideal :=
begin
  refine
  { ..(I.cotangent_to_quotient_square.cod_restrict (I.cotangent_ideal.restrict_scalars R)
    (λ x, by { rw ← to_quotient_square_range, exact linear_map.mem_range_self _ _ })),
    ..(equiv.of_bijective _ ⟨_, _⟩) },
  { rintros x y e,
    replace e := congr_arg subtype.val e,
    obtain ⟨x, rfl⟩ := I.to_cotangent_surjective x,
    obtain ⟨y, rfl⟩ := I.to_cotangent_surjective y,
    rw I.to_cotangent_eq,
    dsimp only [to_cotangent_to_quotient_square, submodule.mkq_apply] at e,
    rwa submodule.quotient.eq at e },
  { rintro ⟨_, x, hx, rfl⟩,
    refine ⟨I.to_cotangent ⟨x, hx⟩, subtype.ext rfl⟩ }
end

@[simp, nolint simp_nf]
lemma cotangent_equiv_ideal_apply (x : I.cotangent) :
  ↑(I.cotangent_equiv_ideal x) = I.cotangent_to_quotient_square x := rfl

lemma cotangent_equiv_ideal_symm_apply (x : R) (hx : x ∈ I) :
  I.cotangent_equiv_ideal.symm ⟨(I ^ 2).mkq x, submodule.mem_map_of_mem hx⟩ =
    I.to_cotangent ⟨x, hx⟩ :=
begin
  apply I.cotangent_equiv_ideal.injective,
  rw I.cotangent_equiv_ideal.apply_symm_apply,
  ext,
  refl
end

/--
If `N` is a f.g. `R`-submodule of `M`, and `I` is an ideal of `R` contained in its jacobson radical,
then `N/IN` is principal as an `R/I`-module implies that `N` is a principal `
-/
lemma submodule.is_principal_of_quotient_smul_is_principal (I : ideal R)
  (hI : I ≤ (⊥ : ideal R).jacobson) (N : submodule R M) (hN : N.fg)
    [h : (⊤ : submodule (R ⧸ I) (N ⧸ I • (⊤ : submodule R N))).is_principal] :
    N.is_principal :=
begin
  unfreezingI { obtain ⟨x, hx'⟩ := h },
  obtain ⟨x, rfl⟩ := submodule.mkq_surjective _ x,
  rw [← set.image_singleton, ← submodule.restrict_scalars_inj R,
    submodule.restrict_scalars_top, ← submodule.span_eq_restrict_scalars,
    ← submodule.map_span, eq_comm, submodule.map_mkq_eq_top,
    ← (submodule.map_injective_of_injective N.injective_subtype).eq_iff,
    submodule.map_sup, submodule.map_smul'', submodule.map_top, submodule.range_subtype,
    submodule.map_span, set.image_singleton, N.subtype_apply] at hx',
  have : submodule.span R {↑x} ⊔ N = submodule.span R {↑x} ⊔ I • N,
  { rw [@sup_comm _ _ _ (I • N), hx', sup_eq_right], exact le_sup_right.trans hx'.le },
  have := submodule.smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson hN hI this.le,
  rw [submodule.bot_smul, sup_bot_eq, sup_eq_left] at this,
  rw sup_eq_right.mpr this at hx',
  exacts [⟨⟨x, hx'.symm⟩⟩, ideal.quotient.mk_surjective],
end


end ideal

attribute [mk_iff] submodule.is_principal

lemma submodule.rank_le_one_iff_is_principal {R M : Type*} [division_ring R] [add_comm_group M] [module R M]
  (N : submodule R M) :
  module.rank R N ≤ 1 ↔ N.is_principal :=
begin
  rw dim_le_one_iff,
  split,
  { rintro ⟨m, hm⟩,
    refine ⟨⟨m, le_antisymm _ ((submodule.span_singleton_le_iff_mem _ _).mpr m.prop)⟩⟩,
    intros x hx,
    obtain ⟨r, hr⟩ := hm ⟨x, hx⟩,
    exact submodule.mem_span_singleton.mpr ⟨r, congr_arg subtype.val hr⟩ },
  { rintro ⟨⟨a, rfl⟩⟩,
    refine ⟨⟨a, submodule.mem_span_singleton_self a⟩, _⟩,
    rintro ⟨m, hm⟩,
    obtain ⟨r, hr⟩ := submodule.mem_span_singleton.mp hm,
    exact ⟨r, subtype.ext hr⟩ }
end

lemma module.rank_le_one_iff_top_is_principal {R M : Type*} [division_ring R] [add_comm_group M]
  [module R M] :
  module.rank R M ≤ 1 ↔ (⊤ : submodule R M).is_principal :=
by rw [← submodule.rank_le_one_iff_is_principal, dim_top]

lemma submodule.finrank_le_one_iff_is_principal {R M : Type*}
  [division_ring R] [add_comm_group M] [module R M] (N : submodule R M) [finite_dimensional R N] :
  finite_dimensional.finrank R N ≤ 1 ↔ N.is_principal :=
by rw [← N.rank_le_one_iff_is_principal, ← finite_dimensional.finrank_eq_dim,
  ← cardinal.nat_cast_le, nat.cast_one]

lemma module.finrank_le_one_iff_top_is_principal {R M : Type*} [division_ring R] [add_comm_group M]
  [module R M] [finite_dimensional R M] :
  finite_dimensional.finrank R M ≤ 1 ↔ (⊤ : submodule R M).is_principal :=
by rw [← module.rank_le_one_iff_top_is_principal, ← finite_dimensional.finrank_eq_dim,
  ← cardinal.nat_cast_le, nat.cast_one]

namespace local_ring

variables (R : Type*) [comm_ring R] [local_ring R]

/-- The `A ⧸ I`-vector space `I ⧸ I ^ 2`. -/
@[reducible] def cotangent_space : Type* := (maximal_ideal R).cotangent

instance : module (residue_field R) (cotangent_space R) :=
ideal.cotangent.module _

instance : is_scalar_tower R (residue_field R) (cotangent_space R) :=
module.is_torsion_by_set.is_scalar_tower _

instance [is_noetherian_ring R] : finite_dimensional (residue_field R) (cotangent_space R) :=
module.finite.of_restrict_scalars_finite R _ _

lemma _root_.ring.is_field_iff_eq_bot_of_is_maximal (R : Type*) [comm_ring R] [nontrivial R] {M : ideal R} [h : M.is_maximal] :
  is_field R ↔ M = ⊥ :=
begin
  split,
  { intro H, letI := H.to_field, exact M.eq_bot_of_prime },
  { intro e, by_contra h', exact ring.ne_bot_of_is_maximal_of_not_is_field h h' e },
end

lemma dim_cotangent_space_eq_zero_iff [is_domain R] [is_noetherian_ring R] :
  finite_dimensional.finrank (residue_field R) (cotangent_space R) = 0 ↔ is_field R :=
by rw [finite_dimensional.finrank_zero_iff, ideal.cotangent_subsingleton_iff,
    ideal.eq_square_iff_eq_bot_or_top _ (is_noetherian.noetherian _),
    or_iff_left (maximal_ideal.is_maximal R).ne_top, ← ring.is_field_iff_eq_bot_of_is_maximal];
  apply_instance
lemma _root_.submodule.map_smul_top {M : Type*} [add_comm_monoid M] [module R M]
  (I : ideal R) (N : submodule R M) (x : N) : submodule.map N.subtype (I • ⊤) = I • N :=
by rw [submodule.map_smul'', submodule.map_top, submodule.range_subtype]

lemma _root_.submodule.mem_smul_top_iff {M : Type*} [add_comm_monoid M] [module R M]
  (I : ideal R) (N : submodule R M) (x : N) : x ∈ I • (⊤ : submodule R N) ↔ (x : M) ∈ I • N :=
begin
  change _ ↔ N.subtype x ∈ I • N,
  have : submodule.map N.subtype (I • ⊤) = I • N,
  { rw [submodule.map_smul'', submodule.map_top, submodule.range_subtype] },
  rw ← this,
  convert (function.injective.mem_set_image N.injective_subtype).symm using 1,
  refl,
end
lemma local_ring.jacobson_eq_maximal_ideal (I : ideal R) (h : I ≠ ⊤) :
  I.jacobson = local_ring.maximal_ideal R :=
begin
  apply le_antisymm,
  { exact Inf_le ⟨local_ring.le_maximal_ideal h, local_ring.maximal_ideal.is_maximal R⟩ },
  { exact le_Inf (λ J (hJ : I ≤ J ∧ J.is_maximal),
      le_of_eq (local_ring.eq_maximal_ideal hJ.2).symm) }
end
lemma foobar {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
  (I : ideal R) (hI : I ≤ (⊥ : ideal R).jacobson) (N : submodule R M) (hN : N.fg)
    [h : (⊤ : submodule (R ⧸ I) (N ⧸ I • (⊤ : submodule R N))).is_principal] :
    N.is_principal :=
begin
  unfreezingI { obtain ⟨x, hx'⟩ := h },
  obtain ⟨x, rfl⟩ := submodule.mkq_surjective _ x,
  rw [← set.image_singleton, ← submodule.restrict_scalars_inj R,
    submodule.restrict_scalars_top, ← submodule.span_eq_restrict_scalars,
    ← submodule.map_span, eq_comm, submodule.map_mkq_eq_top,
    ← (submodule.map_injective_of_injective N.injective_subtype).eq_iff,
    submodule.map_sup, submodule.map_smul'', submodule.map_top, submodule.range_subtype,
    submodule.map_span, set.image_singleton, N.subtype_apply] at hx',
  have : submodule.span R {↑x} ⊔ N = submodule.span R {↑x} ⊔ I • N,
  { rw [@sup_comm _ _ _ (I • N), hx', sup_eq_right], exact le_sup_right.trans hx'.le },
  have := submodule.smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson hN hI this.le,
  rw [submodule.bot_smul, sup_bot_eq, sup_eq_left] at this,
  rw sup_eq_right.mpr this at hx',
  exacts [⟨⟨x, hx'.symm⟩⟩, ideal.quotient.mk_surjective],
end


lemma dim_cotangent_space_eq_one_iff [is_domain R] [is_noetherian_ring R] :
  finite_dimensional.finrank (residue_field R) (cotangent_space R) ≤ 1 ↔
    (maximal_ideal R).is_principal :=
begin
  rw module.finrank_le_one_iff_top_is_principal,
  split,
  { rintro ⟨x, hx'⟩,
    obtain ⟨x, rfl⟩ := submodule.mkq_surjective _ x,
    rw [← set.image_singleton, ← submodule.restrict_scalars_inj R,
      submodule.restrict_scalars_top, ← submodule.span_eq_restrict_scalars,
      ← submodule.map_span, eq_comm, submodule.map_mkq_eq_top] at hx',
    have := submodule.span_eq_restrict_scalars,
    -- ← submodule.span_span_of_tower R,
      -- ← submodule.map_span
  --   -- change _ = submodule.span _ ({submodule.mk} : set (cotangent_space R)),
  --   use x,
  --   apply le_antisymm,
  --   swap, { rw [submodule.span_le, set.singleton_subset_iff], exact x.prop },
  --   have h₁ : (ideal.span {x} : ideal R) ⊔ maximal_ideal R ≤
  --     ideal.span {x} ⊔ (maximal_ideal R) • (maximal_ideal R),
  --   { refine sup_le le_sup_left _,
  --     rintros m hm,
  --     obtain ⟨c, hc⟩ := submodule.mem_span_singleton.mp ((hx'.le : _) (show submodule.quotient.mk
  --     (⟨m, hm⟩ : maximal_ideal R) ∈ ⊤, by triv)),
  --     induction c using quotient.induction_on',
  --     rw ← sub_sub_cancel (c * x) m,
  --     apply sub_mem _ _,
  --     { apply_instance },
  --     { refine ideal.mem_sup_left (ideal.mem_span_singleton'.mpr ⟨c, rfl⟩) },
  --     { have := (submodule.quotient.eq _).mp hc,
  --       rw submodule.mem_smul_top_iff at this,
  --       exact ideal.mem_sup_right this } },
  --   have h₂ : maximal_ideal R ≤ (⊥ : ideal R).jacobson,
  --   { rw local_ring.jacobson_eq_maximal_ideal, exacts [le_refl _, bot_ne_top] },
  --   have := submodule.smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson
  --     (is_noetherian.noetherian _) h₂ h₁,
  --   rw [submodule.bot_smul, sup_bot_eq] at this,
  --   rw [← sup_eq_left, eq_comm],
    -- exact le_sup_left.antisymm (h₁.trans $ le_of_eq this)
     },
  { introI, apply_instance }
end


end local_ring
