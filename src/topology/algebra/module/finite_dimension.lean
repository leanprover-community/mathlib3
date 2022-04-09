/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Anatole Dedecker
-/
import analysis.normed.normed_field
import analysis.locally_convex.balanced_core_hull

/-!
# TODO
-/

universes u v w x

noncomputable theory

open set finite_dimensional topological_space filter
open_locale classical big_operators filter topological_space nnreal uniformity

section move_me

@[to_additive]
instance subgroup.uniform_group {G : Type*} [group G] [uniform_space G] [uniform_group G]
  (S : subgroup G) : uniform_group S :=
{ uniform_continuous_div := uniform_continuous_comap' (uniform_continuous_div.comp $
    uniform_continuous_subtype_val.prod_map uniform_continuous_subtype_val) }

@[to_additive]
lemma subgroup.t1_quotient_of_is_closed {G : Type*} [group G] [topological_space G]
  [topological_group G] (S : subgroup G) [S.normal] (hS : is_closed (S : set G)) :
  t1_space (G ⧸ S) :=
begin
  rw ← quotient_group.ker_mk S at hS,
  exact topological_group.t1_space (G ⧸ S) ((quotient_map_quotient_mk.is_closed_preimage).mp hS)
end

@[to_additive]
lemma subgroup.t2_quotient_of_is_closed {G : Type*} [group G] [topological_space G]
  [topological_group G] (S : subgroup G) [S.normal] (hS : is_closed (S : set G)) :
  t2_space (G ⧸ S) :=
@topological_group.t2_space (G ⧸ S) _ _ _ (S.t1_quotient_of_is_closed hS)

lemma linear_map.ker_subgroup_eq_group_hom_ker {R M M' : Type*} [ring R] [add_comm_group M]
  [add_comm_monoid M'] [module R M] [module R M'] (f : M →ₗ[R] M') :
f.ker.to_add_subgroup = f.to_add_monoid_hom.ker := rfl

def submodule.quotient_equiv_quotient_group {R M : Type*} [ring R] [add_comm_group M] [module R M]
  (S : submodule R M) : M ⧸ S ≃+ M ⧸ S.to_add_subgroup :=
let φ₁ : M ⧸ S.to_add_subgroup ≃+ M ⧸ S.mkq.to_add_monoid_hom.ker :=
      quotient_add_group.equiv_quotient_of_eq
      (by rw [← S.mkq.ker_subgroup_eq_group_hom_ker, S.ker_mkq]),
    φ₂ : M ⧸ S.mkq.to_add_monoid_hom.ker ≃+ M ⧸ S :=
      quotient_add_group.quotient_ker_equiv_of_surjective S.mkq.to_add_monoid_hom
      (submodule.quotient.mk_surjective S)
in (φ₁.trans φ₂).symm

lemma submodule.quotient_equiv_quotient_group_symm_apply {R M : Type*} [ring R] [add_comm_group M]
  [module R M] (S : submodule R M) {x : M} :
  S.quotient_equiv_quotient_group.symm (quotient_add_group.mk x) = (S.mkq x) := rfl

lemma submodule.quotient_equiv_quotient_group_symm_comp_mk {R M : Type*} [ring R] [add_comm_group M]
  [module R M] (S : submodule R M) :
  S.quotient_equiv_quotient_group.symm ∘ quotient_add_group.mk = S.mkq := rfl

lemma submodule.quotient_equiv_quotient_group_apply {R M : Type*} [ring R] [add_comm_group M]
  [module R M] (S : submodule R M) {x : M} :
  S.quotient_equiv_quotient_group (S.mkq x) = (quotient_add_group.mk x) :=
by rw [add_equiv.apply_eq_iff_symm_apply]; refl

lemma submodule.quotient_equiv_quotient_group_comp_mkq {R M : Type*} [ring R] [add_comm_group M]
  [module R M] (S : submodule R M) :
  S.quotient_equiv_quotient_group ∘ S.mkq = quotient_add_group.mk :=
by funext; exact S.quotient_equiv_quotient_group_apply

def submodule.quotient_homeomorph_quotient_group {R M : Type*} [ring R] [add_comm_group M] [module R M]
  (S : submodule R M) [topological_space M] : M ⧸ S ≃ₜ M ⧸ S.to_add_subgroup :=
{ continuous_to_fun :=
  begin
    refine continuous_coinduced_dom _,
    change continuous (S.quotient_equiv_quotient_group ∘ S.mkq),
    rw S.quotient_equiv_quotient_group_comp_mkq,
    exact continuous_quot_mk
  end,
  continuous_inv_fun := continuous_coinduced_dom continuous_quot_mk,
  .. S.quotient_equiv_quotient_group }

lemma submodule.is_open_map_mkq {R M : Type*} [ring R] [add_comm_group M] [module R M]
  (S : submodule R M) [topological_space M] [topological_add_group M] : is_open_map S.mkq :=
begin
  rw ← S.quotient_equiv_quotient_group_symm_comp_mk,
  exact S.quotient_homeomorph_quotient_group.symm.is_open_map.comp
    (quotient_add_group.is_open_map_coe _)
end

instance submodule.topological_add_group_quotient {R M : Type*} [ring R] [add_comm_group M]
  [module R M] [topological_space M] [topological_add_group M] (S : submodule R M) :
    topological_add_group (M ⧸ S) :=
begin
  have : inducing S.quotient_equiv_quotient_group :=
    S.quotient_homeomorph_quotient_group.inducing,
  rw this.1,
  exact topological_add_group_induced _
end

instance submodule.has_continuous_smul_quotient {R M : Type*} [ring R] [add_comm_group M]
  [module R M] [topological_space R] [topological_space M] [topological_add_group M]
  [has_continuous_smul R M] (S : submodule R M) :
  has_continuous_smul R (M ⧸ S) :=
begin
  split,
  have quot : quotient_map (λ au : R × M, (au.1, S.mkq au.2)),
    from is_open_map.to_quotient_map
      (is_open_map.id.prod S.is_open_map_mkq)
      (continuous_id.prod_map continuous_quot_mk)
      (function.surjective_id.prod_map $ surjective_quot_mk _),
  rw quot.continuous_iff,
  exact continuous_quot_mk.comp continuous_smul
end

lemma submodule.t2_quotient_of_is_closed {R M : Type*} [ring R] [add_comm_group M]
  [module R M] [topological_space M] [topological_add_group M] (S : submodule R M)
  (hS : is_closed (S : set M)) :
  t2_space (M ⧸ S) :=
begin
  letI : t2_space (M ⧸ S.to_add_subgroup) := S.to_add_subgroup.t2_quotient_of_is_closed hS,
  exact S.quotient_homeomorph_quotient_group.symm.t2_space
end

lemma induced_symm {α β : Type*} {e : α ≃ β} : induced e.symm = coinduced e :=
begin
  ext t U,
  split,
  { rintros ⟨V, hV, rfl⟩,
    change t.is_open (e ⁻¹' _),
    rwa [← preimage_comp, ← equiv.coe_trans, equiv.self_trans_symm] },
  { intros hU,
    refine ⟨e ⁻¹' U, hU, _⟩,
    rw [← preimage_comp, ← equiv.coe_trans, equiv.symm_trans_self, equiv.coe_refl, preimage_id] }
end

lemma coinduced_symm {α β : Type*} {e : α ≃ β} : coinduced e.symm = induced e :=
by rw [← induced_symm, equiv.symm_symm]

lemma equiv.uniform_embedding {α β : Type*} [uniform_space α] [uniform_space β] (f : α ≃ β)
  (h₁ : uniform_continuous f) (h₂ : uniform_continuous f.symm) : uniform_embedding f :=
{ comap_uniformity :=
  begin
    refine le_antisymm _ _,
    { change comap (f.prod_congr f) _ ≤ _,
      rw ← map_equiv_symm (f.prod_congr f),
      exact h₂ },
    { rw ← map_le_iff_le_comap,
      exact h₁ }
  end,
  inj := f.injective }

--#check
--
--example {α₁ α₂ β₁ β₂ : Type*} {t₁ : topological_space β₁} {t₂ : topological_space β₂}
--  {f₁ : α₁ → β₁} {f₂ : α₂ → β₂} : topological_space.prod
--
--instance submodule.topological_add_group_quotient {𝕜 E : Type*} [ring 𝕜] [add_comm_group E]
--  [module 𝕜 E] [topological_space E] [topological_add_group E] (N : submodule 𝕜 E) :
--    topological_add_group (E ⧸ N) :=
--{ continuous_add := begin
--    have cont : continuous ((N.mkq : E → E ⧸ N) ∘ (λ (p : E × E), p.fst + p.snd)) :=
--      continuous_quot_mk.comp continuous_add,
--    have quot : quotient_map (λ p : E × E, (N.mkq p.1, N.mkq p.2)),
--    { apply is_open_map.to_quotient_map,
--      { exact (quotient_add_group.is_open_map_coe N).prod (quotient_group.is_open_map_coe N) },
--      { exact continuous_quot_mk.prod_map continuous_quot_mk },
--      { exact (surjective_quot_mk _).prod_map (surjective_quot_mk _) } },
--    exact (quotient_map.continuous_iff quot).2 cont,
--  end,
--  continuous_neg := begin
--    have : continuous ((coe : G → G ⧸ N) ∘ (λ (a : G), a⁻¹)) :=
--      continuous_quot_mk.comp continuous_inv,
--    convert continuous_quotient_lift _ this,
--  end }

variables {𝕜 𝕜₂ E F : Type*} [semiring 𝕜] [semiring 𝕜₂]
  [add_comm_group E] [add_comm_group F] [module 𝕜 E] [module 𝕜₂ F]
  [uniform_space E] [uniform_space F] [uniform_add_group E] [uniform_add_group F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜}

lemma continuous_linear_map.uniform_continuous' (f : E →SL[σ₁₂] F) : uniform_continuous f :=
uniform_continuous_add_monoid_hom_of_continuous f.continuous

lemma continuous_linear_equiv.uniform_embedding'
  [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂] (e : E ≃SL[σ₁₂] F) :
  uniform_embedding e :=
e.to_linear_equiv.to_equiv.uniform_embedding
  e.to_continuous_linear_map.uniform_continuous'
  e.symm.to_continuous_linear_map.uniform_continuous'

lemma linear_equiv.uniform_embedding' [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂]
  (e : E ≃ₛₗ[σ₁₂] F) (h₁ : continuous e)
  (h₂ : continuous e.symm) : uniform_embedding e :=
continuous_linear_equiv.uniform_embedding'
({ continuous_to_fun := h₁,
  continuous_inv_fun := h₂,
  .. e } : E ≃SL[σ₁₂] F)

end move_me

/-- A linear map on `ι → 𝕜` (where `ι` is a fintype) is continuous -/
lemma linear_map.continuous_on_pi' {ι : Type w} [fintype ι] {𝕜 : Type u} [field 𝕜]
  [topological_space 𝕜] {E : Type v}  [add_comm_group E] [module 𝕜 E] [topological_space E]
  [topological_add_group E] [has_continuous_smul 𝕜 E] (f : (ι → 𝕜) →ₗ[𝕜] E) : continuous f :=
begin
  -- for the proof, write `f` in the standard basis, and use that each coordinate is a continuous
  -- function.
  have : (f : (ι → 𝕜) → E) =
         (λx, ∑ i : ι, x i • (f (λj, if i = j then 1 else 0))),
    by { ext x, exact f.pi_apply_eq_sum_univ x },
  rw this,
  refine continuous_finset_sum _ (λi hi, _),
  exact (continuous_apply i).smul continuous_const
end

--/-- The space of continuous linear maps between finite-dimensional spaces is finite-dimensional.
---/
--instance {𝕜 E F : Type*} [field 𝕜] [topological_space 𝕜]
--  [topological_space E] [add_comm_group E] [module 𝕜 E] [finite_dimensional 𝕜 E]
--  [topological_space F] [add_comm_group F] [module 𝕜 F] [topological_add_group F]
--  [has_continuous_smul 𝕜 F] [finite_dimensional 𝕜 F] :
--  finite_dimensional 𝕜 (E →L[𝕜] F) :=
--begin
--  haveI : is_noetherian 𝕜 (E →ₗ[𝕜] F) := is_noetherian.iff_fg.mpr (by apply_instance),
--  let I : (E →L[𝕜] F) →ₗ[𝕜] (E →ₗ[𝕜] F) := continuous_linear_map.coe_lm 𝕜,
--  exact module.finite.of_injective I continuous_linear_map.coe_injective
--end

section complete_field

variables {𝕜 : Type u} [nondiscrete_normed_field 𝕜]
{E : Type v} [add_comm_group E] [module 𝕜 E] [topological_space E]
[topological_add_group E] [has_continuous_smul 𝕜 E]
{F : Type w} [add_comm_group F] [module 𝕜 F] [topological_space F]
[topological_add_group F] [has_continuous_smul 𝕜 F]
{F' : Type x} [add_comm_group F'] [module 𝕜 F'] [topological_space F']
[topological_add_group F'] [has_continuous_smul 𝕜 F']
[complete_space 𝕜]

lemma unique_topology_of_t2 [hnorm : nondiscrete_normed_field 𝕜] {t : topological_space 𝕜}
  (h₁ : @topological_add_group 𝕜 t _)
  (h₂ : @has_continuous_smul 𝕜 𝕜 _ hnorm.to_uniform_space.to_topological_space t)
  (h₃ : @t2_space 𝕜 t) :
t = hnorm.to_uniform_space.to_topological_space :=
begin
  refine topological_add_group.ext h₁ infer_instance (le_antisymm _ _),
  { rw metric.nhds_basis_closed_ball.ge_iff,
    intros ε hε,
    rcases normed_field.exists_norm_lt 𝕜 hε with ⟨ξ₀, hξ₀, hξ₀ε⟩,
    have : {ξ₀}ᶜ ∈ @nhds 𝕜 t 0 :=
      is_open.mem_nhds is_open_compl_singleton (ne.symm $ norm_ne_zero_iff.mp hξ₀.ne.symm),
    have : balanced_core 𝕜 {ξ₀}ᶜ ∈ @nhds 𝕜 t 0 := balanced_core_mem_nhds_zero this,
    refine mem_of_superset this (λ ξ hξ, _),
    by_cases hξ0 : ξ = 0,
    { rw hξ0,
      exact metric.mem_closed_ball_self hε.le },
    { rw [mem_closed_ball_zero_iff],
      by_contra' h,
      suffices : (ξ₀ * ξ⁻¹) • ξ ∈ balanced_core 𝕜 {ξ₀}ᶜ,
      { rw [smul_eq_mul 𝕜, mul_assoc, inv_mul_cancel hξ0, mul_one] at this,
        exact not_mem_compl_iff.mpr (mem_singleton ξ₀) ((balanced_core_subset _) this) },
      refine balanced_mem (balanced_core_balanced _) hξ _,
      rw [norm_mul, norm_inv, mul_inv_le_iff (norm_pos_iff.mpr hξ0), mul_one],
      exact (hξ₀ε.trans h).le } },
  { calc (@nhds 𝕜 hnorm.to_uniform_space.to_topological_space 0)
        = map id (@nhds 𝕜 hnorm.to_uniform_space.to_topological_space 0) : map_id.symm
    ... = map (λ x, id x • 1) (@nhds 𝕜 hnorm.to_uniform_space.to_topological_space 0) :
        by conv_rhs {congr, funext, rw [smul_eq_mul, mul_one]}; refl
    ... ≤ (@nhds 𝕜 t ((0 : 𝕜) • 1)) :
        @tendsto.smul_const _ _ _ hnorm.to_uniform_space.to_topological_space t _ _ _ _ _
          tendsto_id (1 : 𝕜)
    ... = (@nhds 𝕜 t 0) : by rw zero_smul }
end

lemma linear_map.continuous_of_is_closed_ker (l : E →ₗ[𝕜] 𝕜) (hl : is_closed (l.ker : set E)) :
  continuous l :=
begin
  by_cases H : finrank 𝕜 l.range = 0,
  { rw [finrank_eq_zero, linear_map.range_eq_bot] at H,
    rw H,
    exact continuous_zero },
  { letI : t2_space (E ⧸ l.ker) := l.ker.t2_quotient_of_is_closed hl,
    have : finrank 𝕜 l.range = 1,
      from le_antisymm (finrank_self 𝕜 ▸ l.range.finrank_le) (zero_lt_iff.mpr H),
    have hi : function.injective (l.ker.liftq l (le_refl _)),
    { rw [← linear_map.ker_eq_bot],
      exact submodule.ker_liftq_eq_bot _ _ _ (le_refl _) },
    have hs : function.surjective (l.ker.liftq l (le_refl _)),
    { rw [← linear_map.range_eq_top, submodule.range_liftq],
      exact eq_top_of_finrank_eq ((finrank_self 𝕜).symm ▸ this) },
    let φ : (E ⧸ l.ker) ≃ₗ[𝕜] 𝕜 := linear_equiv.of_bijective (l.ker.liftq l (le_refl _)) hi hs,
    have hlφ : (l : E → 𝕜) = φ ∘ l.ker.mkq,
      by ext; refl,
    suffices : continuous φ.to_equiv,
    { rw hlφ,
      exact this.comp continuous_quot_mk },
    rw [continuous_iff_coinduced_le, ← induced_symm],
    refine le_of_eq (unique_topology_of_t2 (topological_add_group_induced φ.symm.to_linear_map)
      (has_continuous_smul_induced φ.symm.to_linear_map) _),
    rw t2_space_iff,
    exact λ x y hxy, @separated_by_continuous _ _ (induced _ _) _ _ _
      continuous_induced_dom _ _ (φ.to_equiv.symm.injective.ne hxy) }
end

/-- In finite dimension over a complete field, the canonical identification (in terms of a basis)
with `𝕜^n` together with its sup norm is continuous. This is the nontrivial part in the fact that
all norms are equivalent in finite dimension.

This statement is superceded by the fact that every linear map on a finite-dimensional space is
continuous, in `linear_map.continuous_of_finite_dimensional`. -/
lemma continuous_equiv_fun_basis' [ht2 : t2_space E] {ι : Type v} [fintype ι] (ξ : basis ι 𝕜 E) :
  continuous ξ.equiv_fun :=
begin
  letI : uniform_space E := topological_add_group.to_uniform_space E,
  letI : uniform_add_group E := topological_add_group_is_uniform,
  letI : separated_space E := separated_iff_t2.mpr ht2,
  unfreezingI { induction hn : fintype.card ι with n IH generalizing ι E },
  { rw fintype.card_eq_zero_iff at hn,
    exact continuous_of_const (λ x y, funext hn.elim) },
  { haveI : finite_dimensional 𝕜 E := of_fintype_basis ξ,
    -- first step: thanks to the induction hypothesis, any n-dimensional subspace is equivalent
    -- to a standard space of dimension n, hence it is complete and therefore closed.
    have H₁ : ∀s : submodule 𝕜 E, finrank 𝕜 s = n → is_closed (s : set E),
    { assume s s_dim,
      letI : uniform_add_group s := s.to_add_subgroup.uniform_add_group,
      let b := basis.of_vector_space 𝕜 s,
      have U : uniform_embedding b.equiv_fun.symm.to_equiv,
      { have : fintype.card (basis.of_vector_space_index 𝕜 s) = n,
          by { rw ← s_dim, exact (finrank_eq_card_basis b).symm },
        have : continuous b.equiv_fun := IH b this,
        exact b.equiv_fun.symm.uniform_embedding' b.equiv_fun.symm.to_linear_map.continuous_on_pi
          this },
      have : is_complete (s : set E),
        from complete_space_coe_iff_is_complete.1 ((complete_space_congr U).1 (by apply_instance)),
      exact this.is_closed },
    -- second step: any linear form is continuous, as its kernel is closed by the first step
    have H₂ : ∀f : E →ₗ[𝕜] 𝕜, continuous f,
    { assume f,
      by_cases H : finrank 𝕜 f.range = 0,
      { rw [finrank_eq_zero, linear_map.range_eq_bot] at H,
        rw H,
        exact continuous_zero },
      { have : finrank 𝕜 f.ker = n,
        { have Z := f.finrank_range_add_finrank_ker,
          rw [finrank_eq_card_basis ξ, hn] at Z,
          have : finrank 𝕜 f.range = 1,
            from le_antisymm (finrank_self 𝕜 ▸ f.range.finrank_le) (zero_lt_iff.mpr H),
          rw [this, add_comm, nat.add_one] at Z,
          exact nat.succ.inj Z },
        have : is_closed (f.ker : set E),
          from H₁ _ this,
        exact linear_map.continuous_of_is_closed_ker f this } },
    rw continuous_pi_iff,
    intros i,
    change continuous (ξ.coord i),
    exact H₂ (ξ.coord i) },
end

/-- Any linear map on a finite dimensional space over a complete field is continuous. -/
theorem linear_map.continuous_of_finite_dimensional' [t2_space E] [finite_dimensional 𝕜 E]
  (f : E →ₗ[𝕜] F') :
  continuous f :=
begin
  -- for the proof, go to a model vector space `b → 𝕜` thanks to `continuous_equiv_fun_basis`, and
  -- argue that all linear maps there are continuous.
  let b := basis.of_vector_space 𝕜 E,
  have A : continuous b.equiv_fun :=
    continuous_equiv_fun_basis' b,
  have B : continuous (f.comp (b.equiv_fun.symm : (basis.of_vector_space_index 𝕜 E → 𝕜) →ₗ[𝕜] E)) :=
    linear_map.continuous_on_pi _,
  have : continuous ((f.comp (b.equiv_fun.symm : (basis.of_vector_space_index 𝕜 E → 𝕜) →ₗ[𝕜] E))
                      ∘ b.equiv_fun) := B.comp A,
  convert this,
  ext x,
  dsimp,
  rw [basis.equiv_fun_symm_apply, basis.sum_repr]
end

namespace linear_map

variables [t2_space E] [finite_dimensional 𝕜 E]

/-- The continuous linear map induced by a linear map on a finite dimensional space -/
def to_continuous_linear_map' : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F' :=
{ to_fun := λ f, ⟨f, f.continuous_of_finite_dimensional'⟩,
  inv_fun := coe,
  map_add' := λ f g, rfl,
  map_smul' := λ c f, rfl,
  left_inv := λ f, rfl,
  right_inv := λ f, continuous_linear_map.coe_injective rfl }

@[simp] lemma coe_to_continuous_linear_map''' (f : E →ₗ[𝕜] F') :
  ⇑f.to_continuous_linear_map' = f := rfl

@[simp] lemma coe_to_continuous_linear_map'' (f : E →ₗ[𝕜] F') :
  (f.to_continuous_linear_map' : E →ₗ[𝕜] F') = f := rfl

@[simp] lemma coe_to_continuous_linear_map_symm' :
  ⇑(to_continuous_linear_map' : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F').symm = coe := rfl

end linear_map

namespace linear_equiv

variables [t2_space E] [t2_space F] [finite_dimensional 𝕜 E]

/-- The continuous linear equivalence induced by a linear equivalence on a finite dimensional
space. -/
def to_continuous_linear_equiv' (e : E ≃ₗ[𝕜] F) : E ≃L[𝕜] F :=
{ continuous_to_fun := e.to_linear_map.continuous_of_finite_dimensional',
  continuous_inv_fun := begin
    haveI : finite_dimensional 𝕜 F := e.finite_dimensional,
    exact e.symm.to_linear_map.continuous_of_finite_dimensional'
  end,
  ..e }

@[simp] lemma coe_to_continuous_linear_equiv'' (e : E ≃ₗ[𝕜] F) :
  (e.to_continuous_linear_equiv' : E →ₗ[𝕜] F) = e := rfl

@[simp] lemma coe_to_continuous_linear_equiv''' (e : E ≃ₗ[𝕜] F) :
  (e.to_continuous_linear_equiv' : E → F) = e := rfl

@[simp] lemma coe_to_continuous_linear_equiv_symm'' (e : E ≃ₗ[𝕜] F) :
  (e.to_continuous_linear_equiv'.symm : F →ₗ[𝕜] E) = e.symm := rfl

@[simp] lemma coe_to_continuous_linear_equiv_symm''' (e : E ≃ₗ[𝕜] F) :
  (e.to_continuous_linear_equiv'.symm : F → E) = e.symm := rfl

@[simp] lemma to_linear_equiv_to_continuous_linear_equiv' (e : E ≃ₗ[𝕜] F) :
  e.to_continuous_linear_equiv'.to_linear_equiv = e :=
by { ext x, refl }

@[simp] lemma to_linear_equiv_to_continuous_linear_equiv_symm' (e : E ≃ₗ[𝕜] F) :
  e.to_continuous_linear_equiv'.symm.to_linear_equiv = e.symm :=
by { ext x, refl }

end linear_equiv

namespace continuous_linear_map

variables [t2_space E] [finite_dimensional 𝕜 E]

/-- Builds a continuous linear equivalence from a continuous linear map on a finite-dimensional
vector space whose determinant is nonzero. -/
def to_continuous_linear_equiv_of_det_ne_zero'
  (f : E →L[𝕜] E) (hf : f.det ≠ 0) : E ≃L[𝕜] E :=
((f : E →ₗ[𝕜] E).equiv_of_det_ne_zero hf).to_continuous_linear_equiv'

@[simp] lemma coe_to_continuous_linear_equiv_of_det_ne_zero' (f : E →L[𝕜] E) (hf : f.det ≠ 0) :
  (f.to_continuous_linear_equiv_of_det_ne_zero' hf : E →L[𝕜] E) = f :=
by { ext x, refl }

@[simp] lemma to_continuous_linear_equiv_of_det_ne_zero_apply'
  (f : E →L[𝕜] E) (hf : f.det ≠ 0) (x : E) :
  f.to_continuous_linear_equiv_of_det_ne_zero' hf x = f x :=
rfl

end continuous_linear_map

end complete_field
