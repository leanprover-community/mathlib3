/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro, Johannes Hölzl, Sander Dahmen

Dimension of modules and vector spaces.
-/
import linear_algebra.basis
import set_theory.ordinal
noncomputable theory

universes u u' u'' v v' w w'

variables {𝕜 : Type u} {V V₂ V₃ V₄ : Type v}
variables {ι : Type w} {ι' : Type w'} {η : Type u''} {φ : η → Type u'}
-- TODO: relax these universe constraints

open_locale classical

section vector_space
variables [discrete_field 𝕜] [add_comm_group V] [vector_space 𝕜 V]
include 𝕜
open submodule lattice function set

variables (𝕜 V)
def vector_space.dim : cardinal :=
cardinal.min
  (nonempty_subtype.2 (@exists_is_basis 𝕜 V _ _ _))
  (λ b, cardinal.mk b.1)
variables {𝕜 V}

open vector_space

section
set_option class.instance_max_depth 50
theorem is_basis.le_span (zero_ne_one : (0 : 𝕜) ≠ 1) {v : ι → V} {J : set V} (hv : is_basis 𝕜 v)
   (hJ : span 𝕜 J = ⊤) : cardinal.mk (range v) ≤ cardinal.mk J :=
begin
  cases le_or_lt cardinal.omega (cardinal.mk J) with oJ oJ,
  { have := cardinal.mk_range_eq_of_inj  (linear_independent.injective zero_ne_one hv.1),
    let S : J → set ι := λ j, (is_basis.repr hv j).support.to_set,
    let S' : J → set V := λ j, v '' S j,
    have hs : range v ⊆ ⋃ j, S' j,
    { intros b hb,
      rcases mem_range.1 hb with ⟨i, hi⟩,
      have : span 𝕜 J ≤ comap hv.repr (finsupp.supported 𝕜 𝕜 (⋃ j, S j)) :=
        span_le.2 (λ j hj x hx, ⟨_, ⟨⟨j, hj⟩, rfl⟩, hx⟩),
      rw hJ at this,
      replace : hv.repr (v i) ∈ (finsupp.supported 𝕜 𝕜 (⋃ j, S j)) := this trivial,
      rw [hv.repr_eq_single, finsupp.mem_supported, finsupp.support_single_ne_zero zero_ne_one.symm] at this,
      rw ← hi,
      apply mem_Union.2,
      rcases mem_Union.1 (this (mem_singleton _)) with ⟨j, hj⟩,
      use j,
      rw mem_image,
      use i,
      exact ⟨hj, rfl⟩ },
    refine le_of_not_lt (λ IJ, _),
    suffices : cardinal.mk (⋃ j, S' j) < cardinal.mk (range v),
    { exact not_le_of_lt this ⟨set.embedding_of_subset hs⟩ },
    refine lt_of_le_of_lt (le_trans cardinal.mk_Union_le_sum_mk
      (cardinal.sum_le_sum _ (λ _, cardinal.omega) _)) _,
    { exact λ j, le_of_lt (cardinal.lt_omega_iff_finite.2 $ finite_image _ (finset.finite_to_set _)) },
    { rwa [cardinal.sum_const, cardinal.mul_eq_max oJ (le_refl _), max_eq_left oJ] } },
  { rcases exists_finite_card_le_of_finite_of_linear_independent_of_span
      (cardinal.lt_omega_iff_finite.1 oJ) hv.1.to_subtype_range _ with ⟨fI, hi⟩,
    { rwa [← cardinal.nat_cast_le, cardinal.finset_card, finset.coe_to_finset,
        cardinal.finset_card, finset.coe_to_finset] at hi, },
    { rw hJ, apply set.subset_univ } },
end
end

/-- dimension theorem -/
theorem mk_eq_mk_of_basis {v : ι → V} {v' : ι' → V}
  (hv : is_basis 𝕜 v) (hv' : is_basis 𝕜 v') :
  cardinal.lift.{w w'} (cardinal.mk ι) = cardinal.lift.{w' w} (cardinal.mk ι') :=
begin
  rw ←cardinal.lift_inj.{(max w w') v},
  rw [cardinal.lift_lift, cardinal.lift_lift],
  apply le_antisymm,
  { convert cardinal.lift_le.{v (max w w')}.2 (hv.le_span zero_ne_one hv'.2),
    { rw cardinal.lift_max.{w v w'},
      apply (cardinal.mk_range_eq_of_inj (hv.injective zero_ne_one)).symm, },
    { rw cardinal.lift_max.{w' v w},
      apply (cardinal.mk_range_eq_of_inj (hv'.injective zero_ne_one)).symm, }, },
  { convert cardinal.lift_le.{v (max w w')}.2 (hv'.le_span zero_ne_one hv.2),
    { rw cardinal.lift_max.{w' v w},
      apply (cardinal.mk_range_eq_of_inj (hv'.injective zero_ne_one)).symm, },
    { rw cardinal.lift_max.{w v w'},
      apply (cardinal.mk_range_eq_of_inj (hv.injective zero_ne_one)).symm, }, }
end

theorem is_basis.mk_range_eq_dim {v : ι → V} (h : is_basis 𝕜 v) :
  cardinal.mk (range v) = dim 𝕜 V :=
begin
  have := show ∃ v', dim 𝕜 V = _, from cardinal.min_eq _ _,
  rcases this with ⟨v', e⟩,
  rw e,
  apply cardinal.lift_inj.1,
  rw cardinal.mk_range_eq_of_inj (h.injective zero_ne_one),
  convert @mk_eq_mk_of_basis _ _ _ _ _ _ _ _ _ h v'.property
end

theorem is_basis.mk_eq_dim {v : ι → V} (h : is_basis 𝕜 v) :
  cardinal.lift.{w v} (cardinal.mk ι) = cardinal.lift.{v w} (dim 𝕜 V) :=
by rw [←h.mk_range_eq_dim, cardinal.mk_range_eq_of_inj (h.injective zero_ne_one)]

variables [add_comm_group V₂] [vector_space 𝕜 V₂]

theorem linear_equiv.dim_eq (f : V ≃ₗ[𝕜] V₂) :
  dim 𝕜 V = dim 𝕜 V₂ :=
by letI := classical.dec_eq V;
letI := classical.dec_eq V₂; exact
let ⟨b, hb⟩ := exists_is_basis 𝕜 V in
cardinal.lift_inj.1 $ hb.mk_eq_dim.symm.trans (f.is_basis hb).mk_eq_dim

@[simp] lemma dim_bot : dim 𝕜 (⊥ : submodule 𝕜 V) = 0 :=
by letI := classical.dec_eq V;
  rw [← cardinal.lift_inj, ← (@is_basis_empty_bot pempty 𝕜 V _ _ _ not_nonempty_pempty).mk_eq_dim,
    cardinal.mk_pempty]

@[simp] lemma dim_top : dim 𝕜 (⊤ : submodule 𝕜 V) = dim 𝕜 V :=
linear_equiv.dim_eq (linear_equiv.of_top _ rfl)

lemma dim_of_field (𝕜 : Type*) [discrete_field 𝕜] : dim 𝕜 𝕜 = 1 :=
by rw [←cardinal.lift_inj, ← (@is_basis_singleton_one punit 𝕜 _ _).mk_eq_dim, cardinal.mk_punit]

lemma dim_span {v : ι → V} (hv : linear_independent 𝕜 v) :
  dim 𝕜 ↥(span 𝕜 (range v)) = cardinal.mk (range v) :=
by rw [←cardinal.lift_inj, ← (is_basis_span hv).mk_eq_dim,
    cardinal.mk_range_eq_of_inj (@linear_independent.injective ι 𝕜 V v _ _ _ zero_ne_one hv)]

lemma dim_span_set {s : set V} (hs : linear_independent 𝕜 (λ x, x : s → V)) :
  dim 𝕜 ↥(span 𝕜 s) = cardinal.mk s :=
by rw [← @set_of_mem_eq _ s, ← subtype.val_range]; exact dim_span hs

lemma dim_span_le (s : set V) : dim 𝕜 (span 𝕜 s) ≤ cardinal.mk s :=
begin
  classical,
  rcases
    exists_linear_independent linear_independent_empty (set.empty_subset s)
    with ⟨b, hb, _, hsb, hlib⟩,
  have hsab : span 𝕜 s = span 𝕜 b,
    from span_eq_of_le _ hsb (span_le.2 (λ x hx, subset_span (hb hx))),
  convert cardinal.mk_le_mk_of_subset hb,
  rw [hsab, dim_span_set hlib]
end

lemma dim_span_of_finset (s : finset V) :
  dim 𝕜 (span 𝕜 (↑s : set V)) < cardinal.omega :=
calc dim 𝕜 (span 𝕜 (↑s : set V)) ≤ cardinal.mk (↑s : set V) : dim_span_le ↑s
                             ... = s.card : by rw ←cardinal.finset_card
                             ... < cardinal.omega : cardinal.nat_lt_omega _

theorem dim_prod : dim 𝕜 (V × V₂) = dim 𝕜 V + dim 𝕜 V₂ :=
begin
  letI := classical.dec_eq V,
  letI := classical.dec_eq V₂,
  rcases exists_is_basis 𝕜 V with ⟨b, hb⟩,
  rcases exists_is_basis 𝕜 V₂ with ⟨c, hc⟩,
  rw [← cardinal.lift_inj,
      ← @is_basis.mk_eq_dim 𝕜 (V × V₂) _ _ _ _ _ (is_basis_inl_union_inr hb hc),
      cardinal.lift_add, cardinal.lift_mk,
      ← hb.mk_eq_dim, ← hc.mk_eq_dim,
      cardinal.lift_mk, cardinal.lift_mk,
      cardinal.add_def (ulift b) (ulift c)],
  exact cardinal.lift_inj.1 (cardinal.lift_mk_eq.2
      ⟨equiv.ulift.trans (equiv.sum_congr (@equiv.ulift b) (@equiv.ulift c)).symm ⟩),
end

theorem dim_quotient (p : submodule 𝕜 V) :
  dim 𝕜 p.quotient + dim 𝕜 p = dim 𝕜 V :=
by classical; exact let ⟨f⟩ := quotient_prod_linear_equiv p in dim_prod.symm.trans f.dim_eq

/-- rank-nullity theorem -/
theorem dim_range_add_dim_ker (f : V →ₗ[𝕜] V₂) : dim 𝕜 f.range + dim 𝕜 f.ker = dim 𝕜 V :=
begin
  haveI := λ (p : submodule 𝕜 V), classical.dec_eq p.quotient,
  rw [← f.quot_ker_equiv_range.dim_eq, dim_quotient]
end

lemma dim_range_le (f : V →ₗ[𝕜] V₂) : dim 𝕜 f.range ≤ dim 𝕜 V :=
by rw ← dim_range_add_dim_ker f; exact le_add_right (le_refl _)

lemma dim_map_le (f : V →ₗ V₂) (p : submodule 𝕜 V) : dim 𝕜 (p.map f) ≤ dim 𝕜 p :=
begin
  have h := dim_range_le (f.comp (submodule.subtype p)),
  rwa [linear_map.range_comp, range_subtype] at h,
end

lemma dim_range_of_surjective (f : V →ₗ[𝕜] V₂) (h : surjective f) : dim 𝕜 f.range = dim 𝕜 V₂ :=
begin
  refine linear_equiv.dim_eq (linear_equiv.of_bijective (submodule.subtype _) _ _),
  exact linear_map.ker_eq_bot.2 subtype.val_injective,
  rwa [range_subtype, linear_map.range_eq_top]
end

lemma dim_eq_surjective (f : V →ₗ[𝕜] V₂) (h : surjective f) : dim 𝕜 V = dim 𝕜 V₂ + dim 𝕜 f.ker :=
by rw [← dim_range_add_dim_ker f, ← dim_range_of_surjective f h]

lemma dim_le_surjective (f : V →ₗ[𝕜] V₂) (h : surjective f) : dim 𝕜 V₂ ≤ dim 𝕜 V :=
by rw [dim_eq_surjective f h]; refine le_add_right (le_refl _)

lemma dim_eq_injective (f : V →ₗ[𝕜] V₂) (h : injective f) : dim 𝕜 V = dim 𝕜 f.range :=
by rw [← dim_range_add_dim_ker f, linear_map.ker_eq_bot.2 h]; simp [dim_bot]

set_option class.instance_max_depth 37
lemma dim_submodule_le (s : submodule 𝕜 V) : dim 𝕜 s ≤ dim 𝕜 V :=
begin
  letI := classical.dec_eq V,
  rcases exists_is_basis 𝕜 s with ⟨bs, hbs⟩,
  have : linear_independent 𝕜 (λ (i : bs), submodule.subtype s i.val) :=
    (linear_independent.image hbs.1) (linear_map.disjoint_ker'.2
        (λ _ _ _ _ h, subtype.val_injective h)),
  rcases exists_subset_is_basis (this.to_subtype_range) with ⟨b, hbs_b, hb⟩,
  rw [←cardinal.lift_le, ← is_basis.mk_eq_dim hbs, ← is_basis.mk_eq_dim hb, cardinal.lift_le],
  have : subtype.val '' bs ⊆ b,
  { convert hbs_b,
    rw [@range_comp _ _ _ (λ (i : bs), (i.val)) (submodule.subtype s),
      ←image_univ, submodule.subtype],
    simp only [subtype.val_image_univ],
    refl },
  calc cardinal.mk ↥bs = cardinal.mk ((subtype.val : s → V) '' bs) :
      (cardinal.mk_image_eq $ subtype.val_injective).symm
    ... ≤ cardinal.mk ↥b :
      nonempty.intro (embedding_of_subset this),
end
set_option class.instance_max_depth 32

lemma dim_le_injective (f : V →ₗ[𝕜] V₂) (h : injective f) :
  dim 𝕜 V ≤ dim 𝕜 V₂ :=
by rw [dim_eq_injective f h]; exact dim_submodule_le _

lemma dim_le_of_submodule (s t : submodule 𝕜 V) (h : s ≤ t) : dim 𝕜 s ≤ dim 𝕜 t :=
dim_le_injective (of_le h) $ assume ⟨x, hx⟩ ⟨y, hy⟩ eq,
  subtype.eq $ show x = y, from subtype.ext.1 eq

section
variables [add_comm_group V₃] [vector_space 𝕜 V₃]
variables [add_comm_group V₄] [vector_space 𝕜 V₄]
set_option class.instance_max_depth 70
open linear_map

/-- This is mostly an auxiliary lemma for `dim_sup_add_dim_inf_eq` -/
lemma dim_add_dim_split
  (db : V₃ →ₗ[𝕜] V) (eb : V₄ →ₗ[𝕜] V) (cd : V₂ →ₗ[𝕜] V₃) (ce : V₂ →ₗ[𝕜] V₄)
  (hde : ⊤ ≤ db.range ⊔ eb.range)
  (hgd : ker cd = ⊥)
  (eq : db.comp cd = eb.comp ce)
  (eq₂ : ∀d e, db d = eb e → (∃c, cd c = d ∧ ce c = e)) :
  dim 𝕜 V + dim 𝕜 V₂ = dim 𝕜 V₃ + dim 𝕜 V₄ :=
have hf : surjective (copair db eb),
begin
  refine (range_eq_top.1 $ top_unique $ _),
  rwa [← map_top, ← prod_top, map_copair_prod]
end,
begin
  conv {to_rhs, rw [← dim_prod, dim_eq_surjective _ hf] },
  congr' 1,
  apply linear_equiv.dim_eq,
  fapply linear_equiv.of_bijective,
  { refine cod_restrict _ (pair cd (- ce)) _,
    { assume c,
      simp [add_eq_zero_iff_eq_neg],
      exact linear_map.ext_iff.1 eq c } },
  { rw [ker_cod_restrict, ker_pair, hgd, bot_inf_eq] },
  { rw [eq_top_iff, range_cod_restrict, ← map_le_iff_le_comap, map_top, range_subtype],
    rintros ⟨d, e⟩,
    have h := eq₂ d (-e),
    simp [add_eq_zero_iff_eq_neg] at ⊢ h,
    assume hde,
    rcases h hde with ⟨c, h₁, h₂⟩,
    refine ⟨c, h₁, _⟩,
    rw [h₂, _root_.neg_neg] }
end

lemma dim_sup_add_dim_inf_eq (s t : submodule 𝕜 V) :
  dim 𝕜 (s ⊔ t : submodule 𝕜 V) + dim 𝕜 (s ⊓ t : submodule 𝕜 V) = dim 𝕜 s + dim 𝕜 t :=
dim_add_dim_split (of_le le_sup_left) (of_le le_sup_right) (of_le inf_le_left) (of_le inf_le_right)
  begin
    rw [← map_le_map_iff (ker_subtype $ s ⊔ t), map_sup, map_top,
      ← linear_map.range_comp, ← linear_map.range_comp, subtype_comp_of_le, subtype_comp_of_le,
      range_subtype, range_subtype, range_subtype],
    exact le_refl _
  end
  (ker_of_le _ _ _)
  begin ext ⟨x, hx⟩, refl end
  begin
    rintros ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ eq,
    have : b₁ = b₂ := congr_arg subtype.val eq,
    subst this,
    exact ⟨⟨b₁, hb₁, hb₂⟩, rfl, rfl⟩
  end

lemma dim_add_le_dim_add_dim (s t : submodule 𝕜 V) :
  dim 𝕜 (s ⊔ t : submodule 𝕜 V) ≤ dim 𝕜 s + dim 𝕜 t :=
by rw [← dim_sup_add_dim_inf_eq]; exact le_add_right (le_refl _)

end

section fintype
variable [fintype η]
variables [∀i, add_comm_group (φ i)] [∀i, vector_space 𝕜 (φ i)]

open linear_map

lemma dim_pi : vector_space.dim 𝕜 (Πi, φ i) = cardinal.sum (λi, vector_space.dim 𝕜 (φ i)) :=
begin
  choose b hb using assume i, exists_is_basis 𝕜 (φ i),
  have : is_basis 𝕜 (λ (ji : Σ j, b j), std_basis 𝕜 (λ j, φ j) ji.fst ji.snd.val),
    by apply pi.is_basis_std_basis _ hb,
  rw [←cardinal.lift_inj, ← this.mk_eq_dim],
  simp [λ i, (hb i).mk_range_eq_dim.symm, cardinal.sum_mk]
end

lemma dim_fun {V η : Type u} [fintype η] [add_comm_group V] [vector_space 𝕜 V] :
  vector_space.dim 𝕜 (η → V) = fintype.card η * vector_space.dim 𝕜 V :=
by rw [dim_pi, cardinal.sum_const, cardinal.fintype_card]

lemma dim_fun_eq_lift_mul :
  vector_space.dim 𝕜 (η → V) = (fintype.card η : cardinal.{max u'' v}) *
    cardinal.lift.{v u''} (vector_space.dim 𝕜 V) :=
by rw [dim_pi, cardinal.sum_const_eq_lift_mul, cardinal.fintype_card, cardinal.lift_nat_cast]

lemma dim_fun' : vector_space.dim 𝕜 (η → 𝕜) = fintype.card η :=
by rw [dim_fun_eq_lift_mul, dim_of_field 𝕜, cardinal.lift_one, mul_one, cardinal.nat_cast_inj]

lemma dim_fin_fun (n : ℕ) : dim 𝕜 (fin n → 𝕜) = n :=
by simp [dim_fun']

end fintype

lemma exists_mem_ne_zero_of_ne_bot {s : submodule 𝕜 V} (h : s ≠ ⊥) : ∃ b : V, b ∈ s ∧ b ≠ 0 :=
begin
  classical,
  by_contradiction hex,
  have : ∀x∈s, (x:V) = 0, { simpa only [not_exists, not_and, not_not, ne.def] using hex },
  exact (h $ bot_unique $ assume s hs, (submodule.mem_bot 𝕜).2 $ this s hs)
end

lemma exists_mem_ne_zero_of_dim_pos {s : submodule 𝕜 V} (h : vector_space.dim 𝕜 s > 0) :
  ∃ b : V, b ∈ s ∧ b ≠ 0 :=
exists_mem_ne_zero_of_ne_bot $ assume eq, by rw [(>), eq, dim_bot] at h; exact lt_irrefl _ h

lemma exists_is_basis_fintype (h : dim 𝕜 V < cardinal.omega) :
  ∃ s : (set V), (is_basis 𝕜 (subtype.val : s → V)) ∧ nonempty (fintype s) :=
begin
  cases exists_is_basis 𝕜 V with s hs,
  rw [←cardinal.lift_lt, ← is_basis.mk_eq_dim hs, cardinal.lift_lt,
      cardinal.lt_omega_iff_fintype] at h,
  exact ⟨s, hs, h⟩
end

section rank

def rank (f : V →ₗ[𝕜] V₂) : cardinal := dim 𝕜 f.range

lemma rank_le_domain (f : V →ₗ[𝕜] V₂) : rank f ≤ dim 𝕜 V :=
by rw [← dim_range_add_dim_ker f]; exact le_add_right (le_refl _)

lemma rank_le_range (f : V →ₗ[𝕜] V₂) : rank f ≤ dim 𝕜 V₂ :=
dim_submodule_le _

lemma rank_add_le (f g : V →ₗ[𝕜] V₂) : rank (f + g) ≤ rank f + rank g :=
calc rank (f + g) ≤ dim 𝕜 (f.range ⊔ g.range : submodule 𝕜 V₂) :
  begin
    refine dim_le_of_submodule _ _ _,
    exact (linear_map.range_le_iff_comap.2 $ eq_top_iff'.2 $
      assume x, show f x + g x ∈ (f.range ⊔ g.range : submodule 𝕜 V₂), from
        mem_sup.2 ⟨_, mem_image_of_mem _ (mem_univ _), _, mem_image_of_mem _ (mem_univ _), rfl⟩)
  end
  ... ≤ rank f + rank g : dim_add_le_dim_add_dim _ _

@[simp] lemma rank_zero : rank (0 : V →ₗ[𝕜] V₂) = 0 :=
by rw [rank, linear_map.range_zero, dim_bot]

lemma rank_finset_sum_le {η} (s : finset η) (f : η → V →ₗ[𝕜] V₂) :
  rank (s.sum f) ≤ s.sum (λ d, rank (f d)) :=
@finset.sum_hom_rel _ _ _ _ _ (λa b, rank a ≤ b) f (λ d, rank (f d)) s (le_of_eq rank_zero)
      (λ i g c h, le_trans (rank_add_le _ _) (add_le_add_left' h))

variables [add_comm_group V₃] [vector_space 𝕜 V₃]

lemma rank_comp_le1 (g : V →ₗ[𝕜] V₂) (f : V₂ →ₗ[𝕜] V₃) : rank (f.comp g) ≤ rank f :=
begin
  refine dim_le_of_submodule _ _ _,
  rw [linear_map.range_comp],
  exact image_subset _ (subset_univ _)
end

lemma rank_comp_le2 (g : V →ₗ[𝕜] V₂) (f : V₂ →ₗ V₃) : rank (f.comp g) ≤ rank g :=
by rw [rank, rank, linear_map.range_comp]; exact dim_map_le _ _

end rank

end vector_space

section unconstrained_universes

variables {E : Type v'}
variables [discrete_field 𝕜] [add_comm_group V] [vector_space 𝕜 V]
          [add_comm_group E] [vector_space 𝕜 E]
open vector_space

/-- Version of linear_equiv.dim_eq without universe constraints. -/
theorem linear_equiv.dim_eq_lift (f : V ≃ₗ[𝕜] E) :
  cardinal.lift.{v v'} (dim 𝕜 V) = cardinal.lift.{v' v} (dim 𝕜 E) :=
begin
  cases exists_is_basis 𝕜 V with b hb,
  rw [← cardinal.lift_inj.1 hb.mk_eq_dim, ← (f.is_basis hb).mk_eq_dim, cardinal.lift_mk],
end

end unconstrained_universes
