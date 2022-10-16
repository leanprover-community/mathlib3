/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.constructions.pi

/-!
# Marginals of multivariate functions
-/


noncomputable theory

open_locale classical big_operators topological_space ennreal

section
open finset
variables {α β γ : Type*}
lemma equiv.finset_image_univ_eq_univ [fintype α] [fintype β] (f : α ≃ β) :
  univ.image f = univ :=
by { ext x, simp only [mem_image, mem_univ, iff_true, exists_prop_of_true], use f.symm x, simp }

variables [comm_monoid β]

lemma prod_comp_equiv {s : finset α} (f : γ → β) (g : α ≃ γ) :
  ∏ a in s, f (g a) = ∏ b in s.image g, f b :=
begin
  refine prod_bij' (λ x _, g x) (λ a ha, finset.mem_image_of_mem _ ha) (λ _ _, rfl)
    (λ a _, g.symm a) _ (λ a _, g.symm_apply_apply a) (λ a _, g.apply_symm_apply a),
  simp only [finset.mem_image, exists_imp_distrib], rintro _ _ _ rfl, simpa
end

lemma prod_univ_comp_equiv [fintype α] [fintype γ] (f : γ → β) (g : α ≃ γ) :
  ∏ a, f (g a) = ∏ b, f b :=
by rw [prod_comp_equiv f g, g.finset_image_univ_eq_univ]

end


open function set measure_theory.outer_measure filter (hiding mem_pi) measurable_space


variables {ι ι' : Type*} {α : ι → Type*}

/-- Given one value over a unique, we get a dependent function. -/
def unique_elim [unique ι] (x : α (default : ι)) (i : ι) : α i :=
by { rw [unique.eq_default i], exact x }

@[simp] lemma unique_elim_default [unique ι] (x : α (default : ι)) :
  unique_elim x (default : ι) = x :=
rfl

lemma unique_elim_preimage [unique ι] (t : ∀ i, set (α i)) :
  unique_elim ⁻¹'  pi univ t = t (default : ι) :=
by { ext, simp [unique.forall_iff] }

attribute [simps] equiv.Pi_congr_left
open equiv
lemma Pi_congr_left_symm_preimage_pi (f : ι' ≃ ι) (s : set ι) (t : ∀ i, set (α i)) :
  (f.Pi_congr_left α).symm ⁻¹' (f ⁻¹' s).pi (λ i', t $ f i') = s.pi t :=
begin
  ext, simp only [mem_preimage, set.mem_pi, Pi_congr_left_symm_apply],
  convert f.forall_congr_left, refl
end


lemma Pi_congr_left_preimage_univ_pi (f : ι' ≃ ι) (t : ∀ i, set (α i)) :
  f.Pi_congr_left α ⁻¹' pi univ t = pi univ (λ i, t (f i)) :=
begin
  apply set.ext, rw [← (f.Pi_congr_left α).symm.forall_congr_left],
  intro x, simp only [mem_univ_pi, mem_preimage, apply_symm_apply, Pi_congr_left_symm_apply],
  exact f.forall_congr_left.symm
end

-- lemma Pi_congr_left'_symm_preimage_univ_pi (f : ι ≃ ι') (t : ∀ i, set (α i)) :
--   (f.Pi_congr_left' α).symm ⁻¹' pi univ t = pi univ (λ i, t (f.symm i)) :=
-- Pi_congr_left_preimage_univ_pi f.symm t

lemma measurable_unique_elim [unique ι] [∀ i, measurable_space (α i)] :
  measurable (unique_elim : α (default : ι) → Π i, α i) :=
by { simp_rw [measurable_pi_iff, unique.forall_iff, unique_elim_default], exact measurable_id }


lemma measurable_set.univ_pi_fintype {δ} {π : δ → Type*} [∀ i, measurable_space (π i)] [fintype δ]
  {t : Π i, set (π i)} (ht : ∀ i, measurable_set (t i)) : measurable_set (pi univ t) :=
measurable_set.pi finite_univ.countable (λ i _, ht i)

section new

variables [∀ i, measurable_space (α i)]

variables (α)
lemma measurable_eq_mp {i i' : ι} (h : i = i') : measurable (congr_arg α h).mp :=
by { cases h, exact measurable_id }

lemma measurable.eq_mp {β} [measurable_space β] {i i' : ι} (h : i = i') {f : β → α i}
  (hf : measurable f) : measurable (λ x, (congr_arg α h).mp (f x)) :=
(measurable_eq_mp α h).comp hf
variables {α}

-- section
-- variables (P : ι → Type*) (e : ι ≃ ι')
-- -- note: `@[simps]` generates a lemma where the equality is proven by `Pi_congr_left'._proof_1`
-- @[simp] lemma Pi_congr_left'_symm_apply (f : Π b, P (e.symm b)) (x : ι) :
--   (Pi_congr_left' P e).symm f x =
--   (congr_arg P $ e.symm_apply_apply _).mp (f (e x)) :=
-- rfl
-- end

lemma measurable_Pi_congr_left (f : ι' ≃ ι) : measurable (Pi_congr_left α f) :=
begin
  rw measurable_pi_iff,
  intro i,
  apply measurable.eq_mp α (f.apply_symm_apply i),
  exact measurable_pi_apply (f.symm i)
end

end new



lemma pred_update {α} {β : α → Type*} (P : ∀ ⦃a⦄, β a → Prop)
  (f : Π a, β a) (a' : α) (v : β a') (a : α) :
  P (update f a' v a) ↔ (a = a' ∧ P v) ∨ (a ≠ a' ∧ P (f a)) :=
by { rw [update], split_ifs, { subst h, simp }, { rw [← ne.def] at h, simp [h] }}

@[simp] lemma imp_and_neg_imp_iff (p q : Prop) [decidable p] : (p → q) ∧ (¬ p → q) ↔ q :=
by { by_cases p; simp [h] }

-- #print Union_unpair_prod
/- rename Union_prod to Union_prod_const.
Also prove Union_unpair_prod using this or similar -/
lemma Union_prod {ι α β} (s : ι → set α) (t : ι → set β) :
  (⋃ (x : ι × ι), (s x.1).prod (t x.2)) = (⋃ (i : ι), s i).prod (⋃ (i : ι), t i) :=
by { ext, simp }

-- set_option trace.simps.verbose true
attribute [simps apply symm_apply] subtype_equiv_right
/-- `s ∪ t` (using finset union) is equivalent to `s ∪ t` (using set union) -/
-- @[simps apply symm_apply] -- apply symm_apply
def equiv.finset_union {α} (s t : finset α) : ((s ∪ t : finset α) : set α) ≃ (s ∪ t : set α) :=
subtype_equiv_right $ by sorry --simp

open equiv
-- done below

lemma Union_congr {ι ι₂ α : Type*} {f : ι → set α} {g : ι₂ → set α} (h : ι → ι₂)
  (h1 : function.surjective h) (h2 : ∀ x, g (h x) = f x) : (⋃ x, f x) = ⋃ y, g y :=
(supr_congr h2).symm.trans $ h1.supr_comp _

lemma Inter_congr {ι ι₂ α : Type*} {f : ι → set α} {g : ι₂ → set α} (h : ι → ι₂)
  (h1 : function.surjective h) (h2 : ∀ x, g (h x) = f x) : (⋂ x, f x) = ⋂ y, g y :=
(infi_congr h2).symm.trans $ h1.infi_comp _

lemma Union_univ_pi {ι ι₂} {α : ι → Type*} (t : ∀ i, ι₂ → set (α i)) :
  (⋃ (x : ι → ι₂), pi univ (λ i, t i (x i))) = pi univ (λ i, ⋃ (j : ι₂), t i j) :=
by { ext, simp [classical.skolem] }



lemma surjective_decode_iget (α : Type*) [encodable α] [inhabited α] :
  surjective (λ n, (encodable.decode α n).iget) :=
λ x, ⟨encodable.encode x, by simp_rw [encodable.encodek]⟩

lemma eval_preimage {ι} {α : ι → Type*} {i : ι} {s : set (α i)} :
  eval i ⁻¹' s = pi univ (update (λ i, univ) i s) :=
by { ext x, simp [@forall_update_iff _ (λ i, set (α i)) _ _ _ _ (λ i' y, x i' ∈ y)] }

lemma eval_preimage' {ι} {α : ι → Type*} {i : ι} {s : set (α i)} :
  eval i ⁻¹' s = pi {i} (update (λ i, univ) i s) :=
by { ext, simp }

lemma mem_pi_univ {ι : Type*} {α : ι → Type*} (t : ∀ i, set (α i)) (x : ∀ i, α i) :
  x ∈ pi univ t ↔ ∀ i, x i ∈ t i :=
by simp

lemma pi_univ_ite {ι} {α : ι → Type*} (s : set ι) (t : ∀ i, set (α i)) :
  pi univ (λ i, if i ∈ s then t i else univ) = s.pi t :=
by { ext, simp_rw [set.mem_pi], apply forall_congr, intro i, split_ifs; simp [h] }

lemma pi_univ_eq_Inter {ι} {α : ι → Type*} (t : ∀ i, set (α i)) :
  pi univ t = ⋂ i, eval i ⁻¹' t i :=
by simp_rw [pi_def, mem_univ, Inter_true]

namespace measure_theory

namespace measure

variables [fintype ι] [fintype ι']
variables {m : Π i, outer_measure (α i)}
variables [Π i, measurable_space (α i)] {μ : Π i, measure (α i)} --[Π i, sigma_finite (μ i)]


variables [∀ i, sigma_finite (μ i)]

variable (μ)

-- remove
lemma pi_empty_left (h : ι → false) : measure.pi μ = dirac (λ i, (h i).elim) :=
begin
  haveI : is_empty ι := ⟨h⟩,
  convert pi_of_empty μ (λ i, (h i).elim)
end

lemma pi_unique_left [unique ι] : measure.pi μ = map unique_elim (μ (default : ι)) :=
begin
  apply pi_eq, intros s hs,
  rw [map_apply measurable_unique_elim (measurable_set.univ_pi_fintype hs), unique_elim_preimage],
  symmetry, convert finset.prod_singleton, rw [finset.ext_iff, unique.forall_iff], simp
end

open _root_.sum

/--  The type of dependent functions on a sum type `ι ⊕ ι'` is equivalent to the type of pairs of
  functions on `ι` and on `ι'`. This is a dependent version of `equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps]
def equiv.Pi_sum (π : ι ⊕ ι' → Type*) : ((Π i, π (inl i)) × (Π i', π (inr i'))) ≃ Π i, π i :=
{ to_fun := λ f, sum.rec f.1 f.2,
  inv_fun := λ g, ⟨λ i, g (inl i), λ i', g (inr i')⟩,
  left_inv := λ f, prod.ext rfl rfl,
  right_inv := λ g, by { ext (i|i); refl } }

def equiv.Pi_sum' (π : ι → Type*) (π' : ι' → Type*) :
  ((Π i, π i) × (Π i', π' i')) ≃ Π i, sum.elim π π' i :=
equiv.Pi_sum (sum.elim π π')

lemma pi_map_left (f : ι' ≃ ι) :
  map (f.Pi_congr_left α) (measure.pi (λ i', μ (f i'))) = measure.pi μ :=
begin
  refine (pi_eq _).symm, intros s hs,
  rw [map_apply _ (measurable_set.univ_pi_fintype hs)],
  { simp_rw [Pi_congr_left_preimage_univ_pi, pi_pi _ _,
    prod_univ_comp_equiv (λ i, μ i (s i)) f] },
  { apply measurable_Pi_congr_left }
end

lemma pi_sum {π : ι ⊕ ι' → Type*} [∀ i, measurable_space (π i)] (μ : ∀ i, measure (π i))
  [∀ i, sigma_finite (μ i)] :
  map (equiv.Pi_sum π) ((measure.pi (λ i, μ (sum.inl i))).prod (measure.pi (λ i, μ (sum.inr i)))) =
  measure.pi μ :=
begin
  refine (pi_eq _).symm, intros s hs,
  rw [map_apply],
  all_goals {sorry}
end

end measure

section marginal

open finset topological_space
variables {δ : Type*} {π : δ → Type*} [∀ x, measurable_space (π x)]
variables {μ : ∀ i, measure (π i)} [∀ i, sigma_finite (μ i)]
variables {E : Type*} [normed_add_comm_group E] [second_countable_topology E]
  [normed_space ℝ E] [complete_space E] [measurable_space E] [borel_space E]

/-- Integrate `f(x₁,…,xₙ)` over all variables `xᵢ` where `i ∈ s`. Return a function in the
  remaining variables (it will be constant in the `xᵢ` for `i ∈ s`).
  This is the marginal distribution of all variables not in `s`. -/
def marginal (μ : ∀ i, measure (π i)) (s : finset δ) (f : (Π i, π i) → E) (x : Π i, π i) :
  E :=
∫ y : Π i : (s : set δ), π i, f (λ i, if hi : i ∈ s then y ⟨i, hi⟩ else x i)
  ∂(measure.pi (λ i : (s : set δ), μ i))

/-- The integrand of `marginal _ _ f` is measurable if `f` is. -/
lemma _root_.measurable.marginal_aux {f : (Π i, π i) → E} (hf : measurable f) {s : finset δ}
  {x : Π i, π i} :
  measurable (λ (y : Π i : (s : set δ), π i), f (λ i, if hi : i ∈ s then y ⟨i, hi⟩ else x i)) :=
begin
  refine hf.comp _,
  rw measurable_pi_iff, intro i,
  by_cases h : i ∈ s,
  { simp [h, measurable_pi_apply] },
  { simp [h] }
end

/- Note: this notation is not a binder. This is more convenient since it returns a function. -/
notation `∫⋯∫_` s `, ` f ` ∂` μ:70 := marginal μ s f
notation `∫⋯∫_` s `, ` f := marginal volume s f

lemma marginal_empty (f : (Π i, π i) → E) : ∫⋯∫_ ∅, f ∂μ = f :=
begin
  haveI : subsingleton (Π (i : ((∅ : finset δ) : set δ)), π i) := ⟨λ x y, funext $ λ i, i.2.elim⟩,
  ext x,
  simp_rw [marginal, measure.pi_empty_left _ (λ i : ((∅ : finset δ) : set δ), i.prop)],
  sorry
  -- refine (integral_dirac' _ _ $ subsingleton.strongly_measurable _).trans (by simp)
end

lemma marginal_eq {s : finset δ} {x y : Π i, π i} (f : (Π i, π i) → E)
  (h : ∀ i ∉ s, x i = y i) : (∫⋯∫_ s, f ∂μ) x = (∫⋯∫_ s, f ∂μ) y :=
by { dsimp [marginal], rcongr, exact h _ ‹_› }

-- lemma mpr_refl {α} (h : α = α) (y : α) : h.mpr y = y :=
-- by simp only [eq_mp_eq_cast, eq_self_iff_true]

lemma set.union_apply_left' {α} {s t : set α} [decidable_pred (λ x, x ∈ s)] (H : s ∩ t ⊆ ∅)
  {a : α} (ha : a ∈ s) : equiv.set.union H ⟨a, set.mem_union_left _ ha⟩ = sum.inl ⟨a, ha⟩ :=
dif_pos ha

lemma set.union_apply_right' {α} {s t : set α} [decidable_pred (λ x, x ∈ s)] (H : s ∩ t ⊆ ∅)
  {a : α} (ha : a ∈ t) : equiv.set.union H ⟨a, set.mem_union_right _ ha⟩ = sum.inr ⟨a, ha⟩ :=
dif_neg $ λ h, H ⟨h, ha⟩

lemma marginal_union (f : (Π i, π i) → E) (hf : measurable f) (s t : finset δ) (hst : disjoint s t) :
  ∫⋯∫_ s ∪ t, f ∂μ = ∫⋯∫_ t, ∫⋯∫_ s, f ∂μ ∂μ :=
begin
  have : (s : set δ) ∩ (t : set δ) ⊆ ∅, { exact_mod_cast hst },
  let e : ((s ∪ t : finset δ) : set δ) ≃ (s : set δ) ⊕ (t : set δ) :=
  (finset_union s t).trans (equiv.set.union this),
  ext x,
  simp_rw [marginal, ← measure.pi_map_left _ e.symm],
  rw [integral_map, ← measure.pi_sum, integral_map, integral_prod_symm],
  -- dsimp only [e, set.union_symm_apply_left],
  all_goals {sorry},

  --
  -- { symmetry, congr' with x, congr' with y, congr' with i, symmetry,
        -- by_cases his : i ∈ s; by_cases hit : i ∈ t,
  --   { exact false.elim (this ⟨his, hit⟩) },
  --   all_goals { simp only [his, hit, Pi_congr_left_apply, dif_pos, or_false, false_or,
  --     measure.equiv.Pi_sum_apply, dif_neg, not_false_iff, finset.mem_union] },
  --   all_goals { dsimp only [e, trans_apply, finset_union_apply, set.union_apply_left,
  --   set.union_apply_right, subtype.coe_mk], rw [← heq_iff_eq], refine (eq_mpr_heq _ _).trans _ },
  --   exact congr_arg_heq _ (set.union_apply_left' this his),
  --   exact congr_arg_heq _ (set.union_apply_right' this hit) },

end

lemma marginal_singleton (f : (Π i, π i) → E) (hf : measurable f) (i : δ) :
  ∫⋯∫_ {i}, f ∂μ = λ x, ∫ xᵢ, f (function.update x i xᵢ) ∂(μ i) :=
begin
  letI : unique (({i} : finset δ) : set δ) :=
  ⟨⟨⟨i, finset.mem_singleton_self i⟩⟩, λ j, subtype.ext $ finset.mem_singleton.mp j.2⟩,
  ext x,
  simp_rw [marginal, measure.pi_unique_left _],
  rw [integral_map],
  congr' with y, dsimp only, congr' with j,
  by_cases hj : j = i,
  { cases hj.symm, simp only [dif_pos, finset.mem_singleton, update_same],
    exact @unique_elim_default _ (λ i : (({i} : finset δ) : set δ), π i) _ y },
  { simp [hj] },
  all_goals {sorry},
end

lemma marginal_univ [fintype δ] (f : (Π i, π i) → E) :
  ∫⋯∫_ finset.univ, f ∂μ = λ _, ∫ x, f x ∂(measure.pi μ) :=
begin
  let e : { j // j ∈ finset.univ} ≃ δ := equiv.subtype_univ_equiv finset.mem_univ,
  ext x,
  simp_rw [marginal, ← measure.pi_map_left μ e],
  rw [integral_map], congr' with y, congr' with i, simp [e], dsimp [e], refl,
  sorry, sorry
end

end marginal

end measure_theory
