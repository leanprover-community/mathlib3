import ring_theory.algebra data.matrix
import linear_algebra.finite_dimensional linear_algebra.matrix linear_algebra.determinant
import ring_theory.polynomial ring_theory.integral_closure
import algebra.big_operators

universes u v w

section


variables {ι₁ ι₂ α β γ : Type u} [ring α] [ring β] [add_comm_group γ] [module α β] [module β γ] [module α γ]
  [decidable_eq α] [decidable_eq β] [decidable_eq γ] [decidable_eq ι₁] [decidable_eq ι₂]
  {v₁ : ι₁ → β} {v₂ : ι₂ → γ} (hv₁ : is_basis α v₁) (hv₂ : is_basis β v₂) (f : ι₂ × ι₁ →₀ α)
#check finsupp.map_range (λ (g : ι₁ →₀ α), finsupp.sum g (λ (a : ι₁) (b : α), b • v₁ a)) sorry (finsupp.curry f)

end

class field_extension (α : Type u) (β : Type v) [discrete_field α] [discrete_field β] extends algebra α β

namespace field_extension

section field_norm

open finite_dimensional

variables (α : Type u) [discrete_field α]

def mul_map {β : Type v} [discrete_field β] [field_extension α β] [finite_dimensional α β] (b : β) : β →ₗ[α] β :=
{ to_fun := λ x, b * x,
  add := mul_add b,
  smul := λ a, algebra.mul_smul_comm a b }

lemma mul_map_mul {β : Type v} [discrete_field β] [field_extension α β] [finite_dimensional α β] (b c : β) :
  mul_map α (b * c) = (mul_map α b).comp (mul_map α c) := sorry

variables (β : Type v) [discrete_field β] [field_extension α β] [finite_dimensional α β]

def fin_basis : set β :=
classical.some $ exists_is_basis_finite α β

noncomputable instance fin_basis_fintype : fintype (fin_basis α β) :=
(classical.some_spec $ exists_is_basis_finite α β).2.fintype

lemma fin_basis_is_basis : is_basis α (subtype.val : fin_basis α β → β) :=
(classical.some_spec $ exists_is_basis_finite α β).1

--instance : module α β := by apply_instance
--noncomputable def mul_matrix (b : β) : matrix {x // x ∈ fin_basis α β} {x // x ∈ fin_basis α β} α :=
--@linear_equiv.to_fun α (β →ₗ[α] β) _ _ _ _ linear_map.module matrix.module
--  (lin_equiv_matrix (fin_basis_is_basis α β) (fin_basis_is_basis α β)) (mul_map α b)

noncomputable def mul_matrix (b : β) : matrix {x // x ∈ fin_basis α β} {x // x ∈ fin_basis α β} α :=
by { letI : module α β := algebra.to_module α β,
     letI : module α (β →ₗ[α] β) := linear_map.module,
     letI : module α (matrix {x // x ∈ fin_basis α β} {x // x ∈ fin_basis α β} α) := matrix.module,
     exact (lin_equiv_matrix (fin_basis_is_basis α β) (fin_basis_is_basis α β)).to_fun (mul_map α b) }

noncomputable def field_norm (b : β) : α := matrix.det $ mul_matrix α β b

lemma test (α β γ : Type*) [discrete_field α] [add_comm_group β] [add_comm_group γ]
  [module α β] [module α γ] (e : β ≃ₗ[α] γ) : e.to_fun = e.to_linear_map.to_fun := rfl

@[simp] lemma norm_mul (b c : β) : field_norm α β (b * c) = field_norm α β b * field_norm α β c :=
sorry
/-begin
unfold field_norm,
unfold mul_matrix,
simp,
rw [←matrix.det_mul],
congr,
conv_rhs { rw [←smul_eq_mul], congr, skip, rw [test] },
rw[←linear_map.smul (lin_equiv_matrix _ _).to_linear_map ((lin_equiv_matrix _ _).to_fun (mul_map α b)) (mul_map α c)],

end-/

lemma norm_base (a : α) : field_norm α β (algebra_map β a) = a ^ findim α β := sorry

lemma norm_zero : field_norm α β 0 = 0 := sorry

lemma norm_zero_iff_zero (b : β) : field_norm α β b = 0 ↔ b = 0 := sorry

end field_norm

end field_extension

section

open polynomial

variables (α : Type u) [discrete_field α]
variables {β : Type v} [discrete_field β] [field_extension α β]

instance mpp : module (polynomial α) (polynomial α) := by apply_instance

/-- The ideal of polynomial over α that vanish at b. -/
private def vanishing_ideal (b : β) : ideal (polynomial α) := is_ring_hom.ker (aeval α β b)

lemma mem_vanishing_ideal_iff (b : β) (p : polynomial α) : p ∈ vanishing_ideal α b ↔ aeval α β b p = 0 :=
is_ring_hom.mem_ker _ _

instance (b : β) : ideal.is_principal (vanishing_ideal α b) := by apply_instance

noncomputable def minimal_polynomial {b : β} (hb : is_integral α b) : polynomial α :=
  ideal.is_principal.generator (vanishing_ideal α b) * C (leading_coeff $ ideal.is_principal.generator (vanishing_ideal α b))⁻¹

end

namespace minimal_polynomial

open polynomial ideal ideal.is_principal

variables (α : Type u) [discrete_field α]
variables {β : Type v} [discrete_field β] [field_extension α β]
variables {b : β} (hb : is_integral α b)

lemma mem_vanishing_ideal : minimal_polynomial α hb ∈ vanishing_ideal α b :=
ideal.mul_mem_right _ (generator_mem _)

include hb
lemma vanishing_ideal_ne_bot_of_is_integral : vanishing_ideal α b ≠ ⊥ :=
λ h, begin cases hb with p hp,
  have : p = 0, by { rw [←submodule.mem_bot (polynomial α), ←h, mem_vanishing_ideal_iff], exact hp.2 },
  rw [this] at hp,
  exact not_monic_zero hp.1
end

lemma gen_ne_zero : generator (vanishing_ideal α b) ≠ 0 :=
mt (eq_bot_iff_generator_eq_zero _).mpr $ vanishing_ideal_ne_bot_of_is_integral α hb

lemma C_ne_zero : (leading_coeff $ ideal.is_principal.generator (vanishing_ideal α b))⁻¹ ≠ 0 :=
λ h, by { rw [inv_eq_zero, leading_coeff_eq_zero] at h, exact (gen_ne_zero α hb) h }

lemma nonzero : minimal_polynomial α hb ≠ 0 :=
mul_ne_zero (gen_ne_zero α hb) (λ h, by { rw [←C_0, C_inj] at h, exact (C_ne_zero α hb) h })

lemma monic : monic (minimal_polynomial α hb) :=
monic_mul_leading_coeff_inv (gen_ne_zero α hb)

lemma aeval_zero : aeval α β b (minimal_polynomial α hb) = 0 :=
by { rw [←mem_vanishing_ideal_iff], exact mem_vanishing_ideal _ _ }

lemma degree_pos : degree (minimal_polynomial α hb) > 0 :=
classical.by_contradiction (λ hn,
begin
  rw [not_lt, degree_le_zero_iff] at hn,
  let f := minimal_polynomial α hb,
  have hv : aeval α β b f = 0, from aeval_zero α hb,
  change eval₂ (algebra_map β) b f = 0 at hv,
  change f = C (coeff f 0) at hn,
  rw [hn, eval₂_C, ←algebra.map_zero α β] at hv,
  rw [is_field_hom.injective (algebra_map β) hv, C_0] at hn,
  exact (nonzero α hb) hn
end)

lemma aeval_zero_iff_dvd {p : polynomial α} (hp : aeval α β b p = 0) : minimal_polynomial α hb ∣ p :=
begin
rw [←mem_vanishing_ideal_iff, mem_iff_generator_dvd] at hp,
exact (mul_dvd_of_is_unit_right $ is_unit_iff_degree_eq_zero.mpr $ degree_C $ C_ne_zero α hb).mpr hp
end

lemma minimal {p : polynomial α} (h0 : p ≠ 0) (hp : aeval α β b p = 0) :
  degree (minimal_polynomial α hb) ≤ degree p :=
begin
cases exists_eq_mul_right_of_dvd (aeval_zero_iff_dvd α hb hp) with q h,
have hq : q ≠ 0, from λ hn, by { rw [hn, mul_zero] at h, exact h0 h },
rw [h],
exact degree_le_mul_left _ hq
end

lemma not_is_unit : ¬ is_unit (minimal_polynomial α hb) :=
λ h, not_lt.mpr (le_refl (0 : with_bot ℕ))
  (by { convert degree_pos α hb, exact eq.symm (degree_eq_zero_of_is_unit h) })

lemma irreducible : irreducible (minimal_polynomial α hb) :=
classical.by_contradiction (λ hn,
begin
  unfold irreducible at hn,
  rw [not_and] at hn,
  replace hn := hn (not_is_unit α hb),
  rw [classical.not_forall] at hn,
  cases hn with q1 hn,
  rw [classical.not_forall] at hn,
  cases hn with q2 hn,
  apply hn,
  intro hq,
  rw [@or_iff_not_and_not _ _ (classical.dec _) (classical.dec _)],
  intro hnu,
  have h0q1 : q1 ≠ 0, from λ h, by {rw [h, zero_mul] at hq, exact (nonzero α hb) hq},
  have hq1 : 0 < (nat_degree q1 : with_bot ℕ),
    { rw [←degree_eq_nat_degree h0q1], exact degree_pos_of_ne_zero_of_nonunit h0q1 hnu.1 },
  have h0q2 : q2 ≠ 0, from λ h, by {rw [h, mul_zero] at hq, exact (nonzero α hb) hq},
  have hq2 : 0 < (nat_degree q2 : with_bot ℕ),
    { rw [←degree_eq_nat_degree h0q2], exact degree_pos_of_ne_zero_of_nonunit h0q2 hnu.2 },
  rw [←with_bot.coe_zero, with_bot.coe_lt_coe] at hq1 hq2,
  have hq1q : ¬degree (minimal_polynomial α hb) ≤ degree q1, from
    suffices ¬nat_degree (minimal_polynomial α hb) ≤ nat_degree q1,
      by rwa [degree_eq_nat_degree h0q1, degree_eq_nat_degree (nonzero α hb), with_bot.coe_le_coe],
    (λ h, begin
      rw [hq, nat_degree_mul_eq h0q1 h0q2] at h,
      have : nat_degree q1 > nat_degree q1 + 0, from lt_of_lt_of_le (add_lt_add_left hq2 _) h,
      rw [add_zero] at this,
      exact (not_lt.mpr (le_refl _)) this
    end),
  have hq2q : ¬degree (minimal_polynomial α hb) ≤ degree q2, from
    suffices ¬nat_degree (minimal_polynomial α hb) ≤ nat_degree q2,
      by rwa [degree_eq_nat_degree h0q2, degree_eq_nat_degree (nonzero α hb), with_bot.coe_le_coe],
    (λ h, begin
      rw [hq, nat_degree_mul_eq h0q1 h0q2] at h,
      have : nat_degree q2 > 0 + nat_degree q2, from lt_of_lt_of_le (add_lt_add_right hq1 _) h,
      rw [zero_add] at this,
      exact (not_lt.mpr (le_refl _)) this
    end),
  have h : eval₂ (algebra_map β) b (minimal_polynomial α hb) = 0, from aeval_zero α hb,
  rw [hq, eval₂_mul] at h,
  cases (integral_domain.eq_zero_or_eq_zero_of_mul_eq_zero _ _ h) with h h,
  { exact hq1q (minimal α hb h0q1 h) },
  { exact hq2q (minimal α hb h0q2 h) }
end)

end minimal_polynomial

section finite_dimensional

open vector_space

--TODO: universe issue with cardinals
variables (α : Type u) [discrete_field α]
variables {β : Type u} [discrete_field β] [field_extension α β] [finite_dimensional α β]
variables (b : β)

instance mf : module α (ℕ →₀ α) := finsupp.module ℕ α

def power_basis : (ℕ →₀ α) →ₗ[α] β :=
{ to_fun := λ f, finsupp.sum f (λ i a, algebra_map β a * b ^ i),
  add := λ f g, begin refine finsupp.sum_add_index _ _,
      { intro, rw [algebra.map_zero, zero_mul] },
      { intros, rw [algebra.map_add, add_mul] } end,
  smul := λ f g, begin
      rw [finsupp.sum_smul_index, finsupp.smul_sum],
      conv_rhs { congr, skip, funext, rw [algebra.smul_def, ←mul_assoc, ←algebra.map_mul] },
      { intro, rw [algebra.map_zero, zero_mul] } end }

--TODO: set priorities correct to avoid these instances
instance ms (p : submodule α (ℕ →₀ α)) : module α p := submodule.module p
instance vs (p : submodule α (ℕ →₀ α)) : vector_space α p := vector_space.mk α p

--instance (α : Type*) [division_ring α] : ring α := by apply_instance --hint
--TODO: move
lemma smul_eq_zero_iff_eq_zero_left {α β : Type*} [division_ring α] [decidable_eq α] [add_comm_group β] [module α β]
  (r : α) {b : β} (hb : b ≠ 0) : r • b = 0 ↔ r = 0 :=
⟨λ h, classical.by_contradiction (λ hn, begin
  have hr : r⁻¹ • r • b = r⁻¹ • 0, from congr_arg _ h,
  rw [smul_smul, smul_zero] at hr,
  apply hb,
  rwa [←one_smul α b, ←division_ring.inv_mul_cancel hn],
end),
λ h, by { rw [h, zero_smul] }⟩
--TODO: move
lemma smul_eq_zero_iff_eq_zero_right {α β : Type*} [division_ring α] [decidable_eq α] [add_comm_group β] [module α β]
  {r : α} (hr : r ≠ 0) (b : β) : r • b = 0 ↔ b = 0 :=
⟨λ h, classical.by_contradiction (λ hn,
  by { rw [smul_eq_zero_iff_eq_zero_left _ hn] at h, contradiction, apply_instance }),
λ h, by { rw [h, smul_zero] }⟩

--TODO: move
lemma smul_inj {α β : Type*} [division_ring α] [decidable_eq α] [add_comm_group β] [module α β]
  (b c : β) {r : α} (hr : r ≠ 0) : r • b = r • c ↔ b = c :=
by rw [←sub_eq_zero, ←smul_sub, smul_eq_zero_iff_eq_zero_right hr, sub_eq_zero]


--TODO: exists_is_basis has decidable_eq α and discrete_field α !!!

-- move
lemma sum_ite {α β γ : Type*} [decidable_eq α] [has_zero β] [add_comm_monoid γ]
  (f : α →₀ β) (g : α → β → γ) (hg : ∀ a : α, g a 0 = 0) (a : α) :
  finsupp.sum f (λ (a₂ : α) (b : β), ite (a₂ = a) (g a b) 0) =
  g a (f a) :=
suffices finsupp.sum f (λ (a₂ : α) (b : β), ite (a₂ = a) (g a b) 0) =
  (finset.singleton a).sum (λ (a₂ : α), ite (a₂ = a) (g a (f a₂)) 0),
  by { convert this, rw [finset.sum_singleton, if_pos rfl] },
begin
  unfold finsupp.sum,
  by_cases ha : a ∈ f.support,
  { refine (finset.sum_subset _ _).symm,
    { assume x hx, rw [finset.mem_singleton] at hx, rwa [hx] },
    { assume x _ hx, rw [finset.not_mem_singleton] at hx, rwa [if_neg] } },
  { convert (rfl : (0:γ) = 0),
    { apply finset.sum_eq_zero,
      intros j hj,
      apply if_neg,
      intro h,
      exact ha (h ▸ hj) },
    { apply finset.sum_eq_zero,
      intros j hj,
      rw [finset.mem_singleton] at hj,
      rw [if_pos hj],
      convert hg a,
      have h : ¬(f j ≠ 0), from mt (finsupp.mem_support_to_fun f j).mpr ((eq.symm hj) ▸ ha),
      rwa [ne.def, classical.not_not] at h } }
end

--move
lemma finsupp.curry_apply {α β γ : Type*} [decidable_eq α] [decidable_eq β] [decidable_eq γ] [add_comm_monoid γ]
  (f : (α × β) →₀ γ) (x : α) (y : β) : ((finsupp.curry f) x) y = f (x, y) :=
begin
change ((f.sum $ λ p c, finsupp.single p.1 (finsupp.single p.2 c)) x) y = f (x, y),
rw [finsupp.sum_apply, finsupp.sum_apply],
conv_lhs { congr, skip, funext, rw [finsupp.single_apply],
  change (ite (a₁.fst = x) (finsupp.single (a₁.snd) b) 0).to_fun y,
  rw [show (ite (a₁.fst = x) (finsupp.single (a₁.snd) b) 0).to_fun y =
    ite (a₁ = (x, y)) b 0, { split_ifs with hx h,
    { rwa [show (finsupp.single _ _).to_fun _ = _, from finsupp.single_apply, h, if_pos rfl] },
    { rw [show (finsupp.single _ _).to_fun _ = _, from finsupp.single_apply],
      rw [show a₁ = (a₁.fst, a₁.snd), from eq.symm prod.mk.eta, ←hx, prod.mk.inj_iff, not_and] at h,
      rwa [if_neg (h rfl)] },
    { rw [show a₁ = (a₁.fst, a₁.snd), from eq.symm prod.mk.eta, prod.mk.inj_iff] at h, exact false.elim (hx h.1) },
    { refl } }]
 },
refine sum_ite f (λ _ b, b) _ _,
intro _, refl
end

lemma finsupp.sum_smul {α β γ δ : Type*} [has_zero β] [ring γ] [add_comm_group δ] [module γ δ]
  (f : α →₀ β) (g : α → β → γ) (x : δ) : f.sum (λ a b, g a b • x) = (f.sum (λ a b, g a b)) • x :=
begin
letI : is_add_monoid_hom (λ (g : γ), g • x) :=
  { map_zero := zero_smul _ _,
    map_add := λ _ _, add_smul _ _ x },
exact finset.sum_hom (λ g : γ, g • x)
end

set_option class.instance_max_depth 50

-- move
lemma finsupp_basis (α : Type*) (ι : Type*) [discrete_field α] [decidable_eq ι] :
  is_basis α (λ i : ι, finsupp.single i (1:α)) :=
begin
  split,
  { rw [linear_independent_iff],
    intros f hf,
    ext i,
    rw [finsupp.total_apply, finsupp.ext_iff] at hf,
    replace hf := hf i,
    rw [finsupp.sum_apply] at hf,
    conv_lhs at hf { congr, skip, funext, rw [finsupp.smul_single, finsupp.single_apply] },
    rwa [sum_ite, smul_eq_mul, mul_one] at hf,
    intro _, exact zero_smul _ _ },
  { rw [submodule.eq_top_iff'],
    intro f,
    rw [←set.image_univ, finsupp.mem_span_iff_total],
    have H : f ∈ finsupp.supported α α (set.univ : set ι),
      { rw [finsupp.supported_univ], exact submodule.mem_top },
    existsi [f, H],
    rw [finsupp.total_apply],
    ext i,
    rw [finsupp.sum_apply],
    conv_lhs { congr, skip, funext, rw [finsupp.smul_single, finsupp.single_apply] },
    rw [sum_ite, smul_eq_mul, mul_one],
    intro _, exact zero_smul _ _ }
end

--move
lemma comp_basis {ι₁ ι₂ α β γ : Type*} [ring α] [ring β] [add_comm_group γ] [module α β] [module β γ] [module α γ]
  [decidable_eq α] [decidable_eq β] [decidable_eq γ] [decidable_eq ι₁] [decidable_eq ι₂]
  {v₁ : ι₁ → β} {v₂ : ι₂ → γ} (hv₁ : is_basis α v₁) (hv₂ : is_basis β v₂)
  (hm : ∀ (a : α) (b : β) (g : γ), a • b • g = (a • b) • g) :
  is_basis α (λ i : ι₂ × ι₁, v₁ i.snd • v₂ i.fst) :=
begin
  split,
  { rw [linear_independent_iff],
    assume f hf,
    ext i,
    rw [finsupp.total_apply] at hf,
    conv_lhs at hf { congr, skip, funext, rw [hm] },
    rw [←finsupp.sum_curry_index f (λ (i₂ : ι₂) (i₁ : ι₁) (a : α), (a • v₁ i₁) • v₂ i₂)] at hf,
    { change (finsupp.curry f).sum (λ (i₂ : ι₂) (f : ι₁ →₀ α), f.sum ((λ (i₁ : ι₁) (a : α), (a • v₁ i₁) • v₂ i₂))) = 0 at hf,
      conv_lhs at hf { congr, skip, funext, rw [finsupp.sum_smul] },
      let e := λ (i₁ : ι₁) (a : α), a • v₁ i₁,
      have h : _ := linear_independent_iff.mp hv₂.1 (finsupp.map_range (λ g, finsupp.sum g e) finsupp.sum_zero_index (finsupp.curry f)),
      rw [finsupp.total_apply, finsupp.sum_map_range_index] at h,
      replace h := h hf,
      have h2 : (finsupp.map_range (λ (g : ι₁ →₀ α), finsupp.sum g e) finsupp.sum_zero_index
        (finsupp.curry f)) i.fst = (0 : ι₂ →₀ β) i.fst, by { apply congr_fun, congr, exact h },
      rw [finsupp.map_range_apply] at h2,
      have h3 : (finsupp.curry f) (i.fst) = 0, from linear_independent_iff.mp hv₁.1 _ h2,
      have h4 : ((finsupp.curry f) (i.fst)) (i.snd) = 0, by { rw [h3], refl },
      rwa [finsupp.curry_apply, prod.mk.eta] at h4,
      intro _, rw [zero_smul] },
    { intros _ _, simp only [zero_smul] },
    { intros _ _ _ _, simp only [add_smul] } },
  { rw [submodule.eq_top_iff'],
    intro g,
    rw [←set.image_univ, finsupp.mem_span_iff_total],
    let f := finsupp.uncurry (finsupp.map_range hv₁.repr.to_fun (hv₁.repr).map_zero (hv₂.repr g)),
    have H : f ∈ finsupp.supported α α (set.univ : set (ι₂ × ι₁)),
      { rw [finsupp.supported_univ], exact submodule.mem_top },
    existsi [f, H],
    rw [finsupp.total_apply],
    conv_lhs { congr, skip, funext, rw [hm] },
    rw [←finsupp.sum_curry_index f (λ (i₂ : ι₂) (i₁ : ι₁) (a : α), (a • v₁ i₁) • v₂ i₂)],
    have : finsupp.curry f = finsupp.map_range hv₁.repr.to_fun (hv₁.repr).map_zero (hv₂.repr g), from
      finsupp.finsupp_prod_equiv.right_inv _,
    rw [this, finsupp.sum_map_range_index],
    change (hv₂.repr g).sum (λ (i₂ : ι₂) (b : β), (hv₁.repr b).sum (λ (i₁ : ι₁) (a : α), (a • v₁ i₁) • v₂ i₂)) = g,
    conv_lhs { congr, skip, funext, rw [finsupp.sum_smul],
      rw [show finsupp.sum (hv₁.repr b) (λ (i₁ : ι₁) (a : α), a • v₁ i₁) = ((finsupp.total ι₁ β α v₁).comp hv₁.repr) b,
        by simp only [finsupp.total_apply, linear_map.comp_apply]],
      rw [hv₁.total_comp_repr, linear_map.id_apply] },
    rw [show finsupp.sum (hv₂.repr g) (λ (i₂ : ι₂) (b : β), b • v₂ i₂) = ((finsupp.total ι₂ γ β v₂).comp hv₂.repr) g,
        by simp only [finsupp.total_apply, linear_map.comp_apply]],
    rw [hv₂.total_comp_repr, linear_map.id_apply],
    { intro _, exact finsupp.sum_zero_index },
    { intros _ _, simp only [zero_smul] },
    { intros _ _ _ _, simp only [add_smul] } }
end

instance fhint (α β η : Type*) [discrete_field α] [discrete_field β] [algebra α β]
  [decidable_eq η] : module α (η →₀ β) := by apply_instance

variables {ι : Type*} [decidable_eq ι] {v : ι → β} (hv : is_basis α v)
variables {η : Type*} [decidable_eq η] {f : ι × η →₀ α} {i : ι × η}

#check linear_independent_iff.mp hv.1 (finsupp.map_range
  (λ g : η →₀ α, g.sum (λ (j : ι) (g : η →₀ α), (g i.2) • (v j))) finsupp.sum_zero_index (finsupp.curry f)),
#check @linear_independent_iff


lemma finsupp_basis2 (α β ι η : Type*) [discrete_field α] [discrete_field β] [algebra α β]
  [decidable_eq ι] [decidable_eq η] {v : ι → β} (hv : is_basis α v) :
  is_basis α (λ i : ι × η, finsupp.single i.2 (v i.1)) :=
begin
  split,
  { rw [linear_independent_iff],
    intros f hf,
    ext i,
    rw [finsupp.total_apply, finsupp.ext_iff] at hf,
    replace hf := hf i.2,
    rw [finsupp.sum_apply] at hf,
    conv_lhs at hf { congr, skip, funext, rw [finsupp.smul_single, finsupp.single_apply] },
    rw [←finsupp.sum_curry_index f (λ (j : ι) (n : η) (b : α), ite (n = i.snd) (b • v j) 0)] at hf,
    { change (finsupp.curry f).sum (λ (k : ι) (g : η →₀ α), g.sum (λ (n : η) (b : α), ite (n = i.snd) (b • v k) 0)) = 0 at hf,
      conv_lhs at hf { congr, skip, funext,
        rw [show (λ (n : η) (b : α), ite (n = i.snd) (b • v k) 0) =
          (λ (n : η) (b : α), (ite (n = i.snd) b 0) • v k),
          by { ext, split_ifs, refl, rw [zero_smul] }],
        rw [finsupp.sum_smul, sum_ite _ (λ (n : η) (b : α), b) (λ _, rfl)] },
      change (finsupp.curry f).sum (λ (j : ι) (g : η →₀ α), g i.2 • v j) = 0 at hf,
      sorry
    },
    { sorry },
    { sorry } },
  { rw [submodule.eq_top_iff'],
    intro f,
    rw [←set.image_univ, finsupp.mem_span_iff_total],
    have H : f ∈ finsupp.supported α α (set.univ : set ι),
      { rw [finsupp.supported_univ], exact submodule.mem_top },
    existsi [f, H],
    rw [finsupp.total_apply],
    ext i,
    rw [finsupp.sum_apply],
    conv_lhs { congr, skip, funext, rw [finsupp.smul_single, finsupp.single_apply] },
    rw [sum_ite, smul_eq_mul, mul_one],
    intro _, exact zero_smul _ _ }
end


set_option profiler true
set_option pp.universes true
-- move
lemma dim_finsupp (α : Type u) (β : Type w) (η : Type v) [discrete_field α] [discrete_field β]
  [decidable_eq η] [algebra α β] :
  dim α (η →₀ β) = cardinal.lift.{v w} (cardinal.mk η) * cardinal.lift.{w v} (dim α β) :=
let ⟨b, hb⟩ := exists_is_basis α β in
have h : is_basis α (λ i : η × b, _), from
  comp_basis hb (finsupp_basis β η) sorry,
calc dim α (η →₀ β) = cardinal.lift.{(max v w) (max v w)} (dim α (η →₀ β))      : eq.symm $ cardinal.lift_id _
                ... = cardinal.lift.{(max v w) (max v w)} (cardinal.mk (η × b)) : eq.symm $ h.mk_eq_dim
                ... = cardinal.lift.{(max v w) (max v w)} (cardinal.lift.{v w} (cardinal.mk η) * cardinal.lift.{w v} (cardinal.mk b)) : by rw [cardinal.mk_prod]
                ... = cardinal.lift.{v w} (cardinal.mk η) * cardinal.lift.{w (max w v)} (cardinal.mk.{w} b) : by rw[cardinal.lift_mul, cardinal.lift_lift, cardinal.lift_lift, cardinal.lift_umax]
                ... = cardinal.lift.{v w} (cardinal.mk η) * cardinal.lift.{w v} (cardinal.lift.{w w} (cardinal.mk.{w} b)) : by rw [cardinal.lift_id, cardinal.lift_umax]
                ... = cardinal.lift.{v w} (cardinal.mk η) * cardinal.lift.{w v} (dim α β) : by rw [hb.mk_eq_dim, cardinal.lift_id]
--dim_lt_omega
lemma dim_finsupp_findim (α : Type u) (β : Type w) (η : Type v) [discrete_field α] [discrete_field β]
  [decidable_eq η] [algebra α β] [finite_dimensional α β] :
  dim α (η →₀ β) = cardinal.lift (cardinal.mk η) :=
begin
  convert dim_finsupp α β η,
  sorry
end

lemma power_basis.ker_omega : dim α (power_basis α b).ker ≥ cardinal.omega :=
begin
  -- Assume that the kernel has finite dimension
  by_contradiction h1,
  rw [←lt_iff_not_ge] at h1,
  have h2 : dim α (power_basis α b).range < cardinal.omega, from
    lt_of_le_of_lt (dim_submodule_le _) (finite_dimensional.dim_lt_omega α β),
  -- Since the range has finite dimension, so has the direct sum of the range and kernel
  have h3 : dim α (power_basis α b).range + (dim α (power_basis α b).ker) < cardinal.omega, from
    cardinal.add_lt_omega h2 h1,
  letI : vector_space α (ℕ →₀ α) := vector_space.mk α (ℕ →₀ α), --hint
  have h4 : dim α (ℕ →₀ α) = cardinal.omega, from dim_finsupp_findim α α ℕ,
  rw [dim_range_add_dim_ker, h4] at h3,
  -- We arrive at a contradiction since the domain has infinite dimension
  exact (not_lt.mpr $ le_refl cardinal.omega) h3
end

lemma power_basis.ker_pos : dim α (power_basis α b).ker > 0 :=
lt_of_lt_of_le cardinal.omega_pos $ power_basis.ker_omega α b

instance vhint : vector_space α (ℕ →₀ α) := vector_space.mk α (ℕ →₀ α)
instance ahint : add_comm_group (ℕ →₀ α) := by apply_instance

lemma is_integral_of_aeval_ne_zero (b : β) : is_integral α b ↔
  (∃ p : polynomial α, p ≠ 0 ∧ (polynomial.aeval α β b) p = 0) := sorry

theorem finite_dimensional.integral (b : β) : is_integral α b :=
begin
  cases exists_mem_ne_zero_of_dim_pos (power_basis.ker_pos α b : dim α (power_basis α b).ker > 0) with p hp,
  unfold is_integral,
  rw [test],
  existsi p,
  rwa [linear_map.mem_ker, and_comm] at hp
end

end finite_dimensional
