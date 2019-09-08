import ring_theory.algebra data.matrix
import linear_algebra.finite_dimensional linear_algebra.matrix linear_algebra.determinant
import ring_theory.polynomial ring_theory.integral_closure ring_theory.adjoin
import algebra.big_operators

universes u v w

class field_extension (α : Type u) (β : Type v) [discrete_field α] [discrete_field β] extends algebra α β

namespace field_extension

variables (α : Type u) [discrete_field α]

section

open vector_space

variables (β : Type v) [discrete_field β] [field_extension α β]

lemma dim_ne_zero : dim α β ≠ 0 := sorry

lemma dim_pos : dim α β > 0 := cardinal.pos_iff_ne_zero.mpr (dim_ne_zero α β)

end

section field_norm

open finite_dimensional

section
variables {β : Type v} [discrete_field β] [field_extension α β] [finite_dimensional α β]

private def mul_map (b : β) : β →ₗ[α] β :=
{ to_fun := λ x, b * x,
  add := mul_add b,
  smul := λ a, algebra.mul_smul_comm a b }

lemma mul_map_mul (b c : β) : mul_map α (b * c) = (mul_map α b).comp (mul_map α c) :=
linear_map.ext (λ _, ring.mul_assoc _ _ _)

end

section
variables (β : Type v) [discrete_field β] [field_extension α β] [finite_dimensional α β]

private def fin_basis : set β :=
classical.some $ exists_is_basis_finite α β

noncomputable instance fin_basis_fintype : fintype (fin_basis α β) :=
(classical.some_spec $ exists_is_basis_finite α β).2.fintype

instance fin_basis_decidable_eq : decidable_eq (fin_basis α β) := by apply_instance

lemma fin_basis_is_basis : is_basis α (subtype.val : fin_basis α β → β) :=
(classical.some_spec $ exists_is_basis_finite α β).1

end

variables {β : Type v} [discrete_field β] [field_extension α β] [finite_dimensional α β]

--instance : module α β := by apply_instance
--noncomputable def mul_matrix (b : β) : matrix {x // x ∈ fin_basis α β} {x // x ∈ fin_basis α β} α :=
--@linear_equiv.to_fun α (β →ₗ[α] β) _ _ _ _ linear_map.module matrix.module
--  (lin_equiv_matrix (fin_basis_is_basis α β) (fin_basis_is_basis α β)) (mul_map α b)

noncomputable def mul_matrix (b : β) : matrix {x // x ∈ fin_basis α β} {x // x ∈ fin_basis α β} α :=
by { letI : module α β := algebra.to_module α β,
     letI : module α (β →ₗ[α] β) := linear_map.module,
     letI : module α (matrix {x // x ∈ fin_basis α β} {x // x ∈ fin_basis α β} α) := matrix.module,
     exact (lin_equiv_matrix (fin_basis_is_basis α β) (fin_basis_is_basis α β)).to_fun (mul_map α b) }

lemma mul_matrix_mul (b c : β) : mul_matrix α (b * c) = (mul_matrix α b) * (mul_matrix α c) :=
by { unfold mul_matrix, simp, rw [mul_map_mul, lin_equiv_matrix_comp (fin_basis_is_basis α β) _ _] }

lemma mul_matrix_base (a : α) : mul_matrix α (algebra_map β a) = matrix.diagonal (λ _, a) := sorry

noncomputable def field_norm (b : β) : α := matrix.det $ mul_matrix α b

lemma test (α β γ : Type*) [discrete_field α] [add_comm_group β] [add_comm_group γ]
  [module α β] [module α γ] (e : β ≃ₗ[α] γ) : e.to_fun = e.to_linear_map.to_fun := rfl

@[simp] lemma norm_mul (b c : β) : field_norm α (b * c) = field_norm α b * field_norm α c :=
by { unfold field_norm, rw [mul_matrix_mul, matrix.det_mul] }

@[simp] lemma norm_inv (b : β) : field_norm α b⁻¹ = (field_norm α b)⁻¹ := sorry

@[simp] lemma norm_div (b c : β) : field_norm α (b / c) = field_norm α b / field_norm α c :=
by rw [div_eq_mul_inv, div_eq_mul_inv, ←norm_inv, norm_mul]

lemma norm_base (a : α) : field_norm α (algebra_map β a) = a ^ findim α β :=
begin
unfold field_norm,
rw [mul_matrix_base, matrix.det_diagonal, finset.prod_const, finset.card_univ],
congr,
exact card_eq_findim (fin_basis_is_basis α β)
end

lemma norm_zero : field_norm α (0 : β) = 0 :=
begin
rw [←algebra.map_zero α β, norm_base],
refine zero_pow _,
rw [←cardinal.nat_cast_lt, findim_eq_dim],
exact dim_pos α β
end

lemma norm_zero_iff_zero (b : β) : field_norm α b = 0 ↔ b = 0 :=
⟨sorry, λ h, by rw [h, norm_zero]⟩

lemma norm_one : field_norm α (1 : β) = 1 := by rw [←algebra.map_one α β, norm_base, one_pow]

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

open polynomial ideal ideal.is_principal field_extension

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

lemma ne_zero : minimal_polynomial α hb ≠ 0 :=
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
  exact (ne_zero α hb) hn
end)

lemma aeval_zero_iff_dvd {p : polynomial α} (hp : aeval α β b p = 0) : minimal_polynomial α hb ∣ p :=
begin
rw [←mem_vanishing_ideal_iff, mem_iff_generator_dvd] at hp,
exact (mul_dvd_of_is_unit_right $ is_unit_iff_degree_eq_zero.mpr $ degree_C $ C_ne_zero α hb).mpr hp
end

lemma minimal {p : polynomial α} (hp : p ∈ vanishing_ideal α b) (h0 : p ≠ 0) :
  degree (minimal_polynomial α hb) ≤ degree p :=
begin
rw [mem_vanishing_ideal_iff] at hp,
cases exists_eq_mul_right_of_dvd (aeval_zero_iff_dvd α hb hp) with q h,
have hq : q ≠ 0, from λ hn, by { rw [hn, mul_zero] at h, exact h0 h },
rw [h],
exact degree_le_mul_left _ hq
end

lemma eq_zero_of_degree_lt {p : polynomial α} (hp : p ∈ vanishing_ideal α b)
  (hd : degree p < degree (minimal_polynomial α hb)) : p = 0 :=
classical.by_contradiction (λ hn, not_le_of_lt hd $ minimal α hb hp hn)

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
  have h0q1 : q1 ≠ 0, from λ h, by {rw [h, zero_mul] at hq, exact (ne_zero α hb) hq},
  have hq1 : 0 < (nat_degree q1 : with_bot ℕ),
    { rw [←degree_eq_nat_degree h0q1], exact degree_pos_of_ne_zero_of_nonunit h0q1 hnu.1 },
  have h0q2 : q2 ≠ 0, from λ h, by {rw [h, mul_zero] at hq, exact (ne_zero α hb) hq},
  have hq2 : 0 < (nat_degree q2 : with_bot ℕ),
    { rw [←degree_eq_nat_degree h0q2], exact degree_pos_of_ne_zero_of_nonunit h0q2 hnu.2 },
  rw [←with_bot.coe_zero, with_bot.coe_lt_coe] at hq1 hq2,
  have hq1q : ¬degree (minimal_polynomial α hb) ≤ degree q1, from
    suffices ¬nat_degree (minimal_polynomial α hb) ≤ nat_degree q1,
      by rwa [degree_eq_nat_degree h0q1, degree_eq_nat_degree (ne_zero α hb), with_bot.coe_le_coe],
    (λ h, begin
      rw [hq, nat_degree_mul_eq h0q1 h0q2] at h,
      have : nat_degree q1 > nat_degree q1 + 0, from lt_of_lt_of_le (add_lt_add_left hq2 _) h,
      rw [add_zero] at this,
      exact (not_lt.mpr (le_refl _)) this
    end),
  have hq2q : ¬degree (minimal_polynomial α hb) ≤ degree q2, from
    suffices ¬nat_degree (minimal_polynomial α hb) ≤ nat_degree q2,
      by rwa [degree_eq_nat_degree h0q2, degree_eq_nat_degree (ne_zero α hb), with_bot.coe_le_coe],
    (λ h, begin
      rw [hq, nat_degree_mul_eq h0q1 h0q2] at h,
      have : nat_degree q2 > 0 + nat_degree q2, from lt_of_lt_of_le (add_lt_add_right hq1 _) h,
      rw [zero_add] at this,
      exact (not_lt.mpr (le_refl _)) this
    end),
  have h : eval₂ (algebra_map β) b (minimal_polynomial α hb) = 0, from aeval_zero α hb,
  rw [hq, eval₂_mul] at h,
  cases (integral_domain.eq_zero_or_eq_zero_of_mul_eq_zero _ _ h) with h h,
  { exact hq1q (minimal α hb ((mem_vanishing_ideal_iff α b _).mpr h) h0q1) },
  { exact hq2q (minimal α hb ((mem_vanishing_ideal_iff α b _).mpr h) h0q2) }
end)

lemma degree_unique {p : polynomial α} (h0 : p ≠ 0) (hp : p ∈ vanishing_ideal α b)
  (hmin : ∀ q ∈ vanishing_ideal α b, q ≠ 0 → degree p ≤ degree q) :
  degree (minimal_polynomial α hb) = degree p :=
le_antisymm (minimal α hb hp h0) (hmin _ (mem_vanishing_ideal α hb) (ne_zero α hb))

lemma unique {p : polynomial α} (h0 : p ≠ 0) (hp : p ∈ vanishing_ideal α b) (hm : p.monic)
  (hmin : ∀ q ∈ vanishing_ideal α b, q ≠ 0 → degree p ≤ degree q) :
  minimal_polynomial α hb = p :=
have h1 : minimal_polynomial α hb - p ∈ vanishing_ideal α b, from ideal.sub_mem _ (mem_vanishing_ideal α hb) hp,
have h2 : ¬degree (minimal_polynomial α hb) ≤ degree (minimal_polynomial α hb - p), from
  not_le_of_lt $ degree_sub_lt
    (degree_unique α hb h0 hp hmin) (ne_zero α hb)
    (by rw [monic.def.mp (monic α hb), monic.def.mp hm]),
classical.by_contradiction
  (λ h, absurd (minimal α hb h1 (sub_ne_zero.mpr h)) h2)

lemma congr (h1 h2 : is_integral α b) : minimal_polynomial α h1 = minimal_polynomial α h2 :=
unique α h1 (ne_zero α h2) (mem_vanishing_ideal α h2) (monic α h2) (λ _, minimal α h2)

--TODO: remove finite_dimensional α β
lemma const_eq_norm [finite_dimensional α β] :
  coeff (minimal_polynomial α hb) 0 = (-1) ^ nat_degree (minimal_polynomial α hb) * (field_norm α b) :=
begin
sorry
end

end minimal_polynomial

section adjoin

open polynomial algebra minimal_polynomial vector_space

variables (α : Type u) [discrete_field α]
variables {β : Type v} [discrete_field β] [field_extension α β]
variables (b : β) (hb : is_integral α b)

lemma pow_mem_iff (s : subalgebra α β) (n : ℕ) : b^n ∈ s ↔ b ∈ s := sorry

lemma pow_mem_adjoin (n : ℕ) : b^n ∈ (adjoin α {b} : subalgebra α β) :=
by { rw [pow_mem_iff, ←subalgebra.mem_coe, ←set.singleton_subset_iff],
  exact subset_adjoin }

instance hint1 : module α β := by apply_instance
instance hint2 : comm_ring α := by apply_instance

#check @finsupp.sum_map_range_index
#check @finsupp.sum_comap_domain
#check @finsupp.sum_subtype_domain_index
#check @finsupp.subtype_domain
#check subtype_val.is_add_monoid_hom

#check pow_mem_adjoin
--set_option pp.implicit true

#check @finsupp.map_domain
#check @finsupp.map_domain_sum
#check @finsupp.sum_map_domain_index
#check div_by_monic

#check finsupp.comap_domain

--set_option pp.notation false
--set_option pp.implicit true
--set_option pp.all true

lemma basis_adjoin : @is_basis (fin $ nat_degree $ minimal_polynomial α hb) α (adjoin α {b} : subalgebra α β)
  (λ i, subtype.mk (b^i.val) (pow_mem_adjoin α b i.val)) _ _ (by apply_instance) _ _ _ :=
begin
  split,
  { rw [linear_independent_iff],
    assume f hf,
    rw [finsupp.total_apply] at hf,
    replace hf := congr_arg subtype.val hf,
    unfold finsupp.sum at hf,
    rw [←finset.sum_hom (subtype.val : _ → β)] at hf,
    { conv_lhs at hf { congr, skip, funext, rw [algebra.smul_def, algebra_map] },
      unfold algebra.to_fun at hf,
      conv_lhs at hf { congr, skip, funext, rw [subtype_val.is_monoid_hom.map_mul], dsimp },
      change f.sum (λ i a, algebra_map β a * b^i.val) = 0 at hf,
      have : ∀ j:ℕ, (λ (i:ℕ) (a:α), algebra_map β a * b^i) j 0 = 0,
        { intro _, dsimp, rw [algebra.map_zero, zero_mul] },
      rw [←finsupp.sum_map_domain_index this] at hf,
      { let v := @fin.val (nat_degree $ minimal_polynomial α hb),
        let p := f.map_domain v,
        have hpv : p ∈ vanishing_ideal α b, by rwa [mem_vanishing_ideal_iff],
        have hpd : degree p < degree (minimal_polynomial α hb), from sorry,
        have hp : p = 0, from minimal_polynomial.eq_zero_of_degree_lt α hb hpv hpd,
        have h : p = (finsupp.map_domain v) 0, { rwa [hp, finsupp.map_domain_zero] },
        rwa [function.injective.eq_iff (finsupp.injective_map_domain _)] at h,
        exact λ x y, (fin.ext_iff x y).mpr },
      { assume _ _ _, simp only [algebra.map_add, add_mul] } },
      { sorry } },
    { rw [submodule.eq_top_iff'],
      intro g,
      rw [←set.image_univ, finsupp.mem_span_iff_total],
      have hg : g.val ∈ (aeval α β b).range,
        { convert g.property, symmetry, exact adjoin_singleton_eq_range α b },
      cases set.mem_range.mp hg with l hl,
      --let p := l %ₘ (minimal_polynomial α hb),
      have hp : aeval α β b (l %ₘ minimal_polynomial α hb) = g.val,
        { rwa [mod_by_monic_eq_sub_mul_div _ (monic α hb), (aeval α β b).map_sub,
            (aeval α β b).map_mul, aeval_zero, zero_mul, sub_zero] },
      have hd : degree (l %ₘ minimal_polynomial α hb) < degree (minimal_polynomial α hb), from
        degree_mod_by_monic_lt _ (monic α hb) (ne_zero α hb),
      have hs : (l %ₘ minimal_polynomial α hb).support.to_set ⊆ {n | n < nat_degree (minimal_polynomial α hb)},
        { rw [set.subset_def],
          assume n,
          rw [finset.to_set, finset.set_of_mem, finset.mem_coe, finsupp.mem_support_to_fun,
            set.mem_set_of_eq, ←with_bot.coe_lt_coe, ←degree_eq_nat_degree (ne_zero α hb)],
          assume hn,
          refine lt_of_le_of_lt (le_of_not_lt _) hd,
          revert hn,
          contrapose,
          rw [ne.def, not_not, not_not],
          exact coeff_eq_zero_of_degree_lt },
      have hv : set.bij_on fin.val (fin.val ⁻¹' (l %ₘ minimal_polynomial α hb).support.to_set)
        ((l %ₘ minimal_polynomial α hb).support.to_set),
        { sorry },--{ assume _ _ _ _ _, rwa [fin.ext_iff] },
      rw [finsupp.supported_univ],
      existsi [(l %ₘ minimal_polynomial α hb).comap_domain fin.val (set.inj_on_of_bij_on hv), submodule.mem_top],
      rw [finsupp.total_apply],
      --change ((l %ₘ minimal_polynomial α hb).comap_domain fin.val _).sum (λ i, (λ a, _)) = g,
      --change ((l %ₘ minimal_polynomial α hb).comap_domain fin.val _).sum
      --  (λ j c, ((λ (i:ℕ), (λ (a:α), _)) ∘ (@fin.val (nat_degree (minimal_polynomial α hb)))) j c) = g,
      --conv_lhs { congr, skip, funext,
      --  rw [show a • subtype.mk (b^i.val) (pow_mem_adjoin α b i.val) = (λ j c, c • subtype.mk (b^j.val) (pow_mem_adjoin α b j.val)) i a,
      --    begin dsimp, end], }
      convert finsupp.sum_comap_domain _ _ (λ (i:ℕ) (a:α), a • _) hv,


    }
end

lemma dim_adjoin : dim α (adjoin α {b} : subalgebra α β) = nat_degree (minimal_polynomial α hb) :=
calc dim α (adjoin α {b} : subalgebra α β)
      = cardinal.lift.{v 0} (dim α (adjoin α {b} : subalgebra α β)) : by rw [cardinal.lift_id']
  ... = cardinal.lift.{0 v} (cardinal.mk $ fin $ nat_degree $ minimal_polynomial α hb) :
    eq.symm (is_basis.mk_eq_dim $ basis_adjoin α b hb)
  ... = ↑(nat_degree $ minimal_polynomial α hb) : cardinal.lift_mk_fin _

end adjoin


section finite_dimensional

open vector_space

--TODO: universe issue with cardinals
variables (α : Type u) [discrete_field α]
variables {β : Type u} [discrete_field β] [field_extension α β] [finite_dimensional α β]
variables (b : β)
#check @finsupp.sum_map_domain_index
lemma sum_single_range {α β γ : Type*} [decidable_eq α] [has_zero β] [add_comm_monoid γ] [decidable_eq γ]
  (f : α →₀ β) (g : β → γ) (hg : g 0 = 0) :
  finsupp.sum f (λ (a : α) (b : β), finsupp.single a (g b)) =
  finsupp.map_range g hg f :=
by { rw [←finsupp.sum_map_range_index, finsupp.sum_single], intro _, exact finsupp.single_zero }

lemma sum_single3 {α β γ δ : Type*} [decidable_eq α] [decidable_eq β] [add_comm_monoid β]
  [add_comm_monoid γ] [decidable_eq γ] [decidable_eq δ]
  (f : α →₀ β) (g : α → β → γ) (i : δ) :
  finsupp.sum f (λ (a : α) (b : β), finsupp.single i (g a b)) =
  finsupp.single i (f.sum g) :=
begin
ext j,
rw [finsupp.single_apply, finsupp.sum_apply],
conv_lhs { congr, skip, funext, rw [finsupp.single_apply] },
split_ifs,
refl,
exact finsupp.sum_zero
end

lemma sum_single2 {α β γ : Type*} [decidable_eq α] [has_zero β] [add_comm_monoid γ] [decidable_eq γ]
  (f : α →₀ β) (g : α → β → γ) (hg : ∀ a : α, g a 0 = 0) (a : α) :
  finsupp.sum f (λ (a₂ : α) (b : β), (finsupp.single a (g a b)).to_fun a₂) =
  g a (f a) :=
suffices finsupp.sum f (λ (a₂ : α) (b : β), ite (a = a₂) (g a b) 0) =
  (finset.singleton a).sum (λ (a₂ : α), ite (a = a₂) (g a (f a₂)) 0),
  by { convert this, rw [finset.sum_singleton, if_pos rfl] },
begin
  unfold finsupp.sum,
  by_cases ha : a ∈ f.support,
  { refine (finset.sum_subset _ _).symm,
    { assume x hx, rw [finset.mem_singleton] at hx, rwa [hx] },
    { assume x _ hx, rw [finset.not_mem_singleton] at hx, rw [if_neg], exact ne.symm hx } },
  { convert (rfl : (0:γ) = 0),
    { apply finset.sum_eq_zero,
      intros j hj,
      apply if_neg,
      intro h,
      exact ha (eq.symm h ▸ hj) },
    { apply finset.sum_eq_zero,
      intros j hj,
      rw [finset.mem_singleton] at hj,
      rw [if_pos (eq.symm hj)],
      convert hg a,
      have h : ¬(f j ≠ 0), from mt (finsupp.mem_support_to_fun f j).mpr ((eq.symm hj) ▸ ha),
      rwa [ne.def, classical.not_not] at h } }
end

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
  rw [show (ite (a₁.fst = x) (finsupp.single (a₁.snd) b) 0).to_fun y = ite (a₁ = (x, y)) b 0,
    { split_ifs with hx h,
      { rwa [show (finsupp.single _ _).to_fun _ = _, from finsupp.single_apply, h, if_pos rfl] },
      { rw [show (finsupp.single _ _).to_fun _ = _, from finsupp.single_apply],
        rw [show a₁ = (a₁.fst, a₁.snd), from eq.symm prod.mk.eta, ←hx, prod.mk.inj_iff, not_and] at h,
        rwa [if_neg (h rfl)] },
      { rw [show a₁ = (a₁.fst, a₁.snd), from eq.symm prod.mk.eta, prod.mk.inj_iff] at h, exact false.elim (hx h.1) },
      { refl } }] },
refine sum_ite f (λ _ b, b) _ _,
intro _, refl
end

/-lemma finsupp_basis (η : Type*) {ι α β : Type*} [ring α] [decidable_eq α] [add_comm_group β] [module α β]
  [decidable_eq η] [decidable_eq β] [decidable_eq ι] {v : ι → β} (hv : is_basis α v) :
  is_basis α (λ i : η × ι, finsupp.single i.1 (v i.2)) :=
begin
  split,
  { rw [linear_independent_iff],
    intros f hf,
    ext i,
    rw [finsupp.total_apply, finsupp.ext_iff] at hf,
    replace hf := hf i.1,
    rw [finsupp.sum_apply] at hf,
    conv_lhs at hf { congr, skip, funext, rw [finsupp.smul_single, finsupp.single_apply] },
    rw [←finsupp.sum_curry_index f (λ (n:η) (j:ι) (b:α), ite (n = i.1) (b • v j) 0)] at hf,
    { dsimp at hf,
      conv_lhs at hf { congr, skip, funext,
        rw [show (f.sum (λ (j:ι) (b:α), ite (a = i.1) (b • v j) 0)) =
          ite (a = i.1) (f.sum (λ (j:ι) (b:α), b • v j)) 0,
          { split_ifs, refl, exact finsupp.sum_zero }]},
      rw [sum_ite _ (λ (a:η) (g : ι →₀ α), g.sum (λ (j:ι) (b:α), b • v j)) (λ _, finsupp.sum_zero_index)] at hf,
      dsimp at hf,
      have h4 : ((finsupp.curry f) (i.fst)) (i.snd) = 0, { rw [linear_independent_iff.mp hv.1 _ hf], refl },
      rwa [finsupp.curry_apply, prod.mk.eta] at h4 },
    { intros _ _, simp only [zero_smul, if_t_t] },
    { intros _ _ _ _, dsimp, split_ifs, rw [add_smul], rw [add_zero] } },
  { rw [submodule.eq_top_iff'],
    intro g,
    rw [←set.image_univ, finsupp.mem_span_iff_total],
    let f := finsupp.uncurry (finsupp.map_range hv.repr.to_fun hv.repr.map_zero g),
    have H : f ∈ finsupp.supported α α (set.univ : set (η × ι)),
      { rw [finsupp.supported_univ], exact submodule.mem_top },
    existsi [f, H],
    rw [finsupp.total_apply],
    ext n,
    rw [finsupp.sum_apply],
    conv_lhs { congr, skip, funext, rw [finsupp.smul_single, finsupp.single_apply] },
    rw [←finsupp.sum_curry_index f (λ (m:η) (i:ι) (b:α), ite (m = n) (b • v i) 0)],
    { have : finsupp.curry f = finsupp.map_range hv.repr.to_fun hv.repr.map_zero g, from
        finsupp.finsupp_prod_equiv.right_inv _,
      rw [this, finsupp.sum_map_range_index],
      dsimp,
      conv_lhs { congr, skip, funext,
        rw [show (hv.repr.to_fun b).sum (λ (i:ι) (b:α), ite (a = n) (b • v i) 0) =
          ite (a = n) (((finsupp.total ι β α v).comp hv.repr) b) 0,
          { rw [linear_map.comp_apply, finsupp.total_apply], split_ifs, refl, exact finsupp.sum_zero }],
        rw [hv.total_comp_repr, linear_map.id_apply] },
      { rw [sum_ite], intro _, refl },
      { intro _, exact finsupp.sum_zero_index } },
    { intros _ _, simp only [zero_smul, if_t_t] },
    { intros _ _ _ _, dsimp, split_ifs, rw [add_smul], rw [add_zero] } }
end-/

lemma finsupp_basis (η : Type*) {ι α β : Type*} [ring α] [decidable_eq α] [add_comm_group β] [module α β]
  [decidable_eq η] [decidable_eq β] [decidable_eq ι] {v : ι → β} (hv : is_basis α v) :
  is_basis α (λ i : η × ι, finsupp.single i.1 (v i.2)) :=
begin
  have h : ∀ (f : η × ι →₀ α) (g : η →₀ β), (finsupp.total (η × ι) (η →₀ β) α (λ (i : η × ι), finsupp.single i.1 (v i.2))) f = g ↔
    ∀ n, (finsupp.total ι β α v) (finsupp.curry f n) = g n,
    { intros f g,
      rw [finsupp.total_apply],
      conv_lhs { congr, congr, skip, funext, rw [finsupp.smul_single] },
      rw [←finsupp.sum_curry_index f (λ (n:η) (i:ι) (a:α), finsupp.single n (a • v i))],
      { dsimp,
        conv_lhs { congr, congr, skip, funext, rw [sum_single3] },
        rw [sum_single_range _ (λ f:ι →₀ α, finsupp.sum f (λ (i:ι) (a:α), a • v i)) finsupp.sum_zero_index],
        rw [finsupp.ext_iff],
        split,
        { intros h n, replace h := h n, rwa [finsupp.map_range_apply, ←finsupp.total_apply] at h },
        { intros h n, replace h := h n, rwa [finsupp.map_range_apply, ←finsupp.total_apply] } },
      { intros _ _, dsimp, rw [zero_smul, finsupp.single_zero] },
      { intros _ _ _ _, dsimp, rw [add_smul, finsupp.single_add] } },
  split,
  { rw [linear_independent_iff],
    intros f hf,
    ext i,
    rw [h] at hf,
    have : _ = _, from congr_arg (λ g:ι →₀ α, g i.2) (linear_independent_iff.mp hv.1 _ (hf i.1)),
    rwa [finsupp.curry_apply, prod.mk.eta] at this },
  { rw [submodule.eq_top_iff'],
    intro g,
    rw [←set.image_univ, finsupp.mem_span_iff_total],
    let f := finsupp.uncurry (finsupp.map_range hv.repr.to_fun hv.repr.map_zero g),
    have H : f ∈ finsupp.supported α α (set.univ : set (η × ι)),
      { rw [finsupp.supported_univ], exact submodule.mem_top },
    existsi [f, H],
    rw [h],
    intro n,
    rw [show finsupp.curry f = _, from finsupp.finsupp_prod_equiv.right_inv _, finsupp.map_range_apply],
    change (linear_map.comp (finsupp.total ι β α v) (is_basis.repr hv)) (g n) = g n,
    rw [hv.total_comp_repr, linear_map.id_apply] },
end

/-lemma finsupp_basis (η : Type*) {ι α β : Type*} [ring α] [decidable_eq α] [add_comm_group β] [module α β]
  [decidable_eq η] [decidable_eq β] [decidable_eq ι] {v : ι → β} (hv : is_basis α v) :
  is_basis α (λ i : η × ι, finsupp.single i.1 (v i.2)) :=
begin
  split,
  { rw [linear_independent_iff],
    intros f hf,
    rw [finsupp.total_apply] at hf,
    conv_lhs at hf { congr, skip, funext, rw [finsupp.smul_single] },
    rw [←finsupp.sum_curry_index f (λ (n:η) (i:ι) (a:α), finsupp.single n (a • v i))] at hf,
    { dsimp at hf,
      conv_lhs at hf { congr, skip, funext, rw [sum_single3] },
      rw [sum_single_range _ (λ f:ι →₀ α, finsupp.sum f (λ (i:ι) (a:α), a • v i)) finsupp.sum_zero_index] at hf,
      rw [finsupp.ext_iff] at hf,
      ext i,
      replace hf := hf i.1,
      rw [finsupp.map_range_apply, ←finsupp.total_apply] at hf,
      dsimp at ⊢ hf,
      have h : _ = _, from congr_arg (λ g:ι →₀ α, g i.2) (linear_independent_iff.mp hv.1 _ hf),
      rwa [finsupp.curry_apply, prod.mk.eta] at h },
    { intros _ _, dsimp, rw [zero_smul, finsupp.single_zero] },
    { intros _ _ _ _, dsimp, rw [add_smul, finsupp.single_add] } },
  { rw [submodule.eq_top_iff'],
    intro g,
    rw [←set.image_univ, finsupp.mem_span_iff_total],
    let f := finsupp.uncurry (finsupp.map_range hv.repr.to_fun hv.repr.map_zero g),
    have H : f ∈ finsupp.supported α α (set.univ : set (η × ι)),
      { rw [finsupp.supported_univ], exact submodule.mem_top },
    existsi [f, H],
    rw [finsupp.total_apply],
    conv_lhs { congr, skip, funext, rw [finsupp.smul_single] },
    rw [←finsupp.sum_curry_index f (λ (n:η) (i:ι) (a:α), finsupp.single n (a • v i))],
    { dsimp,
      conv_lhs { congr, skip, funext, rw [sum_single3] },
      rw [sum_single_range _ (λ f:ι →₀ α, finsupp.sum f (λ (i:ι) (a:α), a • v i)) finsupp.sum_zero_index],
      ext n,
      have : finsupp.curry f = finsupp.map_range hv.repr.to_fun hv.repr.map_zero g, from
        finsupp.finsupp_prod_equiv.right_inv _,
      rw [finsupp.map_range_apply, ←finsupp.total_apply, this, finsupp.map_range_apply],
      change (linear_map.comp (finsupp.total ι β α v) (is_basis.repr hv)) (g n) = g n,
      rw [hv.total_comp_repr, linear_map.id_apply] },
    { intros _ _, dsimp, rw [zero_smul, finsupp.single_zero] },
    { intros _ _ _ _, dsimp, rw [add_smul, finsupp.single_add] } }
end-/

-- move
/-lemma finsupp_basis (α : Type*) (ι : Type*) [discrete_field α] [decidable_eq ι] :
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
-/

--TODO: set priorities correct to avoid these instances
instance mf : module α (ℕ →₀ α) := finsupp.module ℕ α
instance ms (p : submodule α (ℕ →₀ α)) : module α p := submodule.module p
instance vs (p : submodule α (ℕ →₀ α)) : vector_space α p := vector_space.mk α p

-- move
lemma dim_finsupp (α : Type u) (β : Type w) (η : Type v) [discrete_field α] [discrete_field β]
  [decidable_eq η] [algebra α β] :
  dim α (η →₀ β) = cardinal.lift.{v w} (cardinal.mk η) * cardinal.lift.{w v} (dim α β) :=
let ⟨b, hb⟩ := exists_is_basis α β in
have h : is_basis α (λ i : η × b, _), from finsupp_basis η hb,
calc dim α (η →₀ β) = cardinal.lift.{(max v w) (max v w)} (dim α (η →₀ β))      : eq.symm $ cardinal.lift_id _
                ... = cardinal.lift.{(max v w) (max v w)} (cardinal.mk (η × b)) : eq.symm $ h.mk_eq_dim
                ... = cardinal.lift.{(max v w) (max v w)} (cardinal.lift.{v w} (cardinal.mk η) * cardinal.lift.{w v} (cardinal.mk b)) : by rw [cardinal.mk_prod]
                ... = cardinal.lift.{v w} (cardinal.mk η) * cardinal.lift.{w (max w v)} (cardinal.mk.{w} b) : by rw[cardinal.lift_mul, cardinal.lift_lift, cardinal.lift_lift, cardinal.lift_umax]
                ... = cardinal.lift.{v w} (cardinal.mk η) * cardinal.lift.{w v} (cardinal.lift.{w w} (cardinal.mk.{w} b)) : by rw [cardinal.lift_id, cardinal.lift_umax]
                ... = cardinal.lift.{v w} (cardinal.mk η) * cardinal.lift.{w v} (dim α β) : by rw [hb.mk_eq_dim, cardinal.lift_id]

def power_basis : (ℕ →₀ α) →ₗ[α] β :=
{ to_fun := λ f, finsupp.sum f (λ i a, algebra_map β a * b ^ i),
  add := λ f g, begin refine finsupp.sum_add_index _ _,
      { intro, rw [algebra.map_zero, zero_mul] },
      { intros, rw [algebra.map_add, add_mul] } end,
  smul := λ f g, begin
      rw [finsupp.sum_smul_index, finsupp.smul_sum],
      conv_rhs { congr, skip, funext, rw [algebra.smul_def, ←mul_assoc, ←algebra.map_mul] },
      { intro, rw [algebra.map_zero, zero_mul] } end }

lemma power_basis.dim_ker_ge_omega : dim α (power_basis α b).ker ≥ cardinal.omega :=
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
  have h4 : dim α (ℕ →₀ α) = cardinal.omega, from --dim_finsupp_findim α α ℕ,
    by { convert dim_finsupp α α ℕ, rw [dim_of_field, cardinal.lift_one, mul_one], refl },
  rw [dim_range_add_dim_ker, h4] at h3,
  -- We arrive at a contradiction since the domain has infinite dimension
  exact (not_lt.mpr $ le_refl cardinal.omega) h3
end

lemma power_basis.ker_pos : dim α (power_basis α b).ker > 0 :=
lt_of_lt_of_le cardinal.omega_pos $ power_basis.dim_ker_ge_omega α b

lemma is_integral_of_aeval_ne_zero (b : β) : is_integral α b ↔
  (∃ p : polynomial α, p ≠ 0 ∧ (polynomial.aeval α β b) p = 0) := sorry

instance vhint : vector_space α (ℕ →₀ α) := vector_space.mk α (ℕ →₀ α)
open polynomial

theorem finite_dimensional.integral (b : β) : is_integral α b :=
begin
  cases exists_mem_ne_zero_of_dim_pos (power_basis.ker_pos α b : dim α (power_basis α b).ker > 0) with p hp,
  unfold is_integral,
  existsi p * C (leading_coeff p)⁻¹,
  split,
  { exact monic_mul_leading_coeff_inv hp.2 },
  { rw [linear_map.mem_ker, and_comm] at hp,
    rw [(aeval α β b).map_mul],
    convert zero_mul _,
    exact hp.2 }
end

end finite_dimensional
