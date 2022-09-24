import order.upper_lower
import algebra.big_operators.ring
import probability.density
import probability.independence
import probability.conditional_expectation
import probability.notation

open finset set measure_theory probability_theory
open_locale big_operators measure_theory ennreal

variables {X : Type*} [fintype X]
variables {Ω : Type*}
variable {F : finset (finset X)}

section to_mathlib

  lemma finset.top_eq_univ : (⊤ : finset X) = univ := rfl
  lemma finset.compl_eq_empty_iff (A : finset X) [decidable_eq X] : Aᶜ = ∅ ↔ A = univ := compl_eq_bot
  lemma finset.compl_eq_univ_iff (A : finset X) [decidable_eq X] : Aᶜ = univ ↔ A = ∅ := compl_eq_top

  lemma ennreal.of_real_sub' (p : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    ennreal.of_real (p - q) = ennreal.of_real p - ennreal.of_real q :=
  begin
    obtain h | h := le_total p q,
    { rw [ennreal.of_real_of_nonpos (sub_nonpos_of_le h), tsub_eq_zero_of_le (ennreal.of_real_le_of_real h)] },
    refine ennreal.eq_sub_of_add_eq ennreal.of_real_ne_top _,
    rw [←ennreal.of_real_add (sub_nonneg_of_le h) hq, sub_add_cancel],
  end

  lemma set.pi_bInter {α β γ : Type*} (s : set α) (t : set β) (f : α → β → set γ) :
    (⋂ i ∈ s, t.pi (f i)) = t.pi (λ j, ⋂ i ∈ s, f i j) :=
  begin
    ext z,
    simp only [set.mem_Inter, set.mem_pi],
    rw forall₂_swap,
  end
end to_mathlib

section pure_probability

  variables [measurable_space Ω] {E : Type*} [measurable_space E]

  lemma prob_ne_inf {ℙ : measure Ω} [is_probability_measure ℙ] (A : set Ω) : ℙ A ≠ ∞ :=
  ne_top_of_le_ne_top ennreal.one_ne_top prob_le_one

  lemma measure_theory.pdf.is_uniform.measurable
    {ℙ : measure Ω} {X : Ω → E} {s : set E} {μ : measure E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞)
    (huX : pdf.is_uniform X s ℙ μ) :
    measurable X :=
  @has_pdf.measurable _ _ _ _ _ _ _ (huX.has_pdf hns hnt)

  lemma measure_theory.pdf.is_uniform.Icc_measurable
    {ℙ : measure Ω} {X : Ω → ℝ} {a b : ℝ} (h : a < b) (huX : pdf.is_uniform X (set.Icc a b) ℙ) :
    measurable X :=
  huX.measurable (by simp [h]) (by simp)

  lemma measure_theory.pdf.is_uniform.Icc_is_probability_measure
    {ℙ : measure Ω} {X : Ω → ℝ} {a b : ℝ} (h : a < b)
    (huX : pdf.is_uniform X (set.Icc a b) ℙ) :
    is_probability_measure ℙ :=
  huX.is_probability_measure (by simp [h]) (by simp) (by simp)

  lemma prob_eq_exp {ℙ : measure Ω} {a : set Ω} (ha : measurable_set a) :
    ∫ ω, a.indicator 1 ω ∂ℙ = (ℙ a).to_real :=
  (integral_indicator_const (1 : ℝ) ha).trans (by simp)

end pure_probability

section pure_combi

  def product_measure [decidable_eq X] (A : finset X) (p : ℝ) : ℝ := p ^ A.card * (1 - p) ^ Aᶜ.card

  lemma product_measure_nonneg [decidable_eq X] {A : finset X} {p : ℝ} (hp : p ∈ set.Icc (0 : ℝ) 1) :
    0 ≤ product_measure A p :=
  mul_nonneg (pow_nonneg hp.1 _) (pow_nonneg (sub_nonneg_of_le hp.2) _)

  lemma product_measure_zero [decidable_eq X] (A : finset X) :
    product_measure A 0 = ite (A = ∅) 1 0 :=
  by simp [product_measure, zero_pow_eq]

  lemma product_measure_empty_zero [decidable_eq X] : product_measure (∅ : finset X) 0 = 1 :=
  by simp [product_measure_zero]

  lemma product_measure_nonempty_zero [decidable_eq X] {A : finset X} (hA : A.nonempty) :
    product_measure A 0 = 0 :=
  by simp [product_measure_zero, hA.ne_empty]

  lemma product_measure_one [decidable_eq X] (A : finset X) :
    product_measure A 1 = ite (A = univ) 1 0 :=
  by simp [product_measure, zero_pow_eq, finset.compl_eq_empty_iff]

  lemma product_measure_univ_one [decidable_eq X] : product_measure (univ : finset X) 1 = 1 :=
  by simp [product_measure_one]

  def product_family_measure [decidable_eq X] (F : finset (finset X)) (p : ℝ) : ℝ :=
    ∑ A in F, product_measure A p

  lemma product_family_measure_mono [decidable_eq X]
    {F₁ F₂ : finset (finset X)} (h : F₁ ⊆ F₂) {p : ℝ} (hp : p ∈ set.Icc (0 : ℝ) 1):
    product_family_measure F₁ p ≤ product_family_measure F₂ p :=
  sum_le_sum_of_subset_of_nonneg h (λ _ _ _, product_measure_nonneg hp)

  lemma product_family_measure_zero [decidable_eq X] (F : finset (finset X)) :
    product_family_measure F 0 = ite (∅ ∈ F) 1 0 :=
  by simp only [product_family_measure, product_measure_zero, sum_ite_eq']

  lemma product_family_measure_one [decidable_eq X] (F : finset (finset X)) :
    product_family_measure F 1 = ite (finset.univ ∈ F) 1 0 :=
  by simp only [product_family_measure, product_measure_one, sum_ite_eq']

  lemma product_family_measure_zero' [decidable_eq X] {F : finset (finset X)}
    (hF : is_upper_set (F : set (finset X))) (hF' : F ≠ univ) :
    product_family_measure F 0 = 0 :=
  begin
    rw [product_family_measure_zero, ←finset.bot_eq_empty, if_neg],
    rwa [←finset.mem_coe, hF.bot_mem, coe_eq_univ],
  end

  lemma product_family_measure_one' [decidable_eq X] {F : finset (finset X)}
    (hF : is_upper_set (F : set (finset X))) (hF' : F.nonempty) :
    product_family_measure F 1 = 1 :=
  by { rw [product_family_measure_one, ←finset.top_eq_univ, if_pos],
      rwa [←finset.mem_coe, hF.top_mem, coe_nonempty] }

  @[simp] lemma product_family_measure_empty [decidable_eq X] (p : ℝ) :
    product_family_measure (∅ : finset (finset X)) p = 0 :=
  by simp only [product_family_measure, sum_empty]

  @[simp] lemma product_family_measure_univ [decidable_eq X] (p : ℝ) :
    product_family_measure (univ : finset (finset X)) p = 1 :=
  begin
    rw [product_family_measure],
    convert sum_pow_mul_eq_add_pow p (1 - p) (univ : finset X),
    { simp only [product_measure, card_compl, card_univ] },
    simp only [add_sub_cancel'_right, one_pow],
  end

end pure_combi

noncomputable def choices {Ω : Type*} (a : X → Ω → ℝ) (p : ℝ) (ω : Ω) : finset X :=
finset.univ.filter (λ x, a x ω ≤ p)

noncomputable def product_measure' [decidable_eq X] (A : finset X) : polynomial ℤ :=
  polynomial.X ^ A.card * (1 - polynomial.X) ^ Aᶜ.card

noncomputable def product_family_measure' [decidable_eq X] (F : finset (finset X)) : polynomial ℤ :=
  ∑ A in F, product_measure' A

lemma eval_product_measure' [decidable_eq X] {A : finset X} (p : ℝ) :
  (product_measure' A).eval₂ (int.cast_ring_hom ℝ) p = product_measure A p :=
begin
  rw [product_measure', product_measure],
  simp only [polynomial.eval₂_mul, polynomial.eval₂_X, polynomial.eval₂_pow,
    polynomial.eval₂_sub, polynomial.eval₂_one],
end

lemma eval_product_family_measure' [decidable_eq X] {F : finset (finset X)} (p : ℝ) :
  (product_family_measure' F).eval₂ (int.cast_ring_hom ℝ) p = product_family_measure F p :=
begin
  simp only [product_family_measure', polynomial.eval₂_finset_sum],
  apply sum_congr rfl,
  simp [eval_product_measure'],
end

lemma choices_eq_set_eq [decidable_eq X] {a : X → Ω → ℝ} {p : ℝ} (A : finset X) :
  {ω | choices a p ω = A} =
    ⋂ (x : X) (_ : x ∈ (univ : finset X)), if x ∈ A then {ω | a x ω ≤ p} else {ω | p < a x ω} :=
begin
  ext ω,
  simp only [finset.ext_iff, set.mem_Inter],
  refine forall_congr (λ i, _),
  split_ifs;
  simp [choices, h],
end

lemma choices_mem_eq {a : X → Ω → ℝ} {p : ℝ} :
  {ω : Ω | choices a p ω ∈ F} = ⋃ A ∈ F, {ω | choices a p ω = A} :=
begin
  ext ω,
  simp only [set.mem_set_of_eq, set.mem_Union, exists_prop, exists_eq_right'],
end

lemma subset_choices_eq {p : ℝ} {a : X → Ω → ℝ} {S : finset X} :
  {ω | S ⊆ choices a p ω} = ⋂ x ∈ S, {ω | a x ω ≤ p} :=
by { ext ω, simp only [mem_set_of_eq, mem_Inter, choices, finset.subset_iff, mem_filter,
  finset.mem_univ, true_and] }

lemma count_copies_eq [decidable_eq X] {a : X → Ω → ℝ} {p : ℝ}
  {G : finset (finset X)} (ω : Ω) :
  ((G.filter (λ S, S ⊆ choices a p ω)).card : ℝ) =
    ∑ S in G, {ω | S ⊆ choices a p ω}.indicator 1 ω :=
begin
  simp only [finset.card_eq_sum_ones, nat.cast_sum, set.indicator_apply,
    set.mem_set_of_eq, nat.cast_one, ←sum_filter, pi.one_apply],
end

variable [measurable_space Ω]

lemma measurable_set_choices_eq {ℙ : measure Ω} {a : X → Ω → ℝ} {p : ℝ} (A : finset X)
  (ha : ∀ i, pdf.is_uniform (a i) (set.Icc 0 1) ℙ) :
  measurable_set {ω | choices a p ω = A} :=
begin
  classical,
  rw choices_eq_set_eq,
  apply measurable_set_bInter,
  intros i hi,
  split_ifs,
  { apply (ha _).Icc_measurable zero_lt_one measurable_set_Iic },
  { apply (ha _).Icc_measurable zero_lt_one measurable_set_Ioi },
end


lemma measurable_set_choices_mem {ℙ : measure Ω} {a : X → Ω → ℝ} {p : ℝ}
  (ha : ∀ i, pdf.is_uniform (a i) (set.Icc 0 1) ℙ) :
  measurable_set {ω : Ω | choices a p ω ∈ F} :=
begin
  rw [choices_mem_eq],
  apply measurable_set_bUnion,
  intros A hA,
  exact measurable_set_choices_eq _ ha,
end

lemma measurable_set_subset_choices {ℙ : measure Ω} {a : X → Ω → ℝ} {p : ℝ} {S : finset X}
  (ha : ∀ i, pdf.is_uniform (a i) (set.Icc 0 1) ℙ) :
  measurable_set {ω | S ⊆ choices a p ω} :=
begin
  rw subset_choices_eq,
  refine measurable_set_bInter _ (λ i hi, _),
  exact (ha _).Icc_measurable zero_lt_one measurable_set_Iic
end


lemma integrable_count_copies [decidable_eq X] [nonempty X] {ℙ : measure Ω} {a : X → Ω → ℝ} {p : ℝ}
  (ha : ∀ i, pdf.is_uniform (a i) (set.Icc 0 1) ℙ)
  {G : finset (finset X)} :
  integrable (λ ω, ((G.filter (λ S, S ⊆ choices a p ω)).card : ℝ)) ℙ :=
begin
  inhabit X,
  haveI := (ha default).Icc_is_probability_measure zero_lt_one,
  simp only [count_copies_eq],
  apply integrable_finset_sum,
  intros i hi,
  exact (integrable_const 1).indicator (measurable_set_subset_choices ha),
end

lemma prob_uniform_le {ℙ : measure Ω} {a : Ω → ℝ} {p : ℝ} (hp : p ∈ set.Icc (0 : ℝ) 1)
  (ha : pdf.is_uniform a (set.Icc 0 1) ℙ) :
  ennreal.to_real (ℙ {ω | a ω ≤ p}) = p :=
begin
  have h' : {ω | a ω ≤ p} = a ⁻¹' set.Iic p, { refl },
  have h'' : set.Icc 0 1 ∩ set.Iic p = set.Icc 0 p,
  { ext q, exact and_congr_left (λ h₁, and_iff_left (hp.2.trans' h₁)) },
  rw [h', ha.measure_preimage _ _ measurable_set_Icc measurable_set_Iic];
  simp [h'', ennreal.to_real_of_real hp.1],
end

lemma prob_lt_uniform {ℙ : measure Ω} {a : Ω → ℝ} {p : ℝ} (hp : p ∈ set.Icc (0 : ℝ) 1)
  (ha : pdf.is_uniform a (set.Icc 0 1) ℙ) :
  ennreal.to_real (ℙ {ω | p < a ω}) = 1 - p :=
begin
  have h' : {ω | p < a ω} = a ⁻¹' set.Ioi p, { refl },
  have h'' : set.Icc 0 1 ∩ set.Ioi p = set.Ioc p 1,
  { ext q, simpa [and_comm] using λ h₁ h₂, hp.1.trans (le_of_lt h₁) },
  rw [h', ha.measure_preimage _ _ measurable_set_Icc measurable_set_Ioi];
  simp [h'', ennreal.to_real_of_real (sub_nonneg_of_le hp.2)],
end


lemma prob_eq_set [decidable_eq X] {ℙ : measure Ω} {a : X → Ω → ℝ} {p : ℝ}
  (hp : p ∈ set.Icc (0 : ℝ) 1)
  (ha : Indep_fun (λ _, borel ℝ) a ℙ) (ha' : ∀ i : X, pdf.is_uniform (a i) (set.Icc 0 1) ℙ)
  (A : finset X) :
  ennreal.to_real (ℙ {ω | choices a p ω = A}) = product_measure A p :=
begin
  rw [choices_eq_set_eq, ha],
  swap,
  { intros i _,
    split_ifs,
    { exact ⟨_, measurable_set_Iic, rfl⟩ },
    { exact ⟨_, measurable_set_Ioi, rfl⟩ } },
  simp only [apply_ite ℙ],
  have h₁ : ∏ x in A, (ℙ {ω : Ω | a x ω ≤ p}).to_real = ∏ x in A, p :=
    prod_congr rfl (λ x hx, prob_uniform_le hp (ha' x)),
  have h₂ : ∏ x in Aᶜ, (ℙ {ω : Ω | p < a x ω}).to_real = ∏ x in Aᶜ, (1 - p) :=
    prod_congr rfl (λ x hx, prob_lt_uniform hp (ha' x)),
  rw [prod_ite, filter_not, ←compl_eq_univ_sdiff, filter_mem_eq_inter, finset.univ_inter,
    ennreal.to_real_mul, ennreal.to_real_prod, ennreal.to_real_prod, h₁, h₂,
    prod_const, prod_const, product_measure],
end

lemma prob_mem_family [nonempty X] [decidable_eq X] (ℙ : measure Ω) (a : X → Ω → ℝ) (p : ℝ)
  (hp : p ∈ set.Icc (0 : ℝ) 1)
  (ha : Indep_fun (λ _, borel ℝ) a ℙ) (ha' : ∀ i : X, pdf.is_uniform (a i) (set.Icc 0 1) ℙ)
  (F : finset (finset X)) :
  ennreal.to_real (ℙ {ω | choices a p ω ∈ F}) = product_family_measure F p :=
begin
  inhabit X,
  haveI := (ha' default).Icc_is_probability_measure zero_lt_one,
  rw [choices_mem_eq, measure_bUnion_finset],
  rw [ennreal.to_real_sum, product_family_measure],
  { exact sum_congr rfl (λ A hA, prob_eq_set hp ha ha' A) },
  { intros x hx,
    refine prob_ne_inf _ },
  { intros A hA B hB n,
    rw [function.on_fun, set.disjoint_left],
    simp only [set.mem_set_of_eq],
    rintro x rfl,
    exact n },
  intros A hA,
  refine measurable_set_choices_eq _ ha',
end

instance my_inst : has_pdf id (volume.restrict (set.Icc (0 : ℝ) 1)) :=
begin
  refine ⟨⟨measurable_id, (set.Icc 0 1).indicator 1, _, _⟩⟩,
  { exact measurable_one.indicator measurable_set_Icc, },
  ext A hA : 1,
  rw [with_density_apply _ hA, measure.map_apply measurable_id hA, set.preimage_id],
  simp only [measure.restrict_apply', measurable_set_Icc, lintegral_indicator, pi.one_apply,
    lintegral_one, measure.restrict_apply, set.univ_inter],
  rw set.inter_comm,
end

lemma my_pdf : pdf id (volume.restrict (set.Icc (0 : ℝ) 1)) =ᵐ[volume] (set.Icc 0 1).indicator 1 :=
begin
  apply ae_eq_of_forall_set_lintegral_eq_of_sigma_finite,
  { apply measurable_pdf },
  { exact measurable_one.indicator measurable_set_Icc },
  intros A hA hA',
  rw ←map_eq_set_lintegral_pdf id (volume.restrict (set.Icc (0 : ℝ) 1)) volume hA,
  simp only [measure.map_id, measure.restrict_apply', measurable_set_Icc, lintegral_indicator,
    pi.one_apply, lintegral_one, measure.restrict_apply, set.univ_inter],
  rw set.inter_comm,
end

lemma construct_uniform : ∃ (ℙ : measure ℝ) (X : ℝ → ℝ), pdf.is_uniform X (set.Icc 0 1) ℙ :=
begin
  refine ⟨volume.restrict (set.Icc 0 1), id, _⟩,
  change _ =ᵐ[_] _,
  simp,
  apply my_pdf,
end


lemma boxes {X : Type*} [decidable_eq X] {s : finset X} (g : X → set ℝ) :
  (⋂ (i : X) (H : i ∈ s), (λ (f : X → ℝ), f i) ⁻¹' g i) =
    set.pi set.univ (λ i, if i ∈ s then g i else set.univ) :=
begin
  ext x,
  simp only [set.mem_Inter, set.mem_preimage, set.mem_univ_pi],
  refine forall_congr _,
  intros i,
  split,
  { intro h,
    split_ifs with h₁ h₁,
    { exact h h₁ },
    { exact set.mem_univ _ } },
  { intros h hi,
    rw if_pos hi at h,
    exact h }
end

lemma construct_uniform_fam (X : Type*) [finite X] : ∃ (ℙ : measure (X → ℝ)) (a : X → (X → ℝ) → ℝ),
  Indep_fun (λ _, borel ℝ) a ℙ ∧ ∀ i : X, pdf.is_uniform (a i) (set.Icc 0 1) ℙ :=
begin
  casesI nonempty_fintype X,
  classical,
  let box := {x : X → ℝ | ∀ i, x i ∈ set.Icc (0 : ℝ) 1},
  have h : ∀ i, measurable (λ (f : X → ℝ), f i) := measurable_pi_apply,
  have : box = set.Icc 0 1,
  { ext i, simp [pi.le_def, forall_and_distrib] },
  have hbox : box = set.pi set.univ (λ _, set.Icc (0 : ℝ) 1),
  { rw [set.pi_univ_Icc, this],
    refl },
  have mbox : measurable_set box,
  { rw this, exact measurable_set_Icc },
  have vbox : volume box = 1,
  { rw [this, real.volume_Icc_pi], simp },
  have int : ∀ i (A : set ℝ), (λ (f : X → ℝ), f i) ⁻¹' A ∩ box =
    set.pi set.univ (λ j, if j = i then set.Icc 0 1 ∩ A else set.Icc 0 1),
  { intros i A,
    ext x,
    simp only [set.mem_inter_eq, set.mem_preimage, set.mem_set_of_eq, set.mem_univ_pi],
    split,
    { rintro ⟨hi, b⟩ j,
      split_ifs,
      { exact ⟨b _, h_1.symm ▸ hi⟩ },
      apply b },
    intros h,
    refine ⟨_, _⟩,
    { have := h i,
      rw if_pos rfl at this,
      exact this.2 },
    intros j,
    have := h j,
    split_ifs at this,
    { exact this.1 },
    exact this },
  haveI : ∀ i, has_pdf (λ (f : X → ℝ), f i) (volume.restrict box) volume,
  { intro i,
    refine ⟨⟨h i, (set.Icc 0 1).indicator 1, _, _⟩⟩,
    { exact measurable_one.indicator measurable_set_Icc },
    ext A hA : 1,
    rw [with_density_apply _ hA, measure.map_apply (h i) hA],
    simp only [lintegral_indicator, measurable_set_Icc, pi.one_apply, lintegral_one,
      measure.restrict_apply, measurable_set.univ, set.univ_inter, h _ hA],
    rw [int, volume_pi_pi],
    simp only [apply_ite volume, real.volume_Icc, sub_zero, ennreal.of_real_one, prod_ite_eq',
      finset.mem_univ, if_true] },
  refine ⟨volume.restrict box, λ x f, f x, _, _⟩,
  { rw Indep_fun_iff_measure_inter_preimage_eq_mul,
    intros s g hg,
    simp only [measure.restrict_apply' mbox, int, volume_pi_pi],
    rw [boxes, hbox, ←set.pi_inter_distrib, volume_pi_pi],
    simp only [apply_ite volume, real.volume_Icc, sub_zero, ennreal.of_real_one, prod_ite_eq',
      finset.mem_univ, if_true],
    have : ∀ i, volume (ite (i ∈ s) (g i) set.univ ∩ set.Icc 0 1) =
      ite (i ∈ s) (volume (g i ∩ set.Icc 0 1)) 1,
    { intro i,
      split_ifs,
      { refl },
      { simp } },
    simp only [this, ←prod_filter, filter_mem_eq_inter, finset.univ_inter, set.inter_comm (g _)] },
  intro i,
  change _ =ᵐ[_] _,
  apply ae_eq_of_forall_set_lintegral_eq_of_sigma_finite,
  { apply measurable_pdf },
  { exact (measurable_one.const_smul _).indicator measurable_set_Icc },
  intros A hA hA',
  rw [←map_eq_set_lintegral_pdf (λ f : X → ℝ, f i) (volume.restrict box) volume hA],
  simp only [real.volume_Icc, sub_zero, ennreal.of_real_one, ennreal.inv_one, one_smul,
    lintegral_indicator, measurable_set_Icc, pi.one_apply, lintegral_one, measure.restrict_apply,
    measurable_set.univ, set.univ_inter, measure.map_apply (h _) hA, measure.restrict_apply' mbox,
    int, volume_pi_pi, apply_ite volume, prod_ite_eq', finset.mem_univ, if_pos],
end

lemma nonempty_of_nonempty_of_not_univ {F : finset (finset X)}
  (hF₀ : F.nonempty) (hF₁ : F ≠ univ) :
  nonempty X :=
begin
  rw ←not_is_empty_iff,
  introI h,
  have : F ⊆ {∅},
  { intros A hA,
    simp },
  rw finset.subset_singleton_iff at this,
  rcases this with rfl | rfl,
  { simpa using hF₀ },
  { refine hF₁ (by simp [singleton_inj]) }
end

lemma product_family_measure_monotone [decidable_eq X] {F : finset (finset X)}
  (hF : is_upper_set (F : set (finset X))) :
  monotone_on (product_family_measure F) (set.Icc 0 1) :=
λ p₁ hp₁ p₂ hp₂ h,
begin
  casesI is_empty_or_nonempty X,
  { have : F = ∅ ∨ F = univ,
    { have : (univ : finset (finset X)) = {∅},
      { rw [finset.univ_unique, singleton_inj], simp },
      rw [this, ←finset.subset_singleton_iff],
      intros x hx,
      simp },
    rcases this with rfl | rfl,
    { simp only [product_family_measure_empty] },
    { simp only [product_family_measure_univ] } },
  obtain ⟨ℙ, a, f₁, f₂⟩ := construct_uniform_fam X,
  set Ω := X → ℝ,
  rw ←prob_mem_family ℙ a p₁ hp₁ f₁ f₂ F,
  rw ←prob_mem_family ℙ a p₂ hp₂ f₁ f₂ F,
  apply ennreal.to_real_mono,
  { inhabit X,
    haveI := (f₂ default).Icc_is_probability_measure zero_lt_one,
    exact prob_ne_inf _ },
  apply measure_mono,
  simp only [set.set_of_subset_set_of],
  intros ω hω,
  have : choices a p₁ ω ⊆ choices a p₂ ω,
  { intros x,
    simp only [choices, mem_filter, finset.mem_univ, true_and],
    intros h₁,
    apply h₁.trans h },
  exact hF this hω,
end

lemma inj_on_or_const (f : ℝ → ℝ) {a b : ℝ} (p : polynomial ℤ)
  (hf : ∀ x, f x = p.eval₂ (int.cast_ring_hom ℝ) x) (hp : monotone_on f (set.Icc a b)) :
  set.inj_on f (set.Icc a b) ∨ ∀ x y ∈ set.Icc a b, f x = f y :=
begin
  have hf' : ∀ x, f x = (p.map (int.cast_ring_hom ℝ)).eval x,
  { simpa only [←polynomial.eval₂_eq_eval_map] },
  simp only [or_iff_not_imp_left, set.inj_on, not_forall, forall_exists_index],
  intros x₁ hx₁ x₂ hx₂ h h',
  wlog := lt_or_gt_of_ne h' using x₁ x₂,
  suffices : polynomial.map (int.cast_ring_hom ℝ) p = polynomial.C (f x₁),
  { simp only [hf'],
    simp only [this, polynomial.eval_C, eq_self_iff_true, implies_true_iff] },
  refine polynomial.eq_of_infinite_eval_eq _ _ ((set.Icc_infinite case).mono (λ t ht, _)),
  have ht' : t ∈ set.Icc a b := ⟨hx₁.1.trans ht.1, hx₂.2.trans' ht.2⟩,
  simp only [polynomial.eval_C, set.mem_set_of_eq, ←hf'],
  exact le_antisymm (h.symm ▸ hp ht' hx₂ ht.2) (hp hx₁ ht' ht.1),
end

lemma product_family_measure_strict_mono [decidable_eq X] {F : finset (finset X)}
  (hF : is_upper_set (F : set (finset X))) (hF₁ : F.nonempty) (hF₂ : F ≠ univ) :
  strict_mono_on (product_family_measure F) (set.Icc 0 1) :=
begin
  intros p₁ hp₁ p₂ hp₂ h,
  refine lt_of_le_of_ne (product_family_measure_monotone hF hp₁ hp₂ h.le) _,
  suffices : set.inj_on (product_family_measure F) (set.Icc 0 1),
  { exact mt (this hp₁ hp₂) h.ne },
  refine (inj_on_or_const _ (product_family_measure' F) _ _).resolve_right _,
  { intro x, rw eval_product_family_measure' },
  { exact product_family_measure_monotone hF },
  simp only [and_imp, not_forall, exists_prop],
  refine ⟨0, by simp, 1, by simp, _⟩,
  simp [product_family_measure_one', product_family_measure_zero', *]
end

lemma product_family_measure_continuous [decidable_eq X] {F : finset (finset X)} :
  continuous (product_family_measure F) :=
begin
  suffices : continuous (λ x, (product_family_measure' F).eval₂ (int.cast_ring_hom ℝ) x),
  { simpa only [eval_product_family_measure'] using this },
  apply polynomial.continuous_eval₂,
end

lemma exists_half [decidable_eq X] {F : finset (finset X)} (hF : is_upper_set (F : set (finset X)))
  (hF₁ : F.nonempty) (hF₂ : F ≠ univ) :
  ∃ p ∈ set.Icc (0 : ℝ) 1, product_family_measure F p = 1 / 2 :=
begin
  simp only [exists_prop],
  refine product_family_measure_continuous.continuous_on.surj_on_Icc
    (set.left_mem_Icc.2 zero_le_one) (set.right_mem_Icc.2 zero_le_one) _,
  rw [product_family_measure_zero' hF hF₂, product_family_measure_one' hF hF₁, set.mem_Icc],
  split; linarith
end

noncomputable def threshold (F : finset (finset X)) : ℝ :=
by classical; exact
if h : ∃ p ∈ set.Icc (0 : ℝ) 1, product_family_measure F p = 1 / 2 then h.some else 0

lemma threshold_mem_Icc : threshold F ∈ set.Icc (0 : ℝ) 1 :=
begin
  rw [threshold],
  split_ifs,
  { exact h.some_spec.some },
  simp
end

lemma threshold_empty : threshold (∅ : finset (finset X)) = 0 :=
dif_neg (by norm_num)

lemma threshold_univ : threshold (univ : finset (finset X)) = 0 :=
dif_neg (by norm_num)

lemma threshold_spec (hF : is_upper_set (F : set (finset X))) (hF₁ : F.nonempty) (hF₂ : F ≠ univ) :
  product_family_measure F (threshold F) = 1 / 2 :=
begin
  rw [threshold],
  split_ifs,
  { exact h.some_spec.some_spec },
  { cases h (exists_half hF hF₁ hF₂) }
end

lemma threshold_unique (hF : is_upper_set (F : set (finset X))) (hF₁ : F.nonempty) (hF₂ : F ≠ univ)
  {p : ℝ} (hp : p ∈ set.Icc (0 : ℝ) 1) (hp' : product_family_measure F p = 1 / 2) :
  p = threshold F :=
begin
  apply (product_family_measure_strict_mono hF hF₁ hF₂).inj_on hp _ _,
  apply threshold_mem_Icc,
  rw [threshold_spec hF hF₁ hF₂, hp']
end

lemma le_threshold_iff (hF : is_upper_set (F : set (finset X))) (hF₁ : F.nonempty) (hF₂ : F ≠ univ)
  {p : ℝ} (hp : p ∈ set.Icc (0 : ℝ) 1) :
  p ≤ threshold F ↔ product_family_measure F p ≤ 1 / 2 :=
by rw [←strict_mono_on.le_iff_le (product_family_measure_strict_mono hF hF₁ hF₂) hp
  threshold_mem_Icc, threshold_spec hF hF₁ hF₂]

lemma threshold_le_iff (hF : is_upper_set (F : set (finset X))) (hF₁ : F.nonempty) (hF₂ : F ≠ univ)
  {p : ℝ} (hp : p ∈ set.Icc (0 : ℝ) 1) :
  threshold F ≤ p ↔ 1 / 2 ≤ product_family_measure F p :=
by rw [←strict_mono_on.le_iff_le (product_family_measure_strict_mono hF hF₁ hF₂) threshold_mem_Icc
  hp, threshold_spec hF hF₁ hF₂]

def finset.upper_closure [decidable_eq X] (G : finset (finset X)) : finset (finset X) :=
finset.univ.filter (λ A, ∃ B ∈ G, B ⊆ A)

lemma finset.upper_closure_empty : (∅ : finset (finset X)).upper_closure = ∅ :=
by simp [finset.upper_closure]

lemma finset_upper_closure_self [decidable_eq X] : F ⊆ F.upper_closure :=
λ A hA, mem_filter.2 ⟨mem_univ _, A, hA, finset.subset.rfl⟩

lemma finset.mem_upper_closure [decidable_eq X] (G : finset (finset X)) (A : finset X) :
  A ∈ G.upper_closure ↔ ∃ B ∈ G, B ⊆ A :=
by simp [finset.upper_closure]

/-- G is a cover of F -/
def finset.has_cover {X : Type*} (F G : finset (finset X)) : Prop := ∀ A ∈ F, ∃ B ∈ G, B ⊆ A

lemma finset.has_cover_iff {F G : finset (finset X)} :
  F.has_cover G ↔ F ⊆ G.upper_closure :=
by simp [finset.upper_closure, finset.subset_iff, finset.has_cover]

lemma has_cover_self {X : Type*} {F : finset (finset X)} : F.has_cover F := subset_upper_closure

lemma univ_has_cover_iff {G : finset (finset X)} :
  (univ : finset (finset X)).has_cover G ↔ ∅ ∈ G :=
⟨λ h, by simpa [finset.subset_empty] using h ∅ (mem_univ _), λ h A _, ⟨_, h, finset.empty_subset _⟩⟩

lemma has_cover_singletons (hF : ∅ ∉ F) : F.has_cover (finset.univ.image singleton) :=
begin
  intros A,
  simp only [mem_coe, coe_upper_closure, mem_set_of_eq, finset.mem_image, finset.mem_univ,
    exists_true_left, finset.le_eq_subset, exists_exists_eq_and, exists_prop, true_and,
    finset.singleton_subset_iff],
  intro hA,
  exact finset.nonempty_iff_ne_empty.2 (ne_of_mem_of_not_mem hA hF),
end

lemma empty_has_cover {X : Type*} {F : finset (finset X)} : (∅ : finset (finset X)).has_cover F :=
by simp [finset.has_cover]

def finset.is_cheap {X : Type*} (G : finset (finset X)) (p : ℝ) : Prop :=
∑ S in G, p ^ S.card ≤ 1 / 2

lemma empty_is_cheap {X : Type*} {p : ℝ} : (∅ : finset (finset X)).is_cheap p :=
by simp [finset.is_cheap]

lemma is_zero_cheap {X : Type*} {G : finset (finset X)} (hG : ∅ ∉ G) : G.is_cheap 0 :=
by { simp only [finset.is_cheap, zero_pow_eq, card_eq_zero, sum_ite_eq', hG, if_false], norm_num }

lemma not_cheap_of_empty_mem {X : Type*} {G : finset (finset X)} {p : ℝ} (hG : ∅ ∈ G) (hp : 0 ≤ p) :
  ¬ G.is_cheap p :=
begin
  simp only [finset.is_cheap, not_le],
  refine lt_of_lt_of_le _ (single_le_sum (λ S hS, pow_nonneg hp _) hG),
  norm_num,
end

lemma not_cheap_one {X : Type*} {G : finset (finset X)} (hG : G.nonempty) : ¬ G.is_cheap 1 :=
begin
  simp only [finset.is_cheap, not_le, one_pow, sum_const, nat.smul_one_eq_coe],
  exact (nat.one_le_cast.2 hG.card_pos).trans_lt' (by norm_num),
end

def real.is_small {X : Type*} (F : finset (finset X)) (p : ℝ) : Prop :=
  ∃ (G : finset (finset X)), F.has_cover G ∧ G.is_cheap p

lemma is_small_one {X : Type*} {p : ℝ} : p.is_small (∅ : finset (finset X)) :=
⟨∅, empty_has_cover, empty_is_cheap⟩

lemma is_small_zero {X : Type*} {F : finset (finset X)} (hF : ∅ ∉ F) : (0 : ℝ).is_small F :=
⟨F, has_cover_self, is_zero_cheap hF⟩

lemma is_small_zero' (hF : is_upper_set (F : set (finset X))) (hF' : F ≠ univ) :
  (0 : ℝ).is_small F :=
is_small_zero (by rwa [←finset.bot_eq_empty, ←finset.mem_coe, hF.bot_mem, coe_eq_univ])

lemma univ_is_small_iff {p : ℝ} (hp : 0 ≤ p) : ¬ p.is_small (univ : finset (finset X)) :=
begin
  simp only [real.is_small, univ_has_cover_iff, not_exists, not_and],
  intros G hG,
  exact not_cheap_of_empty_mem hG hp,
end

noncomputable def expectation_threshold {X : Type*} (F : finset (finset X)) : ℝ :=
Sup {p ∈ Icc 0 1 | p.is_small F}

-- lemma expectation_threshold_mem_Icc :
--   expectation_threshold F ∈ set.Icc (0 : ℝ) 1 :=
-- begin
--   have := is_closed.cSup_mem,
-- end

-- lemma expectation_threshold_empty : expectation_threshold (∅ : finset (finset X)) = 1 :=
-- begin

-- end

lemma expectation_threshold_univ : expectation_threshold (univ : finset (finset X)) = 0 :=
begin
  have : {p ∈ set.Icc (0 : ℝ) 1 | (p : ℝ).is_small (univ : finset (finset X))} = ∅,
  { simp [set.eq_empty_iff_forall_not_mem, univ_is_small_iff] {contextual := tt} },
  rw [expectation_threshold, this, real.Sup_empty],
end


lemma prob_contains_set {ℙ : measure Ω} {a : X → Ω → ℝ} {p : ℝ}
  (hp : p ∈ set.Icc (0 : ℝ) 1)
  (ha : Indep_fun (λ _, borel ℝ) a ℙ) (ha' : ∀ i : X, pdf.is_uniform (a i) (set.Icc 0 1) ℙ)
  (S : finset X) :
  (ℙ {ω | S ⊆ choices a p ω}).to_real = p ^ S.card :=
begin
  rw [subset_choices_eq, ha, ennreal.to_real_prod, ←prod_const],
  { exact prod_congr rfl (λ x hx, prob_uniform_le hp (ha' _)) },
  intros i hi,
  exact ⟨_, measurable_set_Iic, rfl⟩,
end

lemma expectation_contains_set [nonempty X] {ℙ : measure Ω} {a : X → Ω → ℝ} {p : ℝ}
  (hp : p ∈ set.Icc (0 : ℝ) 1)
  (ha : Indep_fun (λ _, borel ℝ) a ℙ) (ha' : ∀ i : X, pdf.is_uniform (a i) (set.Icc 0 1) ℙ)
  (G : finset (finset X)) :
  ∫ ω, (finset.card (G.filter (λ S, S ⊆ choices a p ω)) : ℝ) ∂ℙ = ∑ S in G, p ^ S.card :=
begin
  simp only [count_copies_eq],
  inhabit X,
  haveI := (ha' default).Icc_is_probability_measure zero_lt_one,
  rw integral_finset_sum,
  swap,
  { intros x hx, exact (integrable_const 1).indicator (measurable_set_subset_choices ha'), },
  refine sum_congr rfl (λ x hx, _),
  rw [prob_eq_exp (measurable_set_subset_choices ha'), subset_choices_eq, ha, ←prod_const,
    ennreal.to_real_prod],
  { refine prod_congr rfl (λ i hi, _),
    exact prob_uniform_le hp (ha' _) },
  intros i hi,
  exact ⟨_, measurable_set_Iic, rfl⟩,
end

lemma sum_inequality [nonempty X] {p : ℝ} (hp : p ∈ set.Icc (0 : ℝ) 1)
  {G : finset (finset X)} :
  product_family_measure G.upper_closure p ≤ ∑ S in G, p ^ S.card :=
begin
  obtain ⟨ℙ, a, ha, ha'⟩ := construct_uniform_fam X,
  rw [←prob_mem_family ℙ a p hp ha ha', ←prob_eq_exp, ←expectation_contains_set hp ha ha'],
  refine integral_mono_of_nonneg _ _ _,
  { exact filter.eventually_of_forall (indicator_nonneg (by simp)) },
  { exact integrable_count_copies ha' },
  { refine filter.eventually_of_forall (λ ω, _),
    simp only [set.indicator_apply, mem_set_of_eq, pi.one_apply, G.mem_upper_closure],
    split_ifs,
    { simpa only [nat.one_le_cast, nat.succ_le_iff, card_pos, filter_nonempty_iff] },
    apply nat.cast_nonneg },
  { apply measurable_set_choices_mem ha' }
end

lemma expectation_threshold_le_threshold
  (hF : is_upper_set (F : set (finset X))) (hF₀ : F.nonempty) (hF₁ : F ≠ univ) :
  expectation_threshold F ≤ threshold F :=
begin
  refine cSup_le ⟨0, by simp, is_small_zero' hF hF₁⟩ _,
  intros q hq,
  simp only [mem_sep_eq] at hq,
  rw le_threshold_iff hF hF₀ hF₁ hq.1,
  obtain ⟨hq₁, G, hG₁, hG₂⟩ := hq,
  apply le_trans _ hG₂,
  rw finset.has_cover_iff at hG₁,
  refine (product_family_measure_mono hG₁ hq₁).trans _,
  haveI := nonempty_of_nonempty_of_not_univ hF₀ hF₁,
  refine sum_inequality hq₁,
end

def finset.minimals [decidable_eq X] (F : finset (finset X)) : finset (finset X) :=
F.filter (λ A, ∀ B ∈ F, ¬B ⊂ A)

lemma minimals_subset [decidable_eq X] : F.minimals ⊆ F := filter_subset _ _

lemma mem_minimals [decidable_eq X] (A : finset X) :
  A ∈ F.minimals ↔ A ∈ F ∧ ∀ B ∈ F, ¬ B ⊂ A :=
by simp [finset.minimals]

lemma minimals_aux [decidable_eq X] : ∀ A ∈ F, ∃ B ⊆ A, B ∈ F.minimals :=
begin
  intros A,
  apply finset.strong_induction_on A,
  intros B ih hB,
  by_cases B ∈ F.minimals,
  { exact ⟨_, finset.subset.rfl, h⟩ },
  simp only [mem_minimals, not_and, hB, not_forall, not_not, forall_true_left] at h,
  obtain ⟨C, hC, hC'⟩ := h,
  obtain ⟨D, hD, hD'⟩ := ih _ hC' hC,
  exact ⟨D, hD.trans hC'.1, hD'⟩,
end

lemma minimals_nonempty [decidable_eq X] (hF : F.nonempty) : F.minimals.nonempty :=
begin
  obtain ⟨A, hA⟩ := hF,
  obtain ⟨B, _, hB⟩ := minimals_aux A hA,
  exact ⟨_, hB⟩,
end

lemma minimals_upper_closure [decidable_eq X] (hF : is_upper_set (F : set (finset X))) :
  F.minimals.upper_closure = F :=
begin
  ext A,
  simp only [finset.mem_upper_closure],
  split,
  { rintro ⟨B, hB, hB'⟩,
    exact hF hB' (minimals_subset hB) },
  { intro hA,
    obtain ⟨B, hB, hB'⟩ := minimals_aux _ hA,
    exact ⟨_, hB', hB⟩ }
end

def largest_minimal {X : Type*} (F : finset (finset X)) : ℕ :=
if h : F.nonempty
  then finset.max' (F.image card) (h.image _)
  else 0

-- if h : ∃ A ∈ F, ∀ B ∈ F, ¬B ⊆ A
--   then h.some.card
--   else 0

-- def constant_L : ℝ := sorry

-- theorem one_two {X : Type*} {l : ℕ} {p : ℝ} {H : finset (finset X)}
--   (hH : ∀ A ∈ H, finset.card A ≤ l) (hH' : ¬ p.is_small H) :

#lint
