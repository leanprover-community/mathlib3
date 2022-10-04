import linear_algebra.span
import ring_theory.ideal.operations
import ring_theory.finiteness
import ring_theory.dimension.support
import ring_theory.localization.ideal
import ring_theory.dimension.minimal_primes

/-!

## Todo

Generalize this to non-commutative settings once there are annihilator for non-commutative rings.

-/

variables {R : Type*} [comm_ring R] (I J : ideal R) (M : Type*) [add_comm_group M] [module R M]

def is_associated_prime : Prop :=
I.is_prime ∧ ∃ x : M, I = (R ∙ x).annihilator

variables (R)

def associated_primes : set (ideal R) := { I | is_associated_prime I M }

variables {I M R} (h : is_associated_prime I M)
variables {M' : Type*} [add_comm_group M'] [module R M'] (f : M →ₗ[R] M')

lemma is_associated_prime.is_prime : I.is_prime := h.1

lemma is_associated_prime.map_injective (h : is_associated_prime I M) (hf : function.injective f) :
  is_associated_prime I M' :=
begin
  obtain ⟨x, rfl⟩ := h.2,
  refine ⟨h.1, ⟨f x, _⟩⟩,
  ext r,
  rw [submodule.mem_annihilator_span_singleton, submodule.mem_annihilator_span_singleton,
    ← map_smul, ← f.map_zero, hf.eq_iff],
end

lemma is_associated_prime.iff_of_equiv (l : M ≃ₗ[R] M') :
  is_associated_prime I M ↔ is_associated_prime I M' :=
⟨λ h, h.map_injective l l.injective, λ h, h.map_injective l.symm l.symm.injective⟩

lemma not_is_associated_prime_of_subsingleton [subsingleton M] : ¬ is_associated_prime I M :=
begin
  rintro ⟨hI, x, hx⟩,
  apply hI.ne_top,
  rwa [subsingleton.elim x 0, submodule.span_singleton_eq_bot.mpr rfl,
    submodule.annihilator_bot] at hx
end

variable (R)

lemma exists_le_is_associated_prime_of_is_noetherian_ring [H : is_noetherian_ring R]
  (x : M) (hx : x ≠ 0) :
  ∃ P : ideal R, is_associated_prime P M ∧ (R ∙ x).annihilator ≤ P :=
begin
  have : (R ∙ x).annihilator ≠ ⊤,
  { rwa [ne.def, ideal.eq_top_iff_one, submodule.mem_annihilator_span_singleton, one_smul] },
  obtain ⟨P, ⟨l, h₁, y, rfl⟩, h₃⟩ := set_has_maximal_iff_noetherian.mpr H
    ({ P | (R ∙ x).annihilator ≤ P ∧ P ≠ ⊤ ∧ ∃ y : M, P = (R ∙ y).annihilator })
    ⟨(R ∙ x).annihilator, rfl.le, this, x, rfl⟩,
  refine ⟨_, ⟨⟨h₁, _⟩, y, rfl⟩, l⟩,
  intros a b hab,
  rw or_iff_not_imp_left,
  intro ha,
  rw submodule.mem_annihilator_span_singleton at ha hab,
  have H₁ : (R ∙ y).annihilator ≤ (R ∙ a • y).annihilator,
  { intros c hc,
    rw submodule.mem_annihilator_span_singleton at hc ⊢,
    rw [smul_comm, hc, smul_zero] },
  have H₂ : (submodule.span R {a • y}).annihilator ≠ ⊤,
  { rwa [ne.def, submodule.annihilator_eq_top_iff, submodule.span_singleton_eq_bot] },
  rwa [← h₃ (R ∙ a • y).annihilator ⟨l.trans H₁, H₂, _, rfl⟩ H₁,
    submodule.mem_annihilator_span_singleton, smul_comm, smul_smul]
end

variable {R}

lemma mem_associate_primes : I ∈ associated_primes R M ↔ is_associated_prime I M := iff.rfl

lemma associated_primes_le_of_injective (hf : function.injective f) :
  associated_primes R M ⊆ associated_primes R M' :=
λ I h, h.map_injective f hf

lemma linear_equiv.associated_primes_eq (l : M ≃ₗ[R] M') :
  associated_primes R M = associated_primes R M' :=
le_antisymm (associated_primes_le_of_injective l l.injective)
  (associated_primes_le_of_injective l.symm l.symm.injective)

lemma associated_primes_of_subsingleton [subsingleton M] : associated_primes R M = ∅ :=
begin
  ext, simp only [set.mem_empty_iff_false, iff_false], apply not_is_associated_prime_of_subsingleton
end

variables (R M)

lemma associated_primes_nonempty [is_noetherian_ring R] [nontrivial M] :
  (associated_primes R M).nonempty :=
begin
  obtain ⟨x, hx⟩ := exists_ne (0 : M),
  obtain ⟨P, hP, _⟩ := exists_le_is_associated_prime_of_is_noetherian_ring R x hx,
  exact ⟨P, hP⟩,
end

lemma associated_primes_subset_support :
  associated_primes R M ⊆ module.support R M :=
begin
  rintros _ ⟨h, x, rfl⟩,
  refine ⟨h, ⟨⟨localized_module.mk 0 1, localized_module.mk x 1, _⟩⟩⟩,
  simp_rw [ne.def, localized_module.mk_eq, not_exists, one_smul, smul_zero],
  rintros ⟨a, ha : a ∉ (R ∙ x).annihilator⟩ e,
  rw submodule.mem_annihilator_span_singleton at ha,
  exact ha e,
end

variables {R M}

lemma module.mem_support_if_exists_associated_primes [hR : is_noetherian_ring R]
  {I : ideal R} [I.is_prime] :
  I ∈ module.support R M ↔ ∃ J ∈ associated_primes R M, J ≤ I :=
begin
  split,
  { intro hI,
    haveI := hI.some,
    haveI : nontrivial _ := hI.some_spec,
    haveI hR' : is_noetherian_ring (localization I.prime_compl),
    { rw [is_noetherian_ring_iff, is_noetherian_iff_well_founded] at hR ⊢,
      exact order_embedding.well_founded
        (is_localization.order_embedding I.prime_compl $ localization I.prime_compl).dual hR },
    obtain ⟨p, hp, x, hx⟩ := associated_primes_nonempty
      (localization I.prime_compl) (localized_module I.prime_compl M),
    obtain ⟨⟨m, s⟩, rfl : localized_module.mk m s = x⟩ := quotient.exists_rep x,
    resetI,
    let q := p.comap (algebra_map R $ localization I.prime_compl),
    obtain ⟨S, hS⟩ := (hR.1 : _) q,
    have hq : ∀ x, x ∈ q ↔ ∃ y : I.prime_compl, y • x • m = 0,
    { simp_rw [ideal.mem_comap, hx, submodule.mem_annihilator_span_singleton, algebra_map_smul,
        ← localized_module.zero_mk (1 : I.prime_compl), localized_module.smul'_mk,
        localized_module.mk_eq, one_smul, smul_zero, @eq_comm M 0],
      exact λ _, iff.rfl },
    have : ∀ t : S, ∃ y : I.prime_compl, y • (t : R) • m = 0,
    { simp_rw [← hq, ← hS], intro t, apply submodule.subset_span, exact t.2 },
    choose u hu,
    suffices : (R ∙ finset.univ.prod u • m).annihilator = q,
    { refine ⟨_, ⟨ideal.is_prime.comap _, _, this.symm⟩, set.disjoint_compl_left_iff_subset.mp _⟩,
      exact ((is_localization.is_prime_iff_is_prime_disjoint I.prime_compl _ _).mp hp).2  },
    ext a,
    rw [submodule.mem_annihilator_span_singleton, smul_comm a],
    swap, { apply_instance },
    split,
    { intro e, rw hq, exact ⟨_, e⟩ },
    { rintros ha,
      rw ← hS at ha,
      apply submodule.span_induction ha; clear ha a,
      { intros x hx,
        obtain ⟨y, hy⟩ : u ⟨x, hx⟩ ∣ finset.univ.prod u :=
          finset.dvd_prod_of_mem _ (finset.mem_univ _),
        rw [hy, mul_comm, mul_smul],
        convert smul_zero y,
        exact hu ⟨x, hx⟩ },
      { rw [zero_smul, smul_zero] },
      { intros x y ex ey, rw [add_smul, smul_add, ex, ey, add_zero] },
      { intros x y e, rw [smul_assoc, smul_comm, e, smul_zero] } } },
  { rintro ⟨J, hJ, e⟩,
    exact module.mem_support_of_le e (associated_primes_subset_support _ _ hJ) }
end
.
lemma annihilator_le_of_mem_associate_primes (I ∈ associated_primes R M) :
  (⊤ : submodule R M).annihilator ≤ I :=
begin
  obtain ⟨hI, x, rfl⟩ := H,
  exact submodule.annihilator_mono le_top,
end

lemma submodule.bot_colon (p : submodule R M) : (⊥ : submodule R M).colon p = p.annihilator :=
begin
  ext, simp [submodule.mem_colon, submodule.mem_annihilator],
end

lemma submodule.restrict_scalars_colon_top {A : Type*} [comm_ring A] [algebra R A] (I : ideal A) :
  (I.restrict_scalars R).colon ⊤ = I.comap (algebra_map R A) :=
begin
  ext,
  rw [submodule.mem_colon],
  change _ ↔ (algebra_map R A) x ∈ I,
  split,
  { intros H, rw algebra.algebra_map_eq_smul_one, exact H 1 trivial },
  { intros e a _, rw algebra.smul_def, exact I.mul_mem_right _ e }
end

lemma submodule.top_annihilator_eq_ker {A : Type*} [comm_ring A] [algebra R A] :
  (⊤ : submodule R A).annihilator = (algebra_map R A).ker :=
begin
  rw [ring_hom.ker_eq_comap_bot, ← submodule.restrict_scalars_colon_top,
    submodule.restrict_scalars_bot, submodule.bot_colon],
end

variables (R M)

lemma annihilator_minimal_primes_subset_associated_primes
  [is_noetherian_ring R] [module.finite R M] :
  (⊤ : submodule R M).annihilator.minimal_primes ⊆ associated_primes R M :=
begin
  intros I hI,
  haveI := hI.1.1,
  have : I ∈ module.support R M,
  { rw module.mem_support_iff_annihilator_le_of_fg, exact hI.1.2 },
  rw module.mem_support_if_exists_associated_primes at this,
  obtain ⟨J, hJ, e⟩ := this,
  exact (e.antisymm $ hI.2 ⟨hJ.1, annihilator_le_of_mem_associate_primes _ hJ⟩ e) ▸ hJ,
end

lemma minimal_primes_subset_associated_primes [is_noetherian_ring R] :
  I.minimal_primes ⊆ associated_primes R (R ⧸ I) :=
begin
  convert annihilator_minimal_primes_subset_associated_primes R (R ⧸ I),
  rw [submodule.top_annihilator_eq_ker],
  simp
end

lemma Inf_associated_primes_eq_Inf_support [is_noetherian_ring R] :
  Inf (associated_primes R M) = Inf (module.support R M) :=
begin
  refine le_antisymm (le_Inf _) (Inf_le_Inf (associated_primes_subset_support R M)),
  intros I hI,
  haveI := hI.some,
  obtain ⟨J, hJ, e⟩ := module.mem_support_if_exists_associated_primes.mp hI,
  exact (Inf_le hJ).trans e
end

variables {R M}

lemma mem_Inf_associated_primes_iff_locally_nilpotent [is_noetherian_ring R] {x : R} :
  x ∈ Inf (associated_primes R M) ↔ module.is_locally_nilpotent x M :=
by rw [Inf_associated_primes_eq_Inf_support R M, module.mem_Inf_support_iff_locally_nilpotent]

variables (R M)

lemma coe_Inf_associated_primes [is_noetherian_ring R] :
  (↑(Inf (associated_primes R M)) : set R) = { r : R | module.is_locally_nilpotent r M } :=
set.ext (λ x, mem_Inf_associated_primes_iff_locally_nilpotent)

lemma Inf_associated_primes_eq_annihilator_radical [is_noetherian_ring R] [module.finite R M] :
  Inf (associated_primes R M) = (⊤ : submodule R M).annihilator.radical :=
by rw [Inf_associated_primes_eq_Inf_support, module.Inf_support_eq_annihilator_radical]

section non_zero_divisors

def module.non_zero_divisors : submonoid R :=
{ carrier := λ r, ∀ m : M, r • m = 0 → m = 0,
  mul_mem' := λ r₁ r₂ h₁ h₂ m e, h₂ m (h₁ (r₂ • m) ((smul_smul r₁ r₂ m).trans e)),
  one_mem' := λ m, (one_smul _ _).symm.trans }

variables {R M}

variables {A : Type*} [comm_ring A] [algebra R A]

lemma module.mem_non_zero_divisors {r : R} :
  r ∈ module.non_zero_divisors R M ↔ ∀ m : M, r • m = 0 → m = 0 := iff.rfl

lemma module.comap_non_zero_divisors [module A M] [is_scalar_tower R A M] :
  (module.non_zero_divisors A M).comap (algebra_map R A) = module.non_zero_divisors R M :=
begin
  ext,
  rw [submonoid.mem_comap, module.mem_non_zero_divisors, module.mem_non_zero_divisors],
  simp_rw algebra_map_smul
end

lemma module.non_zero_divisors_self  :
  module.non_zero_divisors R R = non_zero_divisors R :=
begin
  ext,
  rw [module.mem_non_zero_divisors, mem_non_zero_divisors_iff],
  simp_rw [smul_eq_mul, mul_comm],
end

lemma module.non_zero_divisors_of_algebra  :
  module.non_zero_divisors R A = (non_zero_divisors A).comap (algebra_map R A) :=
begin
  rw [← module.non_zero_divisors_self, module.comap_non_zero_divisors]
end

end non_zero_divisors

lemma Union_associated_primes [is_noetherian_ring R] :
  (⋃ I ∈ associated_primes R M, ↑I : set R) = (module.non_zero_divisors R M)ᶜ :=
begin
  ext x,
  simp only [set.mem_Union, set_like.mem_coe, set.mem_compl_iff, module.mem_non_zero_divisors],
  split,
  { rintros ⟨I, ⟨hI, y, rfl⟩, h⟩ hx,
    rw submodule.mem_annihilator_span_singleton at h,
    rw [hx _ h, submodule.span_singleton_eq_bot.mpr rfl, submodule.annihilator_bot] at hI,
    exact (hI.1 : _) rfl },
  { push_neg,
    rintro ⟨m, h₁, h₂⟩,
    obtain ⟨P, h₃, h₄⟩ := exists_le_is_associated_prime_of_is_noetherian_ring R m h₂,
    refine ⟨P, h₃, h₄ (by rwa submodule.mem_annihilator_span_singleton)⟩ }
end

lemma is_associated_prime.eq_primary {R : Type*} [comm_ring R] {I J : ideal R} (hI : I.is_primary)
  (h : is_associated_prime J (R ⧸ I)) : J = I.radical :=
begin
  obtain ⟨hJ, x, e⟩ := h,
  have : x ≠ 0,
  { rintro rfl, apply hJ.1,
    rwa [submodule.span_singleton_eq_bot.mpr rfl, submodule.annihilator_bot] at e },
  obtain ⟨x, rfl⟩ := ideal.quotient.mkₐ_surjective R _ x,
  replace e : ∀ {y}, y ∈ J ↔ x * y ∈ I,
  { intro y, rw [e, submodule.mem_annihilator_span_singleton, ← map_smul, smul_eq_mul, mul_comm,
      ideal.quotient.mkₐ_eq_mk, ← ideal.quotient.mk_eq_mk, submodule.quotient.mk_eq_zero] },
  apply le_antisymm,
  { intros y hy,
    exact (hI.2 $ e.mp hy).resolve_left ((submodule.quotient.mk_eq_zero I).not.mp this) },
  { rw hJ.radical_le_iff, intros y hy, exact e.mpr (I.mul_mem_left x hy) }
end

lemma associated_primes_of_is_primary {R : Type*} [comm_ring R] [is_noetherian_ring R]
  {I : ideal R} (hI : I.is_primary) :
  associated_primes R (R ⧸ I) = {I.radical} :=
begin
  ext J,
  rw [set.mem_singleton_iff],
  refine ⟨is_associated_prime.eq_primary hI, _⟩,
  rintro rfl,
  haveI : nontrivial (R ⧸ I) := ⟨⟨(I^.quotient.mk : _) 1, (I^.quotient.mk : _) 0, _⟩⟩,
  obtain ⟨a, ha⟩ := associated_primes_nonempty R (R ⧸ I),
  exact ha.eq_primary hI ▸ ha,
  rw [ne.def, ideal.quotient.eq, sub_zero, ← ideal.eq_top_iff_one],
  exact hI.1
end
.
