import algebra.module.localized_module
import ring_theory.localization.at_prime
import ring_theory.finiteness

variables (R M A : Type*) [comm_ring R] [add_comm_group M] [module R M] [ring A] [algebra R A]

section
open localized_module

instance {S : submonoid R} : add_comm_group (localized_module S M) :=
{ neg := λ p, lift_on p (λ x, localized_module.mk (-x.1) x.2)
    (λ ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨u, hu⟩, by { rw mk_eq, exact ⟨u, by simpa⟩ }),
  add_left_neg := λ p, begin
    obtain ⟨⟨m, s⟩, rfl : mk m s = p⟩ := quotient.exists_rep p,
    change (mk m s).lift_on (λ x, mk (-x.1) x.2)
      (λ ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨u, hu⟩, by { rw mk_eq, exact ⟨u, by simpa⟩ }) + mk m s = 0,
    rw [lift_on_mk, mk_add_mk],
    simp
  end,
  ..(show add_comm_monoid (localized_module S M), by apply_instance)
}

instance {S : submonoid R} : is_scalar_tower R (localization S) (localized_module S M) :=
begin
  constructor,
  intros x y z,
  obtain ⟨⟨m, s⟩, rfl : localized_module.mk m s = z⟩ := quotient.exists_rep z,
  obtain ⟨r, t, rfl⟩ := is_localization.mk'_surjective S y,
  rw [algebra.smul_def, ← @is_localization.mk'_one _ _ S (localization S),
    ← is_localization.mk'_mul, ← localization.mk_eq_mk', localized_module.mk_smul_mk,
    localized_module.mk_smul_mk, localized_module.smul'_mk, mul_smul, one_mul],
end

end

include M

def module.support : set (ideal R) :=
{ I | ∃ h : I.is_prime, by exactI nontrivial (localized_module I.prime_compl M) }

omit M

lemma localized_module_nontrival_iff (S : submonoid R) :
  nontrivial (localized_module S M) ↔ ∃ x : M, disjoint (S : set R) (R ∙ x).annihilator :=
begin
  rw [nontrivial_iff_exists_ne (localized_module.mk (0 : M) (1 : S))],
  erw (@quotient.surjective_quotient_mk' _ (localized_module.r.setoid S M)).exists,
  simp_rw [prod.exists, ← set.subset_compl_iff_disjoint_right],
  change (∃ (a : M) (b : S), localized_module.mk a b ≠ _) ↔
    ∃ x : M, ∀ y : R, y ∈ S → y ∉ (R ∙ x).annihilator,
  simp_rw [ne.def, localized_module.mk_eq, not_exists, smul_zero, one_smul,
    submodule.mem_annihilator_span_singleton, eq_comm],
  exact ⟨λ ⟨a, _, h⟩, ⟨a, λ y hy, h ⟨y, hy⟩⟩, λ ⟨a, h⟩, ⟨a, 1, λ y, h y y.2⟩⟩
end


lemma localized_module_nontrival (M : submonoid R) :
  nontrivial (localized_module M A) ↔ disjoint (M : set R) (algebra_map R A).ker :=
begin
  split,
  { rintros ⟨a, b, e⟩ x ⟨h₁, h₂ : algebra_map R A x = 0⟩,
    apply e,
    obtain ⟨⟨a₁, a₂⟩, rfl : localized_module.mk a₁ a₂ = a⟩ := quotient.exists_rep a,
    obtain ⟨⟨b₁, b₂⟩, rfl : localized_module.mk b₁ b₂ = b⟩ := quotient.exists_rep b,
    rw [localized_module.mk_eq],
    use ⟨x, h₁⟩,
    simp [submonoid.smul_def, algebra.smul_def, h₂] },
  { intro H,
    refine ⟨⟨localized_module.mk 0 1, localized_module.mk 1 1, _⟩⟩,
    rw [ne.def, localized_module.mk_eq],
    suffices : ∀ x : M, algebra_map R A x ≠ 0,
    { simpa [submonoid.smul_def, ← algebra.algebra_map_eq_smul_one] },
    intros x e, cases H ⟨x.prop, e⟩ },
end

lemma module.support_eq_of_algebra :
  module.support R A = { I | (algebra_map R A).ker ≤ I ∧ I.is_prime } :=
begin
  ext,
  simp [module.support, localized_module_nontrival, ideal.prime_compl,
    set.disjoint_compl_left_iff_subset, and_comm],
end

variables {R M}

lemma module.mem_support_iff {I : ideal R} [hI : I.is_prime] :
  I ∈ module.support R M ↔ nontrivial (localized_module I.prime_compl M) :=
⟨Exists.some_spec, Exists.intro hI⟩

lemma module.mem_support_iff_exists_of_is_prime {I : ideal R} [hI : I.is_prime] :
  I ∈ module.support R M ↔ ∃ x : M, (R ∙ x).annihilator ≤ I :=
begin
  rw [module.mem_support_iff, localized_module_nontrival_iff],
  apply exists_congr,
  intro x, exact set.disjoint_compl_left_iff_subset,
end

lemma module.mem_support_iff_exists {I : ideal R} :
  I ∈ module.support R M ↔ I.is_prime ∧ ∃ x : M, (R ∙ x).annihilator ≤ I :=
begin
  refine ⟨λ h, _, λ ⟨_, h⟩, by exactI module.mem_support_iff_exists_of_is_prime.mpr h⟩,
  haveI := h.some,
  rw module.mem_support_iff_exists_of_is_prime at h,
  exact ⟨infer_instance, h⟩
end

variables (R M)

lemma module.support_eq_exists :
  module.support R M = { I | I.is_prime ∧ ∃ x : M, (R ∙ x).annihilator ≤ I } :=
set.ext (λ I, module.mem_support_iff_exists)

variables {R M}

lemma module.exists_annihilator_le_of_mem_support (I ∈ module.support R M) :
  ∃ x : M, (R ∙ x).annihilator ≤ I :=
(module.mem_support_iff_exists.mp H).2

lemma module.mem_support_of_le {I J : ideal R} (h : I ≤ J) (hI : I ∈ module.support R M)
  [hJ : J.is_prime] :
  J ∈ module.support R M :=
begin
  haveI := hI.some,
  rw module.mem_support_iff_exists_of_is_prime at hI ⊢,
  exact exists_imp_exists (λ a, ge_trans h) hI
end

lemma module.annihilator_le_of_mem_support (I ∈ module.support R M) :
  (⊤ : submodule R M).annihilator ≤ I :=
(submodule.annihilator_mono le_top).trans
  (module.exists_annihilator_le_of_mem_support I H).some_spec

lemma module.mem_support_iff_annihilator_le_of_fg (I : ideal R) [I.is_prime]
  [hM : module.finite R M] :
  I ∈ module.support R M ↔ (⊤ : submodule R M).annihilator ≤ I :=
begin
  refine ⟨module.annihilator_le_of_mem_support I,
    λ e, module.mem_support_iff_exists_of_is_prime.mpr _⟩,
  change ∃ x : M, ∀ y : R, y ∈ _ → y ∈ I,
  simp_rw submodule.mem_annihilator_span_singleton,
  by_contra h,
  push_neg at h,
  choose y h₁ h₂ using h,
  obtain ⟨S, hS⟩ := hM.1,
  have : S.prod y ∈ I.prime_compl := prod_mem (λ c _, h₂ c),
  apply this,
  apply e,
  rw [← hS, submodule.mem_annihilator_span],
  rintro ⟨s, hs⟩,
  obtain ⟨z, e⟩ : y s ∣ S.prod y := finset.dvd_prod_of_mem _ hs,
  rw [e, subtype.coe_mk, mul_comm, mul_smul, h₁, smul_zero],
end

variables (R M)

lemma module.support_eq_of_fg
  [hM : module.finite R M] :
  module.support R M = { I | (⊤ : submodule R M).annihilator ≤ I ∧ I.is_prime } :=
begin
  ext I,
  have : ∀ {p q}, (p ∨ q → (p ↔ q)) → (p ↔ q) := by tauto!,
  refine this (λ H, _),
  haveI : I.is_prime := H.elim Exists.some and.right,
  rw module.mem_support_iff_annihilator_le_of_fg,
  exact (and_iff_left infer_instance).symm
end

lemma module.support_nonempty_iff :
  (module.support R M).nonempty ↔ nontrivial M :=
begin
  rw [module.support_eq_exists, nontrivial_iff_exists_ne (0 : M)],
  split, swap,
  { rintro ⟨a, ha⟩,
    obtain ⟨M, h₁, h₂⟩ := ideal.exists_le_maximal _ ((R ∙ a).annihilator.ne_top_iff_one.mpr _),
    { exactI ⟨M, infer_instance, _, h₂⟩ },
    rwa [submodule.mem_annihilator_span_singleton, one_smul] },
  { rintro ⟨I, hI, x, hx⟩,
    have := hx.trans_lt (lt_top_iff_ne_top.mpr hI.1),
    rw [lt_top_iff_ne_top, ideal.ne_top_iff_one, submodule.mem_annihilator_span_singleton,
      one_smul] at this,
    exact ⟨x, this⟩ }
end

lemma module.support_eq_empty_iff :
  module.support R M = ∅ ↔ subsingleton M :=
begin
  rw [← set.not_nonempty_iff_eq_empty, ← not_nontrivial_iff_subsingleton, not_iff_not,
    module.support_nonempty_iff],
end

lemma module.support_nonempty [h : nontrivial M] : (module.support R M).nonempty :=
(module.support_nonempty_iff R M).mpr h

lemma module.support_eq_nempty [h : subsingleton M] : module.support R M = ∅ :=
(module.support_eq_empty_iff R M).mpr h

variables {R}

def module.is_locally_nilpotent (r : R) (M : Type*) [add_comm_group M] [module R M] : Prop :=
∀ m : M, ∃ n : ℕ, r ^ n • m = 0

variables (R)

lemma module.mem_Inf_support_tfae (x : R) :
  tfae [subsingleton (localized_module (submonoid.powers x) M),
    module.is_locally_nilpotent x M,
    x ∈ Inf (module.support R M)] :=
begin
  tfae_have : 1 → 2,
  { rw [← not_nontrivial_iff_subsingleton, localized_module_nontrival_iff],
    simp_rw [← set.subset_compl_iff_disjoint_left, set.subset_def],
    dsimp,
    simp_rw submodule.mem_annihilator_span_singleton,
    push_neg,
    apply forall_imp,
    rintros m ⟨_, hn, ⟨n, rfl⟩⟩, exact ⟨n, hn⟩ },
  tfae_have : 2 → 3,
  { simp_rw [ideal.mem_Inf, module.mem_support_iff_exists],
    rintros H I ⟨hI, a, ha⟩,
    obtain ⟨n, hn⟩ := H a,
    cases (zero_le n).lt_or_eq,
    { rw ← hI.pow_mem_iff_mem n h, apply ha, rwa submodule.mem_annihilator_span_singleton },
    { subst h, rw [pow_zero, one_smul] at hn, subst hn, apply ha,
      rw submodule.mem_annihilator_span_singleton, rw smul_zero } },
  tfae_have : 3 → 1,
  { rw [← not_nontrivial_iff_subsingleton, ideal.mem_Inf],
    introsI H inst,
    obtain ⟨I, hI⟩ := (module.support_nonempty_iff (localization.away x) _).mpr inst,
    haveI := hI.some,
    apply hI.some.1,
    refine ideal.eq_top_of_is_unit_mem _ _
      (is_localization.map_units _ ⟨x, submonoid.mem_powers x⟩),
    rw ← ideal.mem_comap,
    apply H,
    rw module.mem_support_iff_exists_of_is_prime at hI ⊢,
    obtain ⟨y, hy⟩ := hI,
    obtain ⟨⟨m, s⟩, rfl : localized_module.mk m s = y⟩ := quotient.exists_rep y,
    refine ⟨m, le_trans _ (ideal.comap_mono hy)⟩,
    intros z hz,
    rw submodule.mem_annihilator_span_singleton at hz,
    rw [ideal.mem_comap, submodule.mem_annihilator_span_singleton,
      algebra_map_smul, localized_module.smul'_mk, hz, localized_module.zero_mk] },
  tfae_finish
end

variables {R M}

lemma module.mem_Inf_support_iff_locally_nilpotent {x : R} :
  x ∈ Inf (module.support R M) ↔ module.is_locally_nilpotent x M :=
(module.mem_Inf_support_tfae R M x).out 2 1

lemma module.Inf_support_eq_annihilator_radical [h : module.finite R M] :
  Inf (module.support R M) = (⊤ : submodule R M).annihilator.radical :=
begin
  rw [ideal.radical_eq_Inf, module.support_eq_of_fg]
end

lemma module.is_locally_nilpotent_iff_mem_radical [module.finite R M] (x : R) :
  module.is_locally_nilpotent x M ↔ x ∈ (⊤ : submodule R M).annihilator.radical :=
by rw [← module.mem_Inf_support_iff_locally_nilpotent, module.Inf_support_eq_annihilator_radical]

lemma module.is_locally_nilpotent_of_algebra {x : R} :
  module.is_locally_nilpotent x A ↔ x ∈ (algebra_map R A).ker.radical :=
by rw [ideal.radical_eq_Inf, ← module.mem_Inf_support_iff_locally_nilpotent,
  module.support_eq_of_algebra]
