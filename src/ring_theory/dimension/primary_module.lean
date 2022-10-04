import ring_theory.ideal.operations
import ring_theory.dimension.associate_prime


section

variables {R M A : Type*} [comm_ring R] [add_comm_group M] [module R M] [comm_ring A] [algebra R A]

variables {p : submodule R M}

variables (R M)

def module.coprimary : Prop :=
is_compl ↑(module.non_zero_divisors R M) { r : R | module.is_locally_nilpotent r M }

variables {R M}

namespace module.coprimary

protected
lemma nontrivial (H : module.coprimary R M) : nontrivial M :=
begin
  by_contra h,
  haveI := not_nontrivial_iff_subsingleton.mp h,
  apply set.subset_compl_iff_disjoint_right.mpr H.1 (one_mem $ module.non_zero_divisors R M),
  intro r,
  exact ⟨0, subsingleton.elim _ _⟩
end

protected
lemma nontrivial' (H : module.coprimary R M) : nontrivial R :=
begin
  have := H.nontrivial,
  revert this,
  contrapose,
  simp_rw [not_nontrivial_iff_subsingleton],
  introI _,
  exact module.subsingleton R _
end

protected
lemma or (H : module.coprimary R M) (x : R) :
  x ∈ module.non_zero_divisors R M ∨ module.is_locally_nilpotent x M :=
begin
  have : x ∈ (⊤ : set R) := trivial,
  rwa ← H.sup_eq_top at this
end

protected
lemma iff :
  module.coprimary R M ↔ nontrivial M ∧
    ∀ x, x ∈ module.non_zero_divisors R M ∨ module.is_locally_nilpotent x M :=
begin
  refine ⟨λ h, ⟨h.nontrivial, h.or⟩, _⟩,
  rintros ⟨h₁, h₂⟩,
  constructor,
  { rw ← set.subset_compl_iff_disjoint_left,
    rintros r hr₁ (hr₂ : r ∈ module.non_zero_divisors R M),
    obtain ⟨x, hx⟩ := (nontrivial_iff_exists_ne 0).mp h₁,
    obtain ⟨n, hn⟩ := hr₁ x,
    exact hx (pow_mem hr₂ n _ hn) },
  { rw codisjoint_iff, ext, simpa using h₂ x }
end

protected
lemma iff' [h : nontrivial M] :
  module.coprimary R M ↔ ∀ x, x ∈ module.non_zero_divisors R M ∨ module.is_locally_nilpotent x M :=
begin
  rw [coprimary.iff, and_iff_right h],
end

lemma iff_of_algebra : module.coprimary R A ↔ nontrivial A ∧
  ∀ x, algebra_map R A x ∈ non_zero_divisors A ∨ algebra_map R A x ∈ nilradical A :=
begin
  rw coprimary.iff,
  refine and_congr iff.rfl (forall_congr (λ x, or_congr _ _)),
  { rw module.non_zero_divisors_of_algebra, refl },
  { rw [module.is_locally_nilpotent_of_algebra, nilradical, ← ideal.mem_comap,
      ideal.comap_radical], refl }
end

lemma iff_of_algebra' [h : nontrivial A] : module.coprimary R A ↔
  ∀ x, algebra_map R A x ∈ non_zero_divisors A ∨ algebra_map R A x ∈ nilradical A :=
begin
  rw [iff_of_algebra, and_iff_right h],
end

lemma self [h : nontrivial R] : module.coprimary R R ↔
  ∀ x, x ∈ non_zero_divisors R ∨ x ∈ nilradical R :=
begin
  rw [iff_of_algebra, and_iff_right h],
  refl
end

variables (R M)

protected
lemma tfae [is_noetherian_ring R] :
  tfae [module.coprimary R M,
    associated_primes R M = {Inf (associated_primes R M)},
    ∃ J, associated_primes R M = {J}] :=
begin
  tfae_have : 1 → 2,
  { intro e,
    haveI := e.nontrivial,
    rw set.eq_singleton_iff_nonempty_unique_mem,
    refine ⟨associated_primes_nonempty _ _, λ I H, le_antisymm _ (Inf_le H)⟩,
    show (I : set R) ⊆ ↑(Inf (associated_primes R M)),
    rw [module.coprimary, ← eq_compl_iff_is_compl, eq_compl_comm, ← Union_associated_primes] at e,
    rw [coe_Inf_associated_primes, e],
    exact set.subset_bUnion_of_mem H },
  tfae_have : 2 → 3,
  { exact λ h, ⟨_, h⟩ },
  tfae_have : 3 → 1,
  { rintro ⟨J, e⟩,
    rw [module.coprimary, ← eq_compl_iff_is_compl, eq_compl_comm, ← Union_associated_primes,
      ← coe_Inf_associated_primes, e],
    simp },
  tfae_finish
end

variables {R M}

lemma iff_singleton [is_noetherian_ring R] :
  module.coprimary R M ↔ ∃ J, associated_primes R M = {J} :=
(coprimary.tfae R M).out 0 2

lemma iff_associated_primes' [is_noetherian_ring R] :
  module.coprimary R M ↔ associated_primes R M = {Inf (associated_primes R M)} :=
(coprimary.tfae R M).out 0 1

lemma associated_primes_eq' [is_noetherian_ring R] (h : module.coprimary R M) :
  associated_primes R M = {Inf (associated_primes R M)} :=
iff_associated_primes'.mp h

lemma Inf_associated_primes_is_associated_prime [is_noetherian_ring R] (h : module.coprimary R M) :
  is_associated_prime (Inf (associated_primes R M)) M :=
by { rw ← mem_associate_primes, convert set.mem_singleton _, rwa ← iff_associated_primes' }

lemma Inf_associated_primes_is_prime [is_noetherian_ring R] (h : module.coprimary R M) :
  ideal.is_prime (Inf (associated_primes R M)) :=
h.Inf_associated_primes_is_associated_prime.1

lemma iff_associated_primes [is_noetherian_ring R] [module.finite R M] :
  module.coprimary R M ↔ associated_primes R M = {(⊤ : submodule R M).annihilator.radical} :=
by rw [iff_associated_primes', ← Inf_associated_primes_eq_annihilator_radical]

end module.coprimary

def submodule.is_primary (p : submodule R M) : Prop :=
module.coprimary R (M ⧸ p)

lemma submodule.quotient.subsingleton_iff : subsingleton (M ⧸ p) ↔ p = ⊤ :=
begin
  split,
  { introsI e, rw eq_top_iff, intros x hx, rw ← submodule.quotient.mk_eq_zero,
    exact subsingleton.elim _ _ },
  { rintro rfl, constructor, intros a b,
    obtain ⟨a, rfl⟩ := submodule.quotient.mk_surjective _ a,
    obtain ⟨b, rfl⟩ := submodule.quotient.mk_surjective _ b,
    rw submodule.quotient.eq,
    trivial }
end

lemma submodule.quotient.nontrivial_iff : nontrivial (M ⧸ p) ↔ p ≠ ⊤ :=
begin
  rw [ne.def, ← submodule.quotient.subsingleton_iff, ← not_nontrivial_iff_subsingleton, not_not],
end


lemma submodule.is_primary_iff {p : submodule R M} :
  p.is_primary ↔ p ≠ ⊤ ∧ ∀ (r : R) (m : M), r • m ∈ p → m ∈ p ∨ ∀ m' : M, ∃ n : ℕ, r ^ n • m' ∈ p :=
begin
  rw [submodule.is_primary, module.coprimary.iff],
  refine and_congr submodule.quotient.nontrivial_iff (forall_congr $ λ x, _),
  simp_rw [or_iff_not_imp_left, module.mem_non_zero_divisors, ← submodule.quotient.mk_eq_zero,
    submodule.quotient.mk_smul],
  push_neg,
  split,
  { rintros H m e e' m', apply H ⟨_, e, e'⟩ },
  { rintros H ⟨m, e, e'⟩ m',
    obtain ⟨m, rfl⟩ := submodule.quotient.mk_surjective _ m,
    obtain ⟨m', rfl⟩ := submodule.quotient.mk_surjective _ m',
    exact H m e e' m' },
end

lemma comap_nilradical {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S) :
  (nilradical S).comap f = f.ker.radical :=
ideal.comap_radical f 0

lemma ideal.submodule_is_primary_iff (I : ideal R) : submodule.is_primary I ↔ I.is_primary :=
begin
  by_cases I = ⊤,
  { have : ¬ submodule.is_primary I,
    { intro H, haveI := H.nontrivial, apply not_subsingleton (R ⧸ I), rw h, apply_instance },
    simpa [ideal.is_primary, h] },
  haveI := ideal.quotient.nontrivial h,
  rw [submodule.is_primary, module.coprimary.iff_of_algebra', ideal.is_primary, and_iff_right h],
  simp_rw [← ideal.mem_comap, comap_nilradical, ideal.quotient.algebra_map_eq, ideal.mk_ker,
    or_iff_not_imp_right, ← @ideal.quotient.eq_zero_iff_mem _ _ _ I],
  split,
  { intros H x y e hy, exact H y hy (ideal.quotient.mk I x) e },
  { intros H x hx y e, obtain ⟨y, rfl⟩ := ideal.quotient.mk_surjective y, exact (H e hx) }
end

lemma ideal.is_primary_iff_associated_primes [is_noetherian_ring R] {I : ideal R} :
  I.is_primary ↔ associated_primes R (R ⧸ I) = {I.radical} :=
begin
  rw [← ideal.submodule_is_primary_iff, submodule.is_primary,
    module.coprimary.iff_associated_primes, iff_iff_eq],
  congr,
  rw [submodule.top_annihilator_eq_ker],
  simp,
end

def inf_irreducible {α : Type*} [semilattice_inf α] (x : α) : Prop :=
∀ ⦃y z⦄, x = y ⊓ z → x = y ∨ x = z

lemma inf_irreducible_iff {α : Type*} [semilattice_inf α] (x : α) :
  inf_irreducible x ↔ ∀ y z, x ≤ y → x ≤ z → x = y ⊓ z → y ≤ x ∨ z ≤ x :=
forall₂_congr (λ y z, ⟨λ h _ _ e, or.imp eq.ge eq.ge (h e), λ h e, by simpa [e] using h⟩)

lemma module.coprimary_of_inf_irreducible [nontrivial M] [is_noetherian R M]
  (h : inf_irreducible (⊥ : submodule R M)) : module.coprimary R M :=
begin
  rw module.coprimary.iff',
  intro x,
  rw module.is_locally_nilpotent_iff_mem_radical,
  obtain ⟨n, hn, H⟩ := is_noetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot
    (algebra_map R (module.End R M) x),
  cases h H.symm with h h,
  { refine or.inl (λ m hm, (_ : m ∈ (⊥ : submodule R M))),
    rw [h, ← map_pow, ← tsub_add_cancel_of_le (nat.one_le_iff_ne_zero.mpr hn), pow_add, pow_one],
    show _ • m = 0, rw [mul_smul, hm, smul_zero] },
  { refine or.inr ⟨n, _⟩,
    rw [submodule.mem_annihilator', ← submodule.map_le_iff_le_comap, ← eq_bot_iff, h,
      linear_map.range_eq_map, ← map_pow, algebra.algebra_map_eq_smul_one],
    refl }
end

lemma submodule.is_primary_of_inf_irreducible [is_noetherian R M]
  (h : inf_irreducible p) (h' : p ≠ ⊤) : p.is_primary :=
begin
  haveI : nontrivial (M ⧸ p) := submodule.quotient.nontrivial_iff.mpr h',
  apply module.coprimary_of_inf_irreducible,
  intros x y e,
  simp_rw [← (submodule.comap_injective_of_surjective p.mkq_surjective).eq_iff,
    submodule.comap_bot, p.ker_mkq],
  apply h,
  rw [← submodule.comap_inf, ← e, submodule.comap_bot, p.ker_mkq],
end

lemma exists_inf_irreducibles_inter {α : Type*} [semilattice_inf α] [order_top α]
  [well_founded_gt α] (a : α) (h : a ≠ ⊤) :
  ∃ s : finset α, s.inf id = a ∧ ∀ x ∈ s, x ≠ ⊤ ∧ inf_irreducible x :=
begin
  classical,
  revert h,
  apply well_founded_gt.induction a; clear a,
  intros x H hx,
  by_cases inf_irreducible x,
  { refine ⟨{x}, finset.inf_singleton, λ x' e, _⟩, rw finset.mem_singleton.mp e, exact ⟨hx, h⟩ },
  delta inf_irreducible at h,
  push_neg at h,
  obtain ⟨y, z, rfl, ey, ez⟩ := h,
  obtain ⟨s, hs₁, hs₂⟩ := H y (lt_of_le_of_ne inf_le_left ey) (λ e, by simpa [e] using ez),
  obtain ⟨t, ht₁, ht₂⟩ := H z (lt_of_le_of_ne inf_le_right ez) (λ e, by simpa [e] using ey),
  exact ⟨s ∪ t, by rw [finset.inf_union, hs₁, ht₁],
    λ x, by simpa [or_imp_distrib] using and.intro (hs₂ x) (ht₂ x)⟩
end




end
