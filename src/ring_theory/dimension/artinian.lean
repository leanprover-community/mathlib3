import ring_theory.artinian

variables (R : Type*) [comm_ring R]

lemma is_artinian_ring.is_field_of_is_domain [is_artinian_ring R] [h : nontrivial R] [is_domain R] :
  is_field R :=
begin
  refine ⟨h.1, mul_comm, _⟩,
  intros x hx,
  obtain ⟨n, y, hy⟩ := is_artinian.exists_pow_succ_smul_dvd x (1 : R),
  replace hy : x ^ n * (x * y - 1) = 0,
  { rw [mul_sub, sub_eq_zero], convert hy using 1, simp [nat.succ_eq_add_one, pow_add, mul_assoc] },
  rw [mul_eq_zero, sub_eq_zero] at hy,
  exact ⟨_, hy.resolve_left $ pow_ne_zero _ hx⟩
end

variables {R}

lemma is_artinian_ring.is_maximal_of_is_prime [is_artinian_ring R]
  (I : ideal R) [h : I.is_prime] : I.is_maximal :=
begin
  rw ← ideal.quotient.is_domain_iff_prime at h,
  rw ideal.quotient.maximal_ideal_iff_is_field_quotient,
  haveI : is_artinian_ring (R ⧸ I) :=
    function.surjective.is_artinian_ring ideal.quotient.mk_surjective,
  apply is_artinian_ring.is_field_of_is_domain,
end

lemma is_artinian_ring.is_maximal_iff_is_prime [is_artinian_ring R] (I : ideal R) :
  I.is_maximal ↔ I.is_prime :=
⟨ideal.is_maximal.is_prime, @@is_artinian_ring.is_maximal_of_is_prime _ _ I⟩

lemma is_artinian_ring.jacobson_eq_radical [is_artinian_ring R] (I : ideal R) :
  I.jacobson = I.radical :=
by simp_rw [ideal.jacobson, ideal.radical_eq_Inf, is_artinian_ring.is_maximal_iff_is_prime]

variables (R)

lemma is_artinian_ring.jacobson_eq_nilradical [is_artinian_ring R] :
  (⊥ : ideal R).jacobson = nilradical R :=
is_artinian_ring.jacobson_eq_radical _

lemma is_artinian_ring.is_nilpotent_nilradical [is_artinian_ring R] :
  is_nilpotent (nilradical R) :=
is_artinian_ring.jacobson_eq_nilradical R ▸ is_artinian_ring.is_nilpotent_jacobson_bot

variables {R}

lemma ideal.is_prime.inf_le_iff (I : ideal R) [hI : I.is_prime] (s : set (ideal R)) (hs : s.finite) :
  Inf s ≤ I ↔ ∃ J ∈ s, J ≤ I :=
begin
  refine ⟨_, λ ⟨J, H, e⟩, (Inf_le H).trans e⟩,
  apply set.finite.induction_on hs; clear hs s,
  { intro e, rw [Inf_empty, ← eq_top_iff] at e, exact ((hI.1 : _) e).elim },
  { intros J s h₁ hs H e,
    rw Inf_insert at e,
    by_cases Inf s ≤ I, { obtain ⟨K, hK, hK'⟩ := H h, exact ⟨K, set.mem_insert_of_mem _ hK, hK'⟩ },
    suffices : J ≤ I, { exact ⟨J, set.mem_insert _ _, this⟩ },
    change ¬ ∀ x ∈ Inf s, x ∈ I at h,
    push_neg at h,
    obtain ⟨x, hx, hx'⟩ := h,
    intros y hy,
    have := e (ideal.mul_le_inf (ideal.mul_mem_mul hy hx)),
    rw hI.mul_mem_iff_mem_or_mem at this,
    exact this.resolve_right hx' }
end

lemma ideal.is_prime.mem_of_Inf_eq (I : ideal R) [hI : I.is_prime]
  (s : set (ideal R)) (hs : s.finite) (H : Inf s = I) : I ∈ s :=
begin
  obtain ⟨J, hJ, e⟩ := (ideal.is_prime.inf_le_iff I s hs).mp H.le,
  exact e.antisymm (H.symm.trans_le $ Inf_le hJ) ▸ hJ
end

variables (R)

lemma is_artinian_ring.is_maximal_finite [H : is_artinian_ring R] :
  (set_of ideal.is_maximal : set $ ideal R).finite :=
begin
  nontriviality R,
  let S : set (ideal R) :=
  { J | ∃ s : set (ideal R), s.finite ∧ (∀ I ∈ s, ideal.is_maximal I) ∧ J = Inf s },
  obtain ⟨M, hM⟩ := ideal.exists_maximal R,
  have : S.nonempty := ⟨M, {M}, set.to_finite _, λ _ e, e.symm ▸ hM, Inf_singleton.symm⟩,
  obtain ⟨_, ⟨s, hs, hs', rfl⟩, h⟩ := set_has_minimal_iff_artinian.mpr H S this,
  convert hs,
  ext J,
  refine ⟨λ hJ, _, hs' J⟩,
  haveI : J.is_maximal := hJ,
  have : Inf s ≤ J,
  { rw [← inf_eq_right, ← Inf_insert],
    refine h _ ⟨_, hs.insert _, _, rfl⟩ (Inf_le_Inf $ set.subset_insert _ _),
    unfreezingI { rintros I (rfl|H') }, { apply_instance }, { exact hs' _ H' } },
  obtain ⟨M, hM, hM'⟩ := (ideal.is_prime.inf_le_iff J s hs).mp this,
  exact (hs' M hM).eq_of_le hJ.ne_top hM' ▸ hM,
end

lemma is_artinian_ring.is_prime_finite [H : is_artinian_ring R] :
  (set_of ideal.is_prime : set $ ideal R).finite :=
begin
  convert is_artinian_ring.is_maximal_finite R,
  ext,
  rw is_artinian_ring.is_maximal_iff_is_prime,
end
