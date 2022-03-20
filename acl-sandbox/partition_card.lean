import data.setoid.partition
import algebra.big_operators.order

open_locale big_operators classical

section partition

variables {α : Type*}

/-- The cardinal of ambient fintype equals
  the sum of cardinals of the parts of a partition (finset style)-/
lemma partition.card_of_partition' [fintype α] {c : finset (finset α)}
  (hc : setoid.is_partition
    ({ s : set α | ∃ (t : finset α), s.to_finset = t ∧ t ∈ c } : set (set α))) :
  ∑ (s : finset α) in c, s.card = fintype.card α :=
begin
  rw [← mul_one (fintype.card α), ← finset.sum_card],
  intro a,
  rw finset.card_eq_one,
  obtain ⟨s, hs, hs'⟩ := hc.right a,
  simp only [exists_unique_iff_exists, exists_prop, and_imp, exists_eq_left', set.mem_set_of_eq]
    at hs hs',
  have hs'2 : ∀ (z : finset α), z ∈ c → a ∈ z → z = s.to_finset,
  { intros z hz ha,
    rw [← finset.coe_inj, set.coe_to_finset],
    refine  hs' z _ (finset.mem_coe.mpr ha),
  -- To get the correct type automatically and perform the rewrite
    suffices : ∀ {u v : finset α}, v ∈ c → u = v → u ∈ c,
    { refine this hz _,
      rw [← finset.coe_inj, set.coe_to_finset] },
    { intros u v hu huv, rw huv, exact hu },
  },
  use s.to_finset,
  ext t,
  simp only [finset.mem_filter, finset.mem_singleton],
  split,
  { rintro ⟨ht,ha⟩,
    exact hs'2 t ht ha },
  { intro ht,
    rw ← ht at hs, apply and.intro hs.left,
    rw ht, simp only [set.mem_to_finset],  exact hs.right,}
end

/-- The cardinal of ambient fintype equals
  the sum of cardinals of the parts of a partition (set style)-/
lemma partition.card_of_partition [fintype α] {c : set (set α)} (hc : setoid.is_partition c) :
  ∑ (s : set α) in c.to_finset, s.to_finset.card = fintype.card α :=
begin
  let c' : finset (finset α) := { s : finset (α) | (s : set α) ∈ c }.to_finset,
  have hcc' : c = { s : set α | ∃ (t : finset α), s.to_finset = t ∧ t ∈ c' },
  { simp only [set.mem_to_finset, set.mem_set_of_eq, exists_eq_left',
      set.coe_to_finset, set.set_of_mem_eq] },
  rw hcc' at hc,
  rw ← partition.card_of_partition'  hc,
  have hi : ∀ (a : set α) (ha : a ∈ c.to_finset), a.to_finset ∈ c',
  { intros a ha,
    simp only [set.mem_to_finset, set.mem_set_of_eq, set.coe_to_finset],
    simpa only [set.mem_to_finset] using ha,  },
  have hj : ∀ (a : finset α) (ha : a ∈ c'), (a : set α) ∈ c.to_finset,
  { intros a ha, simpa only [set.mem_to_finset] using ha },
  rw finset.sum_bij' _ hi _ _ hj,
  { intros a ha, simp only [set.coe_to_finset],  },
  { intros a ha, rw [← finset.coe_inj, set.coe_to_finset] },
  { intros a ha, refl },
end

-- TODO : remove the finiteness assumption on α and put it on s
/-- Given a partition of the ambient finite type,
the cardinal of a set is the sum of the cardinalities of its trace on the parts of the partition -/
lemma setoid.is_partition.card_set_eq_sum_parts {α : Type*} [fintype α] (s : set α)
  {P : set (set α)} (hP : setoid.is_partition P) :
  s.to_finset.card =
    finset.sum P.to_finset (λ (t : set α), (s ∩ t).to_finset.card) :=
begin
  rw ← finset.card_bUnion,
  apply congr_arg,
  { rw ← finset.coe_inj,
    simp only [set.coe_to_finset, finset.coe_bUnion],
    rw [set.bUnion_eq_Union, ← set.inter_Union, ← set.sUnion_eq_Union],
    rw setoid.is_partition.sUnion_eq_univ hP,
    exact (set.inter_univ s).symm },
  { intros t ht u hu htu,
    simp only [set.mem_to_finset] at ht hu,
    simp only [set.to_finset_disjoint_iff],
    exact set.disjoint_of_subset (set.inter_subset_right s t) (set.inter_subset_right s u)
      (setoid.is_partition.pairwise_disjoint hP ht hu htu) }
end

/-- The cardinality of a finite type is
  the sum of the cardinalities of the parts of any partition -/
lemma setoid.is_partition.card_eq_sum_parts {α : Type*} [fintype α] {P : set (set α)}
  (hP : setoid.is_partition P) :
  fintype.card α =
    finset.sum P.to_finset (λ (t : set α), t.to_finset.card) :=
begin
  change finset.univ.card = _,
  have : ∀ (t : set α) (ht : t ∈ P.to_finset), t.to_finset.card = (set.univ ∩ t).to_finset.card,
  { intros t ht, apply congr_arg,
    rw set.to_finset_inj, exact (set.univ_inter t).symm,  },
  simp_rw finset.sum_congr rfl this,
  simpa only [set.to_finset_univ, set.to_finset_card, fintype.card_of_finset]
    using setoid.is_partition.card_set_eq_sum_parts (set.univ) hP,
end

end partition
