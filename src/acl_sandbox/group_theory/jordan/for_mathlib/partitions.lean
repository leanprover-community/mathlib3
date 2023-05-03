/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import data.setoid.partition
import algebra.big_operators.order
import data.finite.card
/-!

# Four lemmas on partitions

We provide four lemmas regarding `setoid.is_partition`

* `setoid.is_partition_on` proves that a partition of a type induces
a partition on each of its sets

The three other lemmas show that given a partition of a fintype, its cardinality
is the sum of the cardinalities of its parts, in three different contexts:

* `partition.card_of_partition` : for a fintype
* `partition.card_of_partition'` : for an ambient fintype, with a stronger hypothesis
that the partition is a finset of finsets
* `setoid.is_partition.card_set_eq_sum_parts` : for any finset of a type

## TODO

I am not sure that `partition.card_of_partition'` is useful per se,
but I use it to prove the other two.

-/

variables {α : Type*}

open_locale big_operators

/-- A partion of a type induces partitions on subsets -/
lemma setoid.is_partition_on {α : Type*} {P : set (set α)} (hP : setoid.is_partition P) (s : set α) :
  setoid.is_partition { u : set ↥s | ∃ (t : set α), t ∈ P ∧ coe ⁻¹' t = u ∧ t ∩ s ≠ ∅ } :=
begin
  split,
  { intro h ,
    obtain ⟨t, htP, ht, hts⟩ := set.mem_set_of_eq.mp h,
    apply hts,
    rw [← subtype.image_preimage_coe, ht,set.image_empty] },
  { intro a,
    obtain ⟨t, ht⟩ := hP.right ↑a,
    simp only [exists_unique_iff_exists, exists_prop, and_imp] at ht,
    use coe ⁻¹' t,
    split,
    { simp only [ne.def, set.mem_set_of_eq, set.mem_preimage, exists_unique_iff_exists, exists_prop],
      use t,
      apply and.intro ht.left.left,
      apply and.intro rfl,
      intro h, rw ← set.mem_empty_iff_false (a : α), rw ← h,
      exact set.mem_inter (ht.left.right) (subtype.mem a),
      exact (ht.left.right) },
    { simp only [ne.def, set.mem_set_of_eq, exists_unique_iff_exists, exists_prop, and_imp,
        forall_exists_index],
      intros y x hxP hxy hxs hay, rw ← hxy,
      rw subtype.preimage_coe_eq_preimage_coe_iff ,
      refine congr_arg2 _ _ rfl,
      apply ht.right x hxP, rw [← set.mem_preimage, hxy], exact hay } }
end

open_locale classical

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

/-- Given a partition of the ambient finite type,
the cardinal of a set is the sum of the cardinalities of its trace on the parts of the partition -/
lemma setoid.is_partition.card_set_eq_sum_parts {α : Type*} [fintype α] (s : set α)
  {P : set (set α)} (hP : setoid.is_partition P) :
  s.to_finset.card =
    finset.sum P.to_finset (λ (t : set α), (s ∩ t).to_finset.card) :=
begin
  rw ← finset.card_bUnion,
  apply congr_arg,
  { rw ← finset.coe_inj, simp only [set.coe_to_finset, finset.coe_bUnion],
    rw [set.bUnion_eq_Union, ← set.inter_Union, ← set.sUnion_eq_Union],
    rw setoid.is_partition.sUnion_eq_univ hP,
    exact (set.inter_univ s).symm },
  { intros t ht u hu htu,
    simp only [set.mem_to_finset] at ht hu,
    simp only [←finset.disjoint_coe, set.coe_to_finset],
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

  simpa only [set.to_finset_card, fintype.card_of_finset, finset.filter_congr_decidable,
    set.to_finset_univ] using setoid.is_partition.card_set_eq_sum_parts set.univ hP
end

/-- The cardinality of a finset is the sum of the cardinalities
of the traces of any partition of the ambient type  -/
lemma setoid.is_partition.card_finset_eq_sum_parts {α : Type*}
  {P : set (set α)} (hP : setoid.is_partition P)
  {s : finset α}  :
  let P' := { u : set ↥s | ∃ (t : set α), t ∈ P ∧ coe ⁻¹' t = u ∧ t ∩ s ≠ ∅ } in
  let hP' := setoid.is_partition_on hP in
  s.card =
    finset.sum P'.to_finset (λ (t : set ↥s), t.to_finset.card) :=
begin
  -- let P' := { u : set ↥s | ∃ (t : set α), t ∈ P ∧ coe ⁻¹' t = u ∧ t ∩ s ≠ ∅ },
  -- let hP' := setoid.is_partition_on hP,
/-   have fs : fintype ↥(↑s : set α) := finset_coe.fintype s,
  have fcs : fintype.card ↥s =  fintype.card ↥(s : set α) :=
  by simp only [fintype.card_coe, finset.coe_sort_coe, fintype.card_coe],
  have fcs' : fintype.card ↥(s : set α) = s.card :=
  by simp only [finset.coe_sort_coe, fintype.card_coe],
  -/
  have this :=
    @partition.card_of_partition _ (finset_coe.fintype s) _ (setoid.is_partition_on hP (s : set α)),
  simp only [finset.coe_sort_coe, fintype.card_coe] at this,
  rw ← this,
  apply congr_arg2,
  { apply finset.coe_injective ,
    simp only [ne.def, set.coe_to_finset],
    exact rfl },
  { ext, apply congr_arg, rw set.to_finset_inj }
end

/-
noncomputable def setoid.quotient_equiv {α β : Type*} {s : setoid α} (f : α → β)
  (hf : ∀ x y, s.rel x y ↔ f x = f y) (hf' : f.surjective) : quotient s ≃ β :=
begin
  refine equiv.of_bijective (λ q, q.lift_on' f (λ x y h, (hf x y).mp h)) _,
  split,
  -- injective
  intros x y,
  obtain ⟨a, rfl⟩:= quotient.exists_rep x,
  obtain ⟨b, rfl⟩:= quotient.exists_rep y,
  exact λ h, quotient.eq.mpr ((hf a b).mpr h),
  -- surjective
  exact (quotient.surjective_lift_on' (λ x y, (hf x y).mp)).mpr hf',
end

noncomputable def setoid.is_partition_equiv_quotient {α : Type*}
  {c : set (set α)} (hc : setoid.is_partition c) :
  quotient (setoid.mk_classes c hc.2) ≃ c :=
begin
  apply setoid.quotient_equiv (λ a, (⟨_, @setoid.eqv_class_mem _ c hc.2 a⟩ : c)),
  { intros x y,
    exact ⟨
      λ h,  subtype.ext ( set.ext ( λ z, ⟨λ h', setoid.trans' _ h' h, λ h', setoid.trans' _ h' (setoid.symm' _ h)⟩ )),
      λ hz,  (set.ext_iff.mp(subtype.ext_iff.mp hz) x).mp (setoid.refl' _ x), ⟩, },
  { -- surjective
    rintro ⟨u, hu⟩,
    have hu' : u.nonempty,
    { rw set.nonempty_iff_ne_empty,
      intro hu', apply hc.1,  rw ← hu', exact hu, },
    obtain ⟨a, ha⟩ := hu',
    use a,
    simp only [subtype.mk_eq_mk],
    rw setoid.eq_eqv_class_of_mem hc.2 hu ha, }
end

noncomputable def setoid.is_partition_equiv_quotient' {α : Type*}
  {c : set (set α)} (hc : setoid.is_partition c) :
  quotient (setoid.mk_classes c hc.2) ≃ c :=
begin
  -- Eric Wieser golfed this !
  let φ : quotient (setoid.mk_classes c hc.2) → c := λ q,  q.lift_on' (λ a, (⟨_, @setoid.eqv_class_mem _ c hc.2 a⟩ : c))
    (λ a b hab, subtype.ext $ set.ext $ λ x,
      ⟨λ h, setoid.trans' _ h hab, λ h, setoid.trans' _ h (setoid.symm' _ hab)⟩),
  apply equiv.of_bijective φ,

  let f : α → c := λ a, ⟨_, @setoid.eqv_class_mem _ c hc.2 a⟩,
  have hf : ∀ x y, f x = f y ↔ (setoid.mk_classes c hc.2).rel x y := λ x y, ⟨
    λ hz,  (set.ext_iff.mp(subtype.ext_iff.mp hz) x).mp (setoid.refl' _ x),
    λ h,  subtype.ext ( set.ext ( λ z, ⟨λ h', setoid.trans' _ h' h, λ h', setoid.trans' _ h' (setoid.symm' _ h)⟩ ))⟩,

/-
  have hf : ∀ x y, f x = f y ↔ (setoid.mk_classes c hc.2).rel x y,
  { intros x y,
--    simp only [f],
    simp only [subtype.mk_eq_mk, set.ext_iff, set.mem_set_of],
    split,
    intro hz,
    rw ← hz x, exact setoid.refl' _ _,
    intros h z,
    split,
    intro h', exact setoid.trans' _ h' h,
    intro h', exact setoid.trans' _ h' (setoid.symm' _ h), },
-/

/-
  let f : α → c := λ a, ⟨_, @setoid.eqv_class_mem _ c hc.2 a⟩,
  refine equiv.of_bijective (@quotient.lift _ _ (setoid.mk_classes c hc.2) f _) _,
  { -- well defined
    intros a b hab,
    change (setoid.mk_classes c hc.2).rel a b at hab,
    rw setoid.rel_iff_exists_classes at hab,
    rw setoid.classes_mk_classes at hab,
    obtain ⟨u, h, ha, hb⟩ := hab,
    let hc2 := hc.2,
    simp only [f, subtype.mk_eq_mk],
    rw ← setoid.eq_eqv_class_of_mem hc.2 h ha,
    rw ← setoid.eq_eqv_class_of_mem hc.2 h hb, }, -/

  split,
  { -- injective
    intros x y,
    obtain ⟨a, rfl⟩ := @quotient.exists_rep α (setoid.mk_classes c hc.2) x,
    obtain ⟨b, rfl⟩ := @quotient.exists_rep α (setoid.mk_classes c hc.2) y,
    simp only [quotient.lift_mk, φ, subtype.mk_eq_mk],
    intro hab,
    apply quotient.sound,
    change (setoid.mk_classes c hc.2).rel a b,
    rw setoid.rel_iff_exists_classes,
    use { x : α | (setoid.mk_classes c hc.2).rel x a},
    split,
    rw setoid.classes_mk_classes,
    apply setoid.eqv_class_mem,
    split,
    rw set.mem_set_of, apply setoid.refl' _ a,
    simp only [quotient.lift_on'_mk, subtype.mk_eq_mk] at hab,
    rw hab, rw set.mem_set_of, apply setoid.refl' _ b, },
  { -- surjective
    rw quotient.surjective_lift_on',
    rintro ⟨u, hu⟩,
    have hu' : u.nonempty,
    { rw set.nonempty_iff_ne_empty,
      intro hu', apply hc.1,  rw ← hu', exact hu, },
    obtain ⟨a, ha⟩ := hu',
    use a,
    simp only [subtype.mk_eq_mk],
    rw setoid.eq_eqv_class_of_mem hc.2 hu ha, }
end

-/
