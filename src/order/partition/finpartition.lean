/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.big_operators.basic
import order.atoms
import order.locally_finite
import order.sup_indep

/-!
# Finite partitions

In this file, we define finite partitions. A finpartition of `a : α` is a finite set of pairwise
disjoint parts `parts : finset α` which does not contain `⊥` and whose supremum is `a`.

Finpartitions of a finset are at the heart of Szemerédi's regularity lemma. They are also studied
purely order theoretically in Sperner theory.

## Constructions

We provide many ways to build finpartitions:
* `finpartition.of_erase`: Builds a finpartition by erasing `⊥` for you.
* `finpartition.of_subset`: Builds a finpartition from a subset of the parts of a previous
  finpartition.
* `finpartition.empty`: The empty finpartition of `⊥`.
* `finpartition.indiscrete`: The indiscrete, aka trivial, aka pure, finpartition made of a single
  part.
* `finpartition.discrete`: The discrete finpartition of `s : finset α` made of singletons.
* `finpartition.bind`: Puts together the finpartitions of the parts of a finpartition into a new
  finpartition.
* `finpartition.atomise`: Makes a finpartition of `s : finset α` by breaking `s` along all finsets
  in `F : finset (finset α)`. Two elements of `s` belong to the same part iff they belong to the
  same elements of `F`.

`finpartition.indiscrete` and `finpartition.bind` together form the monadic structure of
`finpartition`.

## Implementation notes

Forbidding `⊥` as a part follows mathematical tradition and is a pragmatic choice concerning
operations on `finpartition`. Not caring about `⊥` being a part or not breaks extensionality (it's
not because the parts of `P` and the parts of `Q` have the same elements that `P = Q`). Enforcing
`⊥` to be a part makes `finpartition.bind` uglier and doesn't rid us of the need of
`finpartition.of_erase`.

## TODO

Link `finpartition` and `setoid.is_partition`.

The order is the wrong way around to make `finpartition a` a graded order. Is it bad to depart from
the literature and turn the order around?
-/

open finset function
open_locale big_operators

variables {α : Type*}

/-- A finite partition of `a : α` is a pairwise disjoint finite set of elements whose supremum is
`a`. We forbid `⊥` as a part. -/
@[ext, derive decidable_eq] structure finpartition [lattice α] [order_bot α] (a : α) :=
(parts : finset α)
(sup_indep : parts.sup_indep id)
(sup_parts : parts.sup id = a)
(not_bot_mem : ⊥ ∉ parts)

attribute [protected] finpartition.sup_indep

namespace finpartition
section lattice
variables [lattice α] [order_bot α]

/-- A `finpartition` constructor which does not insist on `⊥` not being a part. -/
@[simps] def of_erase [decidable_eq α] {a : α} (parts : finset α)
  (sup_indep : parts.sup_indep id) (sup_parts : parts.sup id = a) :
  finpartition a :=
{ parts := parts.erase ⊥,
  sup_indep := sup_indep.subset (erase_subset _ _),
  sup_parts := (sup_erase_bot _).trans sup_parts,
  not_bot_mem := not_mem_erase _ _ }

/-- A `finpartition` constructor from a bigger existing finpartition. -/
@[simps] def of_subset {a b : α} (P : finpartition a) {parts : finset α}
  (subset : parts ⊆ P.parts) (sup_parts : parts.sup id = b) :
  finpartition b :=
{ parts := parts,
  sup_indep := P.sup_indep.subset subset,
  sup_parts := sup_parts,
  not_bot_mem := λ h, P.not_bot_mem (subset h) }

/-- Changes the type of a finpartition to an equal one. -/
@[simps] def copy {a b : α} (P : finpartition a) (h : a = b) : finpartition b :=
{ parts := P.parts,
  sup_indep := P.sup_indep,
  sup_parts := h ▸ P.sup_parts,
  not_bot_mem := P.not_bot_mem }

variables (α)

/-- The empty finpartition. -/
@[simps] protected def empty : finpartition (⊥ : α) :=
{ parts := ∅,
  sup_indep := sup_indep_empty _,
  sup_parts := finset.sup_empty,
  not_bot_mem := not_mem_empty ⊥ }

instance : inhabited (finpartition (⊥ : α)) := ⟨finpartition.empty α⟩

@[simp] lemma default_eq_empty : (default : finpartition (⊥ : α)) = finpartition.empty α := rfl

variables {α} {a : α}

/-- The finpartition in one part, aka indiscrete finpartition. -/
@[simps] def indiscrete (ha : a ≠ ⊥) : finpartition a :=
{ parts := {a},
  sup_indep := sup_indep_singleton _ _,
  sup_parts := finset.sup_singleton,
  not_bot_mem := λ h, ha (mem_singleton.1 h).symm }

variables (P : finpartition a)

protected lemma le {b : α} (hb : b ∈ P.parts) : b ≤ a := (le_sup hb).trans P.sup_parts.le

lemma ne_bot {b : α} (hb : b ∈ P.parts) : b ≠ ⊥ := λ h, P.not_bot_mem $ h.subst hb

protected lemma disjoint : (P.parts : set α).pairwise_disjoint id := P.sup_indep.pairwise_disjoint

variables {P}

lemma parts_eq_empty_iff : P.parts = ∅ ↔ a = ⊥ :=
begin
  simp_rw ←P.sup_parts,
  refine ⟨λ h, _, λ h, eq_empty_iff_forall_not_mem.2 (λ b hb, P.not_bot_mem _)⟩,
  { rw h,
    exact finset.sup_empty },
  { rwa ←le_bot_iff.1 ((le_sup hb).trans h.le) }
end

lemma parts_nonempty_iff : P.parts.nonempty ↔ a ≠ ⊥ :=
by rw [nonempty_iff_ne_empty, not_iff_not, parts_eq_empty_iff]

lemma parts_nonempty (P : finpartition a) (ha : a ≠ ⊥) : P.parts.nonempty := parts_nonempty_iff.2 ha

instance : unique (finpartition (⊥ : α)) :=
{ uniq := λ P,
    by { ext a, exact iff_of_false (λ h, P.ne_bot h $ le_bot_iff.1 $ P.le h) (not_mem_empty a) },
  ..finpartition.inhabited α }

/-- There's a unique partition of an atom. -/
@[reducible] -- See note [reducible non instances]
def _root_.is_atom.unique_finpartition (ha : is_atom a) : unique (finpartition a) :=
{ default := indiscrete ha.1,
  uniq := λ P, begin
    have h : ∀ b ∈ P.parts, b = a,
    { exact λ b hb, (eq_bot_or_eq_of_le_atom ha $ P.le hb).resolve_left (P.ne_bot hb) },
    ext b,
    refine iff.trans ⟨h b, _⟩ mem_singleton.symm,
    rintro rfl,
    obtain ⟨c, hc⟩ := P.parts_nonempty ha.1,
    simp_rw ←h c hc,
    exact hc,
  end }

instance [fintype α] [decidable_eq α] (a : α) :
  fintype (finpartition a) :=
@fintype.of_surjective {p : finset α // p.sup_indep id ∧ p.sup id = a ∧ ⊥ ∉ p} (finpartition a) _
  (subtype.fintype _) (λ i, ⟨i.1, i.2.1, i.2.2.1, i.2.2.2⟩) (λ ⟨_, y, z, w⟩, ⟨⟨_, y, z, w⟩, rfl⟩)

/-! ### Refinement order -/

section order

/-- We say that `P ≤ Q` if `P` refines `Q`: each part of `P` is less than some part of `Q`. -/
instance : has_le (finpartition a) := ⟨λ P Q, ∀ ⦃b⦄, b ∈ P.parts → ∃ c ∈ Q.parts, b ≤ c⟩

instance : partial_order (finpartition a) :=
{ le_refl := λ P b hb, ⟨b, hb, le_rfl⟩,
  le_trans := λ P Q R hPQ hQR b hb, begin
    obtain ⟨c, hc, hbc⟩ := hPQ hb,
    obtain ⟨d, hd, hcd⟩ := hQR hc,
    exact ⟨d, hd, hbc.trans hcd⟩,
  end,
  le_antisymm := λ P Q hPQ hQP, begin
    ext b,
    refine ⟨λ hb, _, λ hb, _⟩,
    { obtain ⟨c, hc, hbc⟩ := hPQ hb,
      obtain ⟨d, hd, hcd⟩ := hQP hc,
      rwa hbc.antisymm,
      rwa P.disjoint.eq_of_le hb hd (P.ne_bot hb) (hbc.trans hcd) },
    { obtain ⟨c, hc, hbc⟩ := hQP hb,
      obtain ⟨d, hd, hcd⟩ := hPQ hc,
      rwa hbc.antisymm,
      rwa Q.disjoint.eq_of_le hb hd (Q.ne_bot hb) (hbc.trans hcd) }
  end,
  ..finpartition.has_le }

instance [decidable (a = ⊥)] : order_top (finpartition a) :=
{ top := if ha : a = ⊥ then (finpartition.empty α).copy ha.symm else indiscrete ha,
  le_top := λ P,
  begin
    split_ifs,
    { intros x hx,
      simpa [h, P.ne_bot hx] using P.le hx },
    { exact λ b hb, ⟨a, mem_singleton_self _, P.le hb⟩ }
  end }

lemma parts_top_subset (a : α) [decidable (a = ⊥)] : (⊤ : finpartition a).parts ⊆ {a} :=
begin
  intros b hb,
  change b ∈ finpartition.parts (dite _ _ _) at hb,
  split_ifs at hb,
  { simp only [copy_parts, empty_parts, not_mem_empty] at hb,
    exact hb.elim },
  { exact hb }
end

lemma parts_top_subsingleton (a : α) [decidable (a = ⊥)] :
  ((⊤ : finpartition a).parts : set α).subsingleton :=
set.subsingleton_of_subset_singleton $ λ b hb, mem_singleton.1 $ parts_top_subset _ hb

end order
end lattice

section distrib_lattice
variables [distrib_lattice α] [order_bot α]

section inf
variables [decidable_eq α] {a b c : α}

instance : has_inf (finpartition a) :=
⟨λ P Q, of_erase ((P.parts.product Q.parts).image $ λ bc, bc.1 ⊓ bc.2)
  begin
    rw sup_indep_iff_disjoint_erase,
    simp only [mem_image, and_imp, exists_prop, forall_exists_index, id.def, prod.exists,
      mem_product, finset.disjoint_sup_right, mem_erase, ne.def],
    rintro _ x₁ y₁ hx₁ hy₁ rfl _ h x₂ y₂ hx₂ hy₂ rfl,
    rcases eq_or_ne x₁ x₂ with rfl | xdiff,
    { refine disjoint.mono inf_le_right inf_le_right (Q.disjoint hy₁ hy₂ _),
      intro t,
      simpa [t] using h },
    exact disjoint.mono inf_le_left inf_le_left (P.disjoint hx₁ hx₂ xdiff),
  end
  begin
    rw [sup_image, comp.left_id, sup_product_left],
    transitivity P.parts.sup id ⊓ Q.parts.sup id,
    { simp_rw [finset.sup_inf_distrib_right, finset.sup_inf_distrib_left],
      refl },
    { rw [P.sup_parts, Q.sup_parts, inf_idem] }
  end⟩

@[simp] lemma parts_inf (P Q : finpartition a) :
  (P ⊓ Q).parts = ((P.parts.product Q.parts).image $ λ bc : α × α, bc.1 ⊓ bc.2).erase ⊥ := rfl

instance : semilattice_inf (finpartition a) :=
{ inf_le_left := λ P Q b hb, begin
    obtain ⟨c, hc, rfl⟩ := mem_image.1 (mem_of_mem_erase hb),
    rw mem_product at hc,
    exact ⟨c.1, hc.1, inf_le_left⟩,
  end,
  inf_le_right := λ P Q b hb, begin
    obtain ⟨c, hc, rfl⟩ := mem_image.1 (mem_of_mem_erase hb),
    rw mem_product at hc,
    exact ⟨c.2, hc.2, inf_le_right⟩,
  end,
  le_inf := λ P Q R hPQ hPR b hb, begin
    obtain ⟨c, hc, hbc⟩ := hPQ hb,
    obtain ⟨d, hd, hbd⟩ := hPR hb,
    have h := _root_.le_inf hbc hbd,
    refine ⟨c ⊓ d, mem_erase_of_ne_of_mem (ne_bot_of_le_ne_bot (P.ne_bot hb) h)
      (mem_image.2 ⟨(c, d), mem_product.2 ⟨hc, hd⟩, rfl⟩), h⟩,
  end,
  ..finpartition.partial_order, ..finpartition.has_inf }

end inf

lemma exists_le_of_le {a b : α} {P Q : finpartition a} (h : P ≤ Q) (hb : b ∈ Q.parts) :
  ∃ c ∈ P.parts, c ≤ b :=
begin
  by_contra' H,
  refine Q.ne_bot hb (disjoint_self.1 $ disjoint.mono_right (Q.le hb) _),
  rw [←P.sup_parts, finset.disjoint_sup_right],
  rintro c hc,
  obtain ⟨d, hd, hcd⟩ := h hc,
  refine (Q.disjoint hb hd _).mono_right hcd,
  rintro rfl,
  exact H _ hc hcd,
end

lemma card_mono {a : α} {P Q : finpartition a} (h : P ≤ Q) : Q.parts.card ≤ P.parts.card :=
begin
  classical,
  have : ∀ b ∈ Q.parts, ∃ c ∈ P.parts, c ≤ b := λ b, exists_le_of_le h,
  choose f hP hf using this,
  rw ←card_attach,
  refine card_le_card_of_inj_on (λ b, f _ b.2) (λ b _, hP _ b.2) (λ b hb c hc h, _),
  exact subtype.coe_injective (Q.disjoint.elim b.2 c.2 $ λ H, P.ne_bot (hP _ b.2) $
    disjoint_self.1 $ H.mono (hf _ b.2) $ h.le.trans $ hf _ c.2),
end

variables [decidable_eq α] {a b c : α}

section bind
variables {P : finpartition a} {Q : Π i ∈ P.parts, finpartition i}

/-- Given a finpartition `P` of `a` and finpartitions of each part of `P`, this yields the
finpartition of `a` obtained by juxtaposing all the subpartitions. -/
@[simps] def bind (P : finpartition a) (Q : Π i ∈ P.parts, finpartition i) : finpartition a :=
{ parts := P.parts.attach.bUnion (λ i, (Q i.1 i.2).parts),
  sup_indep := begin
    rw sup_indep_iff_pairwise_disjoint,
    rintro a ha b hb h,
    rw [finset.mem_coe, finset.mem_bUnion] at ha hb,
    obtain ⟨⟨A, hA⟩, -, ha⟩ := ha,
    obtain ⟨⟨B, hB⟩, -, hb⟩ := hb,
    obtain rfl | hAB := eq_or_ne A B,
    { exact (Q A hA).disjoint ha hb h },
    { exact (P.disjoint hA hB hAB).mono ((Q A hA).le ha) ((Q B hB).le hb) }
  end,
  sup_parts := begin
    simp_rw [sup_bUnion, ←P.sup_parts],
    rw [eq_comm, ←finset.sup_attach],
    exact sup_congr rfl (λ b hb, (Q b.1 b.2).sup_parts.symm),
  end,
  not_bot_mem := λ h, begin
    rw finset.mem_bUnion at h,
    obtain ⟨⟨A, hA⟩, -, h⟩ := h,
    exact (Q A hA).not_bot_mem h,
  end }

lemma mem_bind : b ∈ (P.bind Q).parts ↔ ∃ A hA, b ∈ (Q A hA).parts :=
begin
  rw [bind, mem_bUnion],
  split,
  { rintro ⟨⟨A, hA⟩, -, h⟩,
    exact ⟨A, hA, h⟩ },
  { rintro ⟨A, hA, h⟩,
    exact ⟨⟨A, hA⟩, mem_attach _ ⟨A, hA⟩, h⟩ }
end

lemma card_bind (Q : Π i ∈ P.parts, finpartition i) :
  (P.bind Q).parts.card = ∑ A in P.parts.attach, (Q _ A.2).parts.card :=
begin
  apply card_bUnion,
  rintro ⟨b, hb⟩ - ⟨c, hc⟩ - hbc d,
  rw [inf_eq_inter, mem_inter],
  rintro ⟨hdb, hdc⟩,
  rw [ne.def, subtype.mk_eq_mk] at hbc,
  exact (Q b hb).ne_bot hdb (eq_bot_iff.2 $
    (le_inf ((Q b hb).le hdb) $ (Q c hc).le hdc).trans $ P.disjoint hb hc hbc),
end

end bind

/-- Adds `b` to a finpartition of `a` to make a finpartition of `a ⊔ b`. -/
@[simps] def extend (P : finpartition a) (hb : b ≠ ⊥) (hab : disjoint a b) (hc : a ⊔ b = c) :
  finpartition c :=
{ parts := insert b P.parts,
  sup_indep :=
  begin
    rw [sup_indep_iff_pairwise_disjoint, coe_insert],
    exact P.disjoint.insert (λ d hd hbd, hab.symm.mono_right $ P.le hd),
  end,
  sup_parts := by rwa [sup_insert, P.sup_parts, id, _root_.sup_comm],
  not_bot_mem := λ h, (mem_insert.1 h).elim hb.symm P.not_bot_mem }

lemma card_extend (P : finpartition a) (b c : α) {hb : b ≠ ⊥} {hab : disjoint a b}
  {hc : a ⊔ b = c} :
  (P.extend hb hab hc).parts.card = P.parts.card + 1 :=
card_insert_of_not_mem $ λ h, hb $ hab.symm.eq_bot_of_le $ P.le h

end distrib_lattice

section generalized_boolean_algebra
variables [generalized_boolean_algebra α] [decidable_eq α] {a : α} (P : finpartition a)

/-- Restricts a finpartition to avoid a given element. -/
@[simps] def avoid (b : α) : finpartition (a \ b) :=
of_erase
  (P.parts.image (\ b))
  (P.disjoint.image_finset_of_le $ λ a, sdiff_le).sup_indep
  (begin
    rw [sup_image, comp.left_id, finset.sup_sdiff_right],
    congr,
    exact P.sup_parts,
  end)

end generalized_boolean_algebra
end finpartition

/-! ### Finite partitions of finsets -/

namespace finpartition
variables [decidable_eq α] {s t : finset α} (P : finpartition s)

lemma nonempty_of_mem_parts {a : finset α} (ha : a ∈ P.parts) : a.nonempty :=
nonempty_iff_ne_empty.2 $ P.ne_bot ha

lemma exists_mem {a : α} (ha : a ∈ s) : ∃ t ∈ P.parts, a ∈ t :=
by { simp_rw ←P.sup_parts at ha, exact mem_sup.1 ha }

lemma bUnion_parts : P.parts.bUnion id = s := (sup_eq_bUnion _ _).symm.trans P.sup_parts

lemma sum_card_parts : ∑ i in P.parts, i.card = s.card :=
begin
  convert congr_arg finset.card P.bUnion_parts,
  rw card_bUnion P.sup_indep.pairwise_disjoint,
  refl,
end

/-- `⊥` is the partition in singletons, aka discrete partition. -/
instance (s : finset α) : has_bot (finpartition s) :=
⟨{ parts := s.map ⟨singleton, singleton_injective⟩,
  sup_indep := set.pairwise_disjoint.sup_indep begin
      rw finset.coe_map,
      exact finset.pairwise_disjoint_range_singleton.subset (set.image_subset_range _ _),
    end,
  sup_parts := by rw [sup_map, comp.left_id, embedding.coe_fn_mk, finset.sup_singleton'],
  not_bot_mem := by simp }⟩

@[simp] lemma parts_bot (s : finset α) :
  (⊥ : finpartition s).parts = s.map ⟨singleton, singleton_injective⟩ := rfl

lemma card_bot (s : finset α) : (⊥ : finpartition s).parts.card = s.card := finset.card_map _
lemma mem_bot_iff : t ∈ (⊥ : finpartition s).parts ↔ ∃ a ∈ s, {a} = t := mem_map

instance (s : finset α) : order_bot (finpartition s) :=
{ bot_le := λ P t ht, begin
    rw mem_bot_iff at ht,
    obtain ⟨a, ha, rfl⟩ := ht,
    obtain ⟨t, ht, hat⟩ := P.exists_mem ha,
    exact ⟨t, ht, singleton_subset_iff.2 hat⟩,
  end,
  ..finpartition.has_bot s }

lemma card_parts_le_card (P : finpartition s) : P.parts.card ≤ s.card :=
by { rw ←card_bot s, exact card_mono bot_le }

section atomise

/-- Cuts `s` along the finsets in `F`: Two elements of `s` will be in the same part if they are
in the same finsets of `F`. -/
def atomise (s : finset α) (F : finset (finset α)) : finpartition s :=
of_erase
  (F.powerset.image $ λ Q, s.filter (λ i, ∀ t ∈ F, t ∈ Q ↔ i ∈ t))
  (set.pairwise_disjoint.sup_indep $ λ x hx y hy h z hz, h begin
    rw [mem_coe, mem_image] at hx hy,
    obtain ⟨Q, hQ, rfl⟩ := hx,
    obtain ⟨R, hR, rfl⟩ := hy,
    suffices h : Q = R,
    { subst h },
    rw [id, id, inf_eq_inter, mem_inter, mem_filter, mem_filter] at hz,
    rw mem_powerset at hQ hR,
    ext i,
    refine ⟨λ hi, _, λ hi, _⟩,
    { rwa [hz.2.2 _ (hQ hi), ←hz.1.2 _ (hQ hi)] },
    { rwa [hz.1.2 _ (hR hi), ←hz.2.2 _ (hR hi)] }
  end)
  (begin
    refine (finset.sup_le $ λ t ht, _).antisymm (λ a ha, _),
    { rw mem_image at ht,
      obtain ⟨A, hA, rfl⟩ := ht,
      exact s.filter_subset _ },
    { rw [mem_sup],
      refine ⟨s.filter (λ i, ∀ t, t ∈ F → (t ∈ F.filter (λ u, a ∈ u) ↔ i ∈ t)),
        mem_image_of_mem _ (mem_powerset.2 $ filter_subset _ _), mem_filter.2 ⟨ha, λ t ht, _⟩⟩,
      rw mem_filter,
      exact and_iff_right ht }
  end)

variables {F : finset (finset α)}

lemma mem_atomise {t : finset α} :
  t ∈ (atomise s F).parts ↔ t.nonempty ∧ ∃ (Q ⊆ F), s.filter (λ i, ∀ u ∈ F, u ∈ Q ↔ i ∈ u) = t :=
by simp only [atomise, of_erase, bot_eq_empty, mem_erase, mem_image, nonempty_iff_ne_empty,
  mem_singleton, and_comm, mem_powerset, exists_prop]

lemma atomise_empty (hs : s.nonempty) : (atomise s ∅).parts = {s} :=
begin
  simp only [atomise, powerset_empty, image_singleton, not_mem_empty, forall_false_left,
    implies_true_iff, filter_true],
  exact erase_eq_of_not_mem (not_mem_singleton.2 hs.ne_empty.symm),
end

lemma card_atomise_le : (atomise s F).parts.card ≤ 2^F.card :=
(card_le_of_subset $ erase_subset _ _).trans $ finset.card_image_le.trans (card_powerset _).le

lemma bUnion_filter_atomise (t : finset α) (ht : t ∈ F) (hts : t ⊆ s) :
  ((atomise s F).parts.filter $ λ u, u ⊆ t).bUnion id = t :=
begin
  ext a,
  rw mem_bUnion,
  refine ⟨λ ⟨u, hu, ha⟩, (mem_filter.1 hu).2 ha, λ ha, _⟩,
  obtain ⟨u, hu, hau⟩ := (atomise s F).exists_mem (hts ha),
  refine ⟨u, mem_filter.2 ⟨hu, λ b hb, _⟩, hau⟩,
  obtain ⟨Q, hQ, rfl⟩ := (mem_atomise.1 hu).2,
  rw mem_filter at hau hb,
  rwa [←hb.2 _ ht, hau.2 _ ht]
end

end atomise
end finpartition
