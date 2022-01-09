/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.big_operators.basic
import order.atoms
import order.sup_indep

/-!
# Finite partitions

In this file, we define finite partitions. A finpartition of `a : α` is a finite set of pairwise
disjoint parts `parts : finset α` which does not contain `⊥` and whose supremum is `a`.

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

## TODO

Link `finpartition` and `setoid.is_partition`.
-/

open finset function
open_locale big_operators

variables {α : Type*}

lemma set.pairwise_disjoint.eq_of_le {α ι : Type*} [semilattice_inf α] [order_bot α] {s : set ι}
  {f : ι → α} (hs : s.pairwise_disjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
  (hf : f i ≠ ⊥) (hij : f i ≤ f j) :
  i = j :=
begin
  classical,
  by_contra,
  exact hf (disjoint_self.1 $ (hs hi hj h).mono_right hij),
end

lemma mk_mem_product {β : Type*} {s : finset α} {t : finset β} {a : α} {b : β} (ha : a ∈ s)
  (hb : b ∈ t) :
  (a, b) ∈ s.product t :=
mem_product.2 ⟨ha, hb⟩

/-- A finite partition of `a : α` is a pairwise disjoint finite set of elements whose supremum is
`a`. We forbid `⊥` as a part. -/
@[ext] structure finpartition {α : Type*} [lattice α] [order_bot α] (a : α) :=
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

@[simps]
def copy {a b : α} (P : finpartition a) (h : a = b) : finpartition b :=
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

lemma eq_empty (P : finpartition (⊥ : α)) : P = finpartition.empty α :=
begin
  ext a,
  exact iff_of_false (λ h, P.ne_bot h $ le_bot_iff.1 $ P.le h) (not_mem_empty a),
end

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

lemma parts_nonempty (P : finpartition a) (ha : a ≠ ⊥) : P.parts.nonempty :=
parts_nonempty_iff.2 ha

instance : unique (finpartition (⊥ : α)) := { uniq := eq_empty ..finpartition.inhabited α }

/-- There's a unique partition of an atom. -/
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
  end,  }

/-! ### Refinement order -/

section order
variables (a)

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
  .. finpartition.has_le a }

instance [decidable (a = ⊥)] : order_top (finpartition a) :=
{ top := if ha : a = ⊥ then (finpartition.empty α).copy ha.symm else indiscrete ha,
  le_top := λ P,
  begin
    split_ifs,
    { intros x hx,
      simpa [h, P.ne_bot hx] using P.le hx },
    { exact λ b hb, ⟨a, mem_singleton_self _, P.le hb⟩ }
  end }

instance {α : Type*} [decidable_eq α] [distrib_lattice α] [order_bot α] (a : α) :
  has_inf (finpartition a) :=
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
    simp_rw [←finset.inf_sup_left, ←finset.sup_inf_right],
    erw [P.sup_parts, Q.sup_parts, inf_idem],
  end⟩

instance [decidable_eq α] : has_sup (finpartition a) :=
⟨λ P Q,
  { parts := sorry,
    sup_indep := sorry,
    sup_parts := sorry,
    not_bot_mem := sorry }⟩

instance [decidable_eq α] : lattice (finpartition a) :=
{ le_sup_left := _,
  le_sup_right := _,
  sup_le := _,
  inf_le_left := λ P Q b hb, begin
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
  .. finpartition.partial_order a,
  .. finpartition.has_inf a,
  .. finpartition.has_sup a }


end order

section bind
variables [decidable_eq α]

/-- Given a finpartition `P` of `a` and finpartitions of each part of `P`, this yields the
finpartition of `a` obtained by juxtaposing all the subpartitions. -/
@[simps] def bind (P : finpartition a) (Q : Π i ∈ P.parts, finpartition i) : finpartition a :=
{ parts := P.parts.attach.bUnion (λ i, (Q i.1 i.2).parts),
  sup_indep := λ a ha b hb h, begin
    rw [finset.mem_coe, finset.mem_bUnion] at ha hb,
    obtain ⟨⟨A, hA⟩, -, ha⟩ := ha,
    obtain ⟨⟨B, hB⟩, -, hb⟩ := hb,
    obtain rfl | hAB := eq_or_ne A B,
    { exact (Q A hA).sup_indep _ ha _ hb h },
    { exact (P.sup_indep _ hA _ hB hAB).mono ((Q A hA).le ha) ((Q B hB).le hb) }
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

lemma mem_bind {P : finpartition a} {Q : Π i ∈ P.parts, finpartition i} {b : α} :
  b ∈ (P.bind Q).parts ↔ ∃ A hA, b ∈ (Q A hA).parts :=
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
    (le_inf ((Q b hb).le hdb) $ (Q c hc).le hdc).trans $ P.sup_indep _ hb _ hc hbc),
end

end bind

/-- Adds `b` to a finpartition of `a` to make a finpartition of `a ⊔ b`. -/
@[simps] def extend [decidable_eq α] (P : finpartition a) {b c : α} (hb : b ≠ ⊥)
  (hab : disjoint a b) (hc : a ⊔ b = c) :
  finpartition c :=
{ parts := insert b P.parts,
  sup_indep :=
  begin
    rw coe_insert,
    exact P.sup_indep.insert (λ d hd hbd, hab.symm.mono_right $ P.le hd),
  end,
  sup_parts := by rwa [sup_insert, P.sup_parts, sup_comm],
  not_bot_mem := λ h, (mem_insert.1 h).elim hb.symm P.not_bot_mem }

lemma card_extend [decidable_eq α] (P : finpartition a) (b c : α) {hb : b ≠ ⊥} {hab : disjoint a b}
  {hc : a ⊔ b = c} :
  (P.extend hb hab hc).parts.card = P.parts.card + 1 :=
card_insert_of_not_mem $ λ h, hb $ hab.symm.eq_bot_of_le $ P.le h

end lattice

section generalized_boolean_algebra
variables [generalized_boolean_algebra α] [decidable_eq α] {a : α} (P : finpartition a)

/-- Restricts a finpartition to avoid a given element. -/
def avoid (b : α) : finpartition (a \ b) :=
of_erase
  (P.parts.image (\ b))
  (P.sup_indep.image_finset $ λ a, sdiff_le)
  (begin
    rw [sup_image, comp.left_id, finset.sup_sdiff_right],
    congr,
    exact P.sup_parts,
  end)

end generalized_boolean_algebra
end finpartition

/-! ### Finite partitions of finsets -/

namespace finpartition
variables [decidable_eq α] {s : finset α} (P : finpartition s)

lemma nonempty_of_mem_parts {a : finset α} (ha : a ∈ P.parts) : a.nonempty :=
nonempty_iff_ne_empty.2 $ P.ne_bot ha

lemma exists_mem {a : α} (ha : a ∈ s) : ∃ t ∈ P.parts, a ∈ t :=
by { simp_rw ←P.sup_parts at ha, exact mem_sup.1 ha }

lemma bUnion_parts : P.parts.bUnion id = s := (sup_eq_bUnion _ _).symm.trans P.sup_parts

lemma sum_card_parts : ∑ i in P.parts, i.card = s.card :=
begin
  rw ←card_bUnion P.sup_indep,
  exact congr_arg finset.card P.bUnion_parts,
end

lemma parts_nonempty [nonempty α] [fintype α] (P : finpartition (univ : finset α)) :
  P.parts.nonempty :=
parts_nonempty_iff.2 univ_nonempty.ne_empty

/-- The partition in singletons. -/
@[simps] def discrete (s : finset α) : finpartition s :=
{ parts := s.map ⟨singleton, singleton_injective⟩,
  sup_indep :=
    begin
      rw finset.coe_map,
      exact finset.pairwise_disjoint_range_singleton.subset (set.image_subset_range _ _),
    end,
  sup_parts := by rw [sup_map, comp.left_id, embedding.coe_fn_mk, finset.sup_singleton'],
  not_bot_mem := by simp }

lemma card_discrete : (discrete s).parts.card = s.card := finset.card_map _

section atomise

/-- Cuts `s` along the finsets in `F`: Two elements of `s` will be in the same part if they are
in the same finsets of `F`. -/
def atomise (s : finset α) (F : finset (finset α)) : finpartition s :=
of_erase
  (F.powerset.image $ λ Q, s.filter (λ i, ∀ t ∈ F, t ∈ Q ↔ i ∈ t))
  (λ x hx y hy h z hz, h begin
    rw [mem_coe, mem_image] at hx hy,
    obtain ⟨Q, hQ, rfl⟩ := hx,
    obtain ⟨R, hR, rfl⟩ := hy,
    suffices h : Q = R,
    { subst h },
    rw [inf_eq_inter, mem_inter, mem_filter, mem_filter] at hz,
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
  simp_rw [atomise, powerset_empty, image_singleton, not_mem_empty, forall_false_left,
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
