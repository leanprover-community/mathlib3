/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import order.antichain
import order.order_iso_nat
import order.well_founded
import tactic.tfae

/-!
# Well-founded sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A well-founded subset of an ordered type is one on which the relation `<` is well-founded.

## Main Definitions
 * `set.well_founded_on s r` indicates that the relation `r` is
  well-founded when restricted to the set `s`.
 * `set.is_wf s` indicates that `<` is well-founded when restricted to `s`.
 * `set.partially_well_ordered_on s r` indicates that the relation `r` is
  partially well-ordered (also known as well quasi-ordered) when restricted to the set `s`.
 * `set.is_pwo s` indicates that any infinite sequence of elements in `s` contains an infinite
  monotone subsequence. Note that this is equivalent to containing only two comparable elements.

## Main Results
 * Higman's Lemma, `set.partially_well_ordered_on.partially_well_ordered_on_sublist_forall₂`,
  shows that if `r` is partially well-ordered on `s`, then `list.sublist_forall₂` is partially
  well-ordered on the set of lists of elements of `s`. The result was originally published by
  Higman, but this proof more closely follows Nash-Williams.
 * `set.well_founded_on_iff` relates `well_founded_on` to the well-foundedness of a relation on the
 original type, to avoid dealing with subtypes.
 * `set.is_wf.mono` shows that a subset of a well-founded subset is well-founded.
 * `set.is_wf.union` shows that the union of two well-founded subsets is well-founded.
 * `finset.is_wf` shows that all `finset`s are well-founded.

## TODO

Prove that `s` is partial well ordered iff it has no infinite descending chain or antichain.

## References
 * [Higman, *Ordering by Divisibility in Abstract Algebras*][Higman52]
 * [Nash-Williams, *On Well-Quasi-Ordering Finite Trees*][Nash-Williams63]
-/

variables {ι α β : Type*}

namespace set

/-! ### Relations well-founded on sets -/

/-- `s.well_founded_on r` indicates that the relation `r` is well-founded when restricted to `s`. -/
def well_founded_on (s : set α) (r : α → α → Prop) : Prop := well_founded $ λ a b : s, r a b

@[simp] lemma well_founded_on_empty (r : α → α → Prop) : well_founded_on ∅ r :=
well_founded_of_empty _

section well_founded_on
variables {r r' : α → α → Prop}

section any_rel
variables {s t : set α} {x y : α}

lemma well_founded_on_iff :
  s.well_founded_on r ↔ well_founded (λ (a b : α), r a b ∧ a ∈ s ∧ b ∈ s) :=
begin
  have f : rel_embedding (λ (a : s) (b : s), r a b) (λ (a b : α), r a b ∧ a ∈ s ∧ b ∈ s) :=
    ⟨⟨coe, subtype.coe_injective⟩, λ a b, by simp⟩,
  refine ⟨λ h, _, f.well_founded⟩,
  rw well_founded.well_founded_iff_has_min,
  intros t ht,
  by_cases hst : (s ∩ t).nonempty,
  { rw ← subtype.preimage_coe_nonempty at hst,
    rcases h.has_min (coe ⁻¹' t) hst with ⟨⟨m, ms⟩, mt, hm⟩,
    exact ⟨m, mt, λ x xt ⟨xm, xs, ms⟩, hm ⟨x, xs⟩ xt xm⟩ },
  { rcases ht with ⟨m, mt⟩,
    exact ⟨m, mt, λ x xt ⟨xm, xs, ms⟩, hst ⟨m, ⟨ms, mt⟩⟩⟩ }
end

namespace well_founded_on

protected lemma induction (hs : s.well_founded_on r) (hx : x ∈ s) {P : α → Prop}
  (hP : ∀ y ∈ s, (∀ z ∈ s, r z y → P z) → P y) : P x :=
begin
  let Q : s → Prop := λ y, P y,
  change Q ⟨x, hx⟩,
  refine well_founded.induction hs ⟨x, hx⟩ _,
  simpa only [subtype.forall]
end

protected lemma mono (h : t.well_founded_on r') (hle : r ≤ r') (hst : s ⊆ t) :
  s.well_founded_on r :=
begin
  rw well_founded_on_iff at *,
  refine subrelation.wf (λ x y xy, _) h,
  exact ⟨hle _ _ xy.1, hst xy.2.1, hst xy.2.2⟩
end

lemma subset (h : t.well_founded_on r) (hst : s ⊆ t) : s.well_founded_on r := h.mono le_rfl hst

open relation

/-- `a` is accessible under the relation `r` iff `r` is well-founded on the downward transitive
  closure of `a` under `r` (including `a` or not). -/
lemma acc_iff_well_founded_on {α} {r : α → α → Prop} {a : α} :
  [ acc r a,
    {b | refl_trans_gen r b a}.well_founded_on r,
    {b | trans_gen r b a}.well_founded_on r ].tfae :=
begin
  tfae_have : 1 → 2,
  { refine λ h, ⟨λ b, _⟩, apply inv_image.accessible,
    rw ← acc_trans_gen_iff at h ⊢,
    obtain h'|h' := refl_trans_gen_iff_eq_or_trans_gen.1 b.2,
    { rwa h' at h }, { exact h.inv h' } },
  tfae_have : 2 → 3,
  { exact λ h, h.subset (λ _, trans_gen.to_refl) },
  tfae_have : 3 → 1,
  { refine λ h, acc.intro _ (λ b hb, (h.apply ⟨b, trans_gen.single hb⟩).of_fibration subtype.val _),
    exact λ ⟨c, hc⟩ d h, ⟨⟨d, trans_gen.head h hc⟩, h, rfl⟩ },
  tfae_finish,
end

end well_founded_on
end any_rel

section is_strict_order
variables [is_strict_order α r] {s t : set α}

instance is_strict_order.subset : is_strict_order α (λ (a b : α), r a b ∧ a ∈ s ∧ b ∈ s) :=
{ to_is_irrefl := ⟨λ a con, irrefl_of r a con.1 ⟩,
  to_is_trans := ⟨λ a b c ab bc, ⟨trans_of r ab.1 bc.1, ab.2.1, bc.2.2⟩ ⟩ }

lemma well_founded_on_iff_no_descending_seq :
  s.well_founded_on r ↔ ∀ (f : ((>) : ℕ → ℕ → Prop) ↪r r), ¬∀ n, f n ∈ s :=
begin
  simp only [well_founded_on_iff, rel_embedding.well_founded_iff_no_descending_seq, ← not_exists,
    ← not_nonempty_iff, not_iff_not],
  split,
  { rintro ⟨⟨f, hf⟩⟩,
    have H : ∀ n, f n ∈ s, from λ n, (hf.2 n.lt_succ_self).2.2,
    refine ⟨⟨f, _⟩, H⟩,
    simpa only [H, and_true] using @hf },
  { rintro ⟨⟨f, hf⟩, hfs : ∀ n, f n ∈ s⟩,
    refine ⟨⟨f, _⟩⟩,
    simpa only [hfs, and_true] using @hf }
end

lemma well_founded_on.union (hs : s.well_founded_on r) (ht : t.well_founded_on r) :
  (s ∪ t).well_founded_on r :=
begin
  rw well_founded_on_iff_no_descending_seq at *,
  rintro f hf,
  rcases nat.exists_subseq_of_forall_mem_union f hf with ⟨g, hg|hg⟩,
  exacts [hs (g.dual.lt_embedding.trans f) hg, ht (g.dual.lt_embedding.trans f) hg]
end

@[simp] lemma well_founded_on_union :
  (s ∪ t).well_founded_on r ↔ s.well_founded_on r ∧ t.well_founded_on r :=
⟨λ h, ⟨h.subset $ subset_union_left _ _, h.subset $ subset_union_right _ _⟩, λ h, h.1.union h.2⟩

end is_strict_order
end well_founded_on

/-! ### Sets well-founded w.r.t. the strict inequality -/

section has_lt
variables [has_lt α] {s t : set α}

/-- `s.is_wf` indicates that `<` is well-founded when restricted to `s`. -/
def is_wf (s : set α) : Prop := well_founded_on s (<)

@[simp] lemma is_wf_empty : is_wf (∅ : set α) := well_founded_of_empty _

lemma is_wf_univ_iff : is_wf (univ : set α) ↔ well_founded ((<) : α → α → Prop) :=
by simp [is_wf, well_founded_on_iff]

theorem is_wf.mono (h : is_wf t) (st : s ⊆ t) : is_wf s := h.subset st

end has_lt

section preorder
variables [preorder α] {s t : set α} {a : α}

protected lemma is_wf.union (hs : is_wf s) (ht : is_wf t) : is_wf (s ∪ t) := hs.union ht

@[simp] lemma is_wf_union : is_wf (s ∪ t) ↔ is_wf s ∧ is_wf t := well_founded_on_union

end preorder

section preorder
variables [preorder α] {s t : set α} {a : α}

theorem is_wf_iff_no_descending_seq :
  is_wf s ↔ ∀ f : ℕ → α, strict_anti f → ¬(∀ n, f (order_dual.to_dual n) ∈ s) :=
well_founded_on_iff_no_descending_seq.trans
  ⟨λ H f hf, H ⟨⟨f, hf.injective⟩, λ a b, hf.lt_iff_lt⟩, λ H f, H f (λ _ _, f.map_rel_iff.2)⟩

end preorder

/-!
### Partially well-ordered sets

A set is partially well-ordered by a relation `r` when any infinite sequence contains two elements
where the first is related to the second by `r`. Equivalently, any antichain (see `is_antichain`) is
finite, see `set.partially_well_ordered_on_iff_finite_antichains`.
-/

/-- A subset is partially well-ordered by a relation `r` when any infinite sequence contains
  two elements where the first is related to the second by `r`. -/
def partially_well_ordered_on (s : set α) (r : α → α → Prop) : Prop :=
∀ f : ℕ → α, (∀ n, f n ∈ s) → ∃ m n : ℕ, m < n ∧ r (f m) (f n)

section partially_well_ordered_on
variables {r : α → α → Prop} {r' : β → β → Prop} {f : α → β} {s : set α} {t : set α} {a : α}

lemma partially_well_ordered_on.mono (ht : t.partially_well_ordered_on r) (h : s ⊆ t) :
  s.partially_well_ordered_on r :=
λ f hf, ht f $ λ n, h $ hf n

@[simp] lemma partially_well_ordered_on_empty (r : α → α → Prop) : partially_well_ordered_on ∅ r :=
λ f hf, (hf 0).elim

lemma partially_well_ordered_on.union (hs : s.partially_well_ordered_on r)
  (ht : t.partially_well_ordered_on r) :
  (s ∪ t).partially_well_ordered_on r :=
begin
  rintro f hf,
  rcases nat.exists_subseq_of_forall_mem_union f hf with ⟨g, hgs|hgt⟩,
  { rcases hs _ hgs with ⟨m, n, hlt, hr⟩,
    exact ⟨g m, g n, g.strict_mono hlt, hr⟩ },
  { rcases ht _ hgt with ⟨m, n, hlt, hr⟩,
    exact ⟨g m, g n, g.strict_mono hlt, hr⟩ }
end

@[simp] lemma partially_well_ordered_on_union :
  (s ∪ t).partially_well_ordered_on r ↔
    s.partially_well_ordered_on r ∧ t.partially_well_ordered_on r :=
⟨λ h, ⟨h.mono $ subset_union_left _ _, h.mono $ subset_union_right _ _⟩, λ h, h.1.union h.2⟩

lemma partially_well_ordered_on.image_of_monotone_on (hs : s.partially_well_ordered_on r)
  (hf : ∀ (a₁ ∈ s) (a₂ ∈ s), r a₁ a₂ → r' (f a₁) (f a₂)) :
  (f '' s).partially_well_ordered_on r' :=
begin
  intros g' hg',
  choose g hgs heq using hg',
  obtain rfl : f ∘ g = g', from funext heq,
  obtain ⟨m, n, hlt, hmn⟩ := hs g hgs,
  exact ⟨m, n, hlt, hf _ (hgs m) _ (hgs n) hmn⟩
end

lemma _root_.is_antichain.finite_of_partially_well_ordered_on (ha : is_antichain r s)
  (hp : s.partially_well_ordered_on r) :
  s.finite :=
begin
  refine not_infinite.1 (λ hi, _),
  obtain ⟨m, n, hmn, h⟩ := hp (λ n, hi.nat_embedding _ n) (λ n, (hi.nat_embedding _ n).2),
  exact hmn.ne ((hi.nat_embedding _).injective $ subtype.val_injective $
    ha.eq (hi.nat_embedding _ m).2 (hi.nat_embedding _ n).2 h),
end

section is_refl
variables [is_refl α r]

protected lemma finite.partially_well_ordered_on (hs : s.finite) : s.partially_well_ordered_on r :=
begin
  intros f hf,
  obtain ⟨m, n, hmn, h⟩ := hs.exists_lt_map_eq_of_forall_mem hf,
  exact ⟨m, n, hmn, h.subst $ refl (f m)⟩,
end

lemma _root_.is_antichain.partially_well_ordered_on_iff (hs : is_antichain r s) :
  s.partially_well_ordered_on r ↔ s.finite :=
⟨hs.finite_of_partially_well_ordered_on, finite.partially_well_ordered_on⟩

@[simp] lemma partially_well_ordered_on_singleton (a : α) : partially_well_ordered_on {a} r :=
(finite_singleton a).partially_well_ordered_on

@[simp] lemma partially_well_ordered_on_insert :
  partially_well_ordered_on (insert a s) r ↔ partially_well_ordered_on s r :=
by simp only [← singleton_union, partially_well_ordered_on_union,
  partially_well_ordered_on_singleton, true_and]

protected lemma partially_well_ordered_on.insert (h : partially_well_ordered_on s r) (a : α) :
  partially_well_ordered_on (insert a s) r :=
partially_well_ordered_on_insert.2 h

lemma partially_well_ordered_on_iff_finite_antichains [is_symm α r] :
  s.partially_well_ordered_on r ↔ ∀ t ⊆ s, is_antichain r t → t.finite :=
begin
  refine ⟨λ h t ht hrt, hrt.finite_of_partially_well_ordered_on (h.mono ht), _⟩,
  rintro hs f hf,
  by_contra' H,
  refine infinite_range_of_injective (λ m n hmn, _) (hs _ (range_subset_iff.2 hf) _),
  { obtain h | h | h := lt_trichotomy m n,
    { refine (H _ _ h _).elim,
      rw hmn,
      exact refl _ },
    { exact h },
    { refine (H _ _ h _).elim,
      rw hmn,
      exact refl _ } },
  rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩ hmn,
  obtain h | h  := (ne_of_apply_ne _ hmn).lt_or_lt,
  { exact H _ _ h },
  { exact mt symm (H _ _ h) }
end

variables [is_trans α r]

lemma partially_well_ordered_on.exists_monotone_subseq (h : s.partially_well_ordered_on r)
  (f : ℕ → α) (hf : ∀ n, f n ∈ s) :
  ∃ g : ℕ ↪o ℕ, ∀ m n : ℕ, m ≤ n → r (f (g m)) (f (g n)) :=
begin
  obtain ⟨g, h1 | h2⟩ := exists_increasing_or_nonincreasing_subseq r f,
  { refine ⟨g, λ m n hle, _⟩,
    obtain hlt | rfl := hle.lt_or_eq,
    exacts [h1 m n hlt, refl_of r _] },
  { exfalso,
    obtain ⟨m, n, hlt, hle⟩ := h (f ∘ g) (λ n, hf _),
    exact h2 m n hlt hle }
end

lemma partially_well_ordered_on_iff_exists_monotone_subseq :
  s.partially_well_ordered_on r ↔
    ∀ f : ℕ → α, (∀ n, f n ∈ s) → ∃ (g : ℕ ↪o ℕ), ∀ m n : ℕ, m ≤ n → r (f (g m)) (f (g n)) :=
begin
  classical,
  split; intros h f hf,
  { exact h.exists_monotone_subseq f hf },
  { obtain ⟨g, gmon⟩ := h f hf,
    exact ⟨g 0, g 1, g.lt_iff_lt.2 zero_lt_one, gmon _ _ zero_le_one⟩ }
end

protected lemma partially_well_ordered_on.prod {t : set β} (hs : partially_well_ordered_on s r)
  (ht : partially_well_ordered_on t r') :
  partially_well_ordered_on (s ×ˢ t) (λ x y : α × β, r x.1 y.1 ∧ r' x.2 y.2) :=
begin
  intros f hf,
  obtain ⟨g₁, h₁⟩ := hs.exists_monotone_subseq (prod.fst ∘ f) (λ n, (hf n).1),
  obtain ⟨m, n, hlt, hle⟩ := ht (prod.snd ∘ f ∘ g₁) (λ n, (hf _).2),
  exact ⟨g₁ m, g₁ n, g₁.strict_mono hlt, h₁ _ _ hlt.le, hle⟩
end

end is_refl

lemma partially_well_ordered_on.well_founded_on [is_preorder α r]
 (h : s.partially_well_ordered_on r) :
  s.well_founded_on (λ a b, r a b ∧ ¬r b a) :=
begin
  letI : preorder α := { le := r, le_refl := refl_of r, le_trans := λ _ _ _, trans_of r },
  change s.well_founded_on (<), change s.partially_well_ordered_on (≤) at h,
  rw well_founded_on_iff_no_descending_seq,
  intros f hf,
  obtain ⟨m, n, hlt, hle⟩ := h f hf,
  exact (f.map_rel_iff.2 hlt).not_le hle,
end

end partially_well_ordered_on

section is_pwo
variables [preorder α] [preorder β] {s t : set α}

/-- A subset of a preorder is partially well-ordered when any infinite sequence contains
  a monotone subsequence of length 2 (or equivalently, an infinite monotone subsequence). -/
def is_pwo (s : set α) : Prop := partially_well_ordered_on s (≤)

lemma is_pwo.mono (ht : t.is_pwo) : s ⊆ t → s.is_pwo := ht.mono

theorem is_pwo.exists_monotone_subseq (h : s.is_pwo) (f : ℕ → α) (hf : ∀ n, f n ∈ s) :
  ∃ (g : ℕ ↪o ℕ), monotone (f ∘ g) :=
h.exists_monotone_subseq f hf

theorem is_pwo_iff_exists_monotone_subseq :
  s.is_pwo ↔ ∀ f : ℕ → α, (∀ n, f n ∈ s) → ∃ (g : ℕ ↪o ℕ), monotone (f ∘ g) :=
partially_well_ordered_on_iff_exists_monotone_subseq

protected lemma is_pwo.is_wf (h : s.is_pwo) : s.is_wf :=
by simpa only [← lt_iff_le_not_le] using h.well_founded_on

lemma is_pwo.prod {t : set β} (hs : s.is_pwo) (ht : t.is_pwo) : is_pwo (s ×ˢ t) := hs.prod ht

lemma is_pwo.image_of_monotone_on (hs : s.is_pwo) {f : α → β} (hf : monotone_on f s) :
 is_pwo (f '' s) :=
hs.image_of_monotone_on hf

lemma is_pwo.image_of_monotone (hs : s.is_pwo) {f : α → β} (hf : monotone f) : is_pwo (f '' s) :=
hs.image_of_monotone_on (hf.monotone_on _)

protected lemma is_pwo.union (hs : is_pwo s) (ht : is_pwo t) : is_pwo (s ∪ t) := hs.union ht

@[simp] lemma is_pwo_union : is_pwo (s ∪ t) ↔ is_pwo s ∧ is_pwo t := partially_well_ordered_on_union

protected lemma finite.is_pwo (hs : s.finite) : is_pwo s := hs.partially_well_ordered_on
@[simp] lemma is_pwo_of_finite [finite α] : s.is_pwo := s.to_finite.is_pwo

@[simp] lemma is_pwo_singleton (a : α) : is_pwo ({a} : set α) := (finite_singleton a).is_pwo

@[simp] lemma is_pwo_empty : is_pwo (∅ : set α) := finite_empty.is_pwo

protected lemma subsingleton.is_pwo (hs : s.subsingleton) : is_pwo s := hs.finite.is_pwo

@[simp] lemma is_pwo_insert {a} : is_pwo (insert a s) ↔ is_pwo s :=
by simp only [←singleton_union, is_pwo_union, is_pwo_singleton, true_and]

protected lemma is_pwo.insert (h : is_pwo s) (a : α) : is_pwo (insert a s) := is_pwo_insert.2 h

protected lemma finite.is_wf (hs : s.finite) : is_wf s := hs.is_pwo.is_wf
@[simp] lemma is_wf_singleton {a : α} : is_wf ({a} : set α) := (finite_singleton a).is_wf
protected lemma subsingleton.is_wf (hs : s.subsingleton) : is_wf s := hs.is_pwo.is_wf

@[simp] lemma is_wf_insert {a} : is_wf (insert a s) ↔ is_wf s :=
by simp only [←singleton_union, is_wf_union, is_wf_singleton, true_and]

lemma is_wf.insert (h : is_wf s) (a : α) : is_wf (insert a s) := is_wf_insert.2 h

end is_pwo

section well_founded_on
variables {r : α → α → Prop} [is_strict_order α r] {s : set α} {a : α}

protected lemma finite.well_founded_on (hs : s.finite) : s.well_founded_on r :=
by { letI := partial_order_of_SO r, exact hs.is_wf }

@[simp] lemma well_founded_on_singleton : well_founded_on ({a} : set α) r :=
(finite_singleton a).well_founded_on

protected lemma subsingleton.well_founded_on (hs : s.subsingleton) : s.well_founded_on r :=
hs.finite.well_founded_on

@[simp] lemma well_founded_on_insert : well_founded_on (insert a s) r ↔ well_founded_on s r :=
by simp only [←singleton_union, well_founded_on_union, well_founded_on_singleton, true_and]

lemma well_founded_on.insert (h : well_founded_on s r) (a : α) : well_founded_on (insert a s) r :=
well_founded_on_insert.2 h

end well_founded_on

section linear_order
variables [linear_order α] {s : set α}

protected lemma is_wf.is_pwo (hs : s.is_wf) : s.is_pwo :=
begin
  intros f hf,
  lift f to ℕ → s using hf,
  have hrange : (range f).nonempty := range_nonempty _,
  rcases hs.has_min (range f) (range_nonempty _) with ⟨_, ⟨m, rfl⟩, hm⟩,
  simp only [forall_range_iff, not_lt] at hm,
  exact ⟨m, m + 1, lt_add_one m, hm _⟩,
end

/-- In a linear order, the predicates `set.is_wf` and `set.is_pwo` are equivalent. -/
lemma is_wf_iff_is_pwo : s.is_wf ↔ s.is_pwo := ⟨is_wf.is_pwo, is_pwo.is_wf⟩

end linear_order
end set

namespace finset
variables {r : α → α → Prop}

@[simp] protected lemma partially_well_ordered_on [is_refl α r] (s : finset α) :
  (s : set α).partially_well_ordered_on r :=
s.finite_to_set.partially_well_ordered_on

@[simp] protected lemma is_pwo [preorder α] (s : finset α) : set.is_pwo (↑s : set α) :=
s.partially_well_ordered_on

@[simp] protected lemma is_wf [preorder α] (s : finset α) : set.is_wf (↑s : set α) :=
s.finite_to_set.is_wf

@[simp] protected lemma well_founded_on [is_strict_order α r] (s : finset α) :
  set.well_founded_on (↑s : set α) r :=
by { letI := partial_order_of_SO r, exact s.is_wf }

lemma well_founded_on_sup [is_strict_order α r] (s : finset ι) {f : ι → set α} :
  (s.sup f).well_founded_on r ↔ ∀ i ∈ s, (f i).well_founded_on r :=
finset.cons_induction_on s (by simp) $ λ a s ha hs, by simp [-sup_set_eq_bUnion, hs]

lemma partially_well_ordered_on_sup (s : finset ι) {f : ι → set α} :
  (s.sup f).partially_well_ordered_on r ↔ ∀ i ∈ s, (f i).partially_well_ordered_on r :=
finset.cons_induction_on s (by simp) $ λ a s ha hs, by simp [-sup_set_eq_bUnion, hs]

lemma is_wf_sup [preorder α] (s : finset ι) {f : ι → set α} :
  (s.sup f).is_wf ↔ ∀ i ∈ s, (f i).is_wf :=
s.well_founded_on_sup

lemma is_pwo_sup [preorder α] (s : finset ι) {f : ι → set α} :
  (s.sup f).is_pwo ↔ ∀ i ∈ s, (f i).is_pwo :=
s.partially_well_ordered_on_sup

@[simp] lemma well_founded_on_bUnion [is_strict_order α r] (s : finset ι) {f : ι → set α} :
  (⋃ i ∈ s, f i).well_founded_on r ↔ ∀ i ∈ s, (f i).well_founded_on r :=
by simpa only [finset.sup_eq_supr] using s.well_founded_on_sup

@[simp] lemma partially_well_ordered_on_bUnion (s : finset ι) {f : ι → set α} :
  (⋃ i ∈ s, f i).partially_well_ordered_on r ↔ ∀ i ∈ s, (f i).partially_well_ordered_on r :=
by simpa only [finset.sup_eq_supr] using s.partially_well_ordered_on_sup

@[simp] lemma is_wf_bUnion [preorder α] (s : finset ι) {f : ι → set α} :
  (⋃ i ∈ s, f i).is_wf ↔ ∀ i ∈ s, (f i).is_wf :=
s.well_founded_on_bUnion

@[simp] lemma is_pwo_bUnion [preorder α] (s : finset ι) {f : ι → set α} :
  (⋃ i ∈ s, f i).is_pwo ↔ ∀ i ∈ s, (f i).is_pwo :=
s.partially_well_ordered_on_bUnion

end finset

namespace set
section preorder
variables [preorder α] {s : set α} {a : α}

/-- `is_wf.min` returns a minimal element of a nonempty well-founded set. -/
noncomputable def is_wf.min (hs : is_wf s) (hn : s.nonempty) : α :=
hs.min univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)

lemma is_wf.min_mem (hs : is_wf s) (hn : s.nonempty) : hs.min hn ∈ s :=
(well_founded.min hs univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)).2

lemma is_wf.not_lt_min (hs : is_wf s) (hn : s.nonempty) (ha : a ∈ s) : ¬ a < hs.min hn :=
hs.not_lt_min univ (nonempty_iff_univ_nonempty.1 hn.to_subtype) (mem_univ (⟨a, ha⟩ : s))

@[simp]
lemma is_wf_min_singleton (a) {hs : is_wf ({a} : set α)} {hn : ({a} : set α).nonempty} :
  hs.min hn = a :=
eq_of_mem_singleton (is_wf.min_mem hs hn)

end preorder

section linear_order
variables [linear_order α] {s t : set α} {a : α}

lemma is_wf.min_le (hs : s.is_wf) (hn : s.nonempty) (ha : a ∈ s) : hs.min hn ≤ a :=
le_of_not_lt (hs.not_lt_min hn ha)

lemma is_wf.le_min_iff (hs : s.is_wf) (hn : s.nonempty) : a ≤ hs.min hn ↔ ∀ b, b ∈ s → a ≤ b :=
⟨λ ha b hb, le_trans ha (hs.min_le hn hb), λ h, h _ (hs.min_mem _)⟩

lemma is_wf.min_le_min_of_subset
  {hs : s.is_wf} {hsn : s.nonempty} {ht : t.is_wf} {htn : t.nonempty} (hst : s ⊆ t) :
  ht.min htn ≤ hs.min hsn :=
(is_wf.le_min_iff _ _).2 (λ b hb, ht.min_le htn (hst hb))

lemma is_wf.min_union (hs : s.is_wf) (hsn : s.nonempty) (ht : t.is_wf) (htn : t.nonempty) :
  (hs.union ht).min (union_nonempty.2 (or.intro_left _ hsn)) = min (hs.min hsn) (ht.min htn) :=
begin
  refine le_antisymm (le_min (is_wf.min_le_min_of_subset (subset_union_left _ _))
      (is_wf.min_le_min_of_subset (subset_union_right _ _))) _,
  rw min_le_iff,
  exact ((mem_union _ _ _).1 ((hs.union ht).min_mem
    (union_nonempty.2 (or.intro_left _ hsn)))).imp (hs.min_le _) (ht.min_le _),
end

end linear_order
end set

open set

namespace set.partially_well_ordered_on
variables {r : α → α → Prop}

/-- In the context of partial well-orderings, a bad sequence is a nonincreasing sequence
  whose range is contained in a particular set `s`. One exists if and only if `s` is not
  partially well-ordered. -/
def is_bad_seq (r : α → α → Prop) (s : set α) (f : ℕ → α) : Prop :=
(∀ n, f n ∈ s) ∧ ∀ m n : ℕ, m < n → ¬ r (f m) (f n)

lemma iff_forall_not_is_bad_seq (r : α → α → Prop) (s : set α) :
  s.partially_well_ordered_on r ↔ ∀ f, ¬ is_bad_seq r s f :=
forall_congr $ λ f, by simp [is_bad_seq]

/-- This indicates that every bad sequence `g` that agrees with `f` on the first `n`
  terms has `rk (f n) ≤ rk (g n)`. -/
def is_min_bad_seq (r : α → α → Prop) (rk : α → ℕ) (s : set α) (n : ℕ) (f : ℕ → α) : Prop :=
∀ g : ℕ → α, (∀ (m : ℕ), m < n → f m = g m) → rk (g n) < rk (f n) → ¬ is_bad_seq r s g

/-- Given a bad sequence `f`, this constructs a bad sequence that agrees with `f` on the first `n`
  terms and is minimal at `n`.
-/
noncomputable def min_bad_seq_of_bad_seq (r : α → α → Prop) (rk : α → ℕ) (s : set α)
  (n : ℕ) (f : ℕ → α) (hf : is_bad_seq r s f) :
  { g : ℕ → α // (∀ (m : ℕ), m < n → f m = g m) ∧ is_bad_seq r s g ∧ is_min_bad_seq r rk s n g } :=
begin
  classical,
  have h : ∃ (k : ℕ) (g : ℕ → α), (∀ m, m < n → f m = g m) ∧ is_bad_seq r s g
        ∧ rk (g n) = k :=
  ⟨_, f, λ _ _, rfl, hf, rfl⟩,
  obtain ⟨h1, h2, h3⟩ := classical.some_spec (nat.find_spec h),
  refine ⟨classical.some (nat.find_spec h), h1, by convert h2, λ g hg1 hg2 con, _⟩,
  refine nat.find_min h _ ⟨g, λ m mn, (h1 m mn).trans (hg1 m mn), by convert con, rfl⟩,
  rwa ← h3,
end

lemma exists_min_bad_of_exists_bad (r : α → α → Prop) (rk : α → ℕ) (s : set α) :
  (∃ f, is_bad_seq r s f) → ∃ f, is_bad_seq r s f ∧ ∀ n, is_min_bad_seq r rk s n f :=
begin
  rintro ⟨f0, (hf0 : is_bad_seq r s f0)⟩,
  let fs : Π (n : ℕ), { f :  ℕ → α // is_bad_seq r s f ∧ is_min_bad_seq r rk s n f },
  { refine nat.rec _ _,
    { exact ⟨(min_bad_seq_of_bad_seq r rk s 0 f0 hf0).1,
        (min_bad_seq_of_bad_seq r rk s 0 f0 hf0).2.2⟩, },
    { exact λ n fn, ⟨(min_bad_seq_of_bad_seq r rk s (n + 1) fn.1 fn.2.1).1,
        (min_bad_seq_of_bad_seq r rk s (n + 1) fn.1 fn.2.1).2.2⟩ } },
  have h : ∀ m n, m ≤ n → (fs m).1 m = (fs n).1 m,
  { intros m n mn,
    obtain ⟨k, rfl⟩ := exists_add_of_le mn,
    clear mn,
    induction k with k ih,
    { refl },
    rw [ih, ((min_bad_seq_of_bad_seq r rk s (m + k).succ (fs (m + k)).1 (fs (m + k)).2.1).2.1 m
        (nat.lt_succ_iff.2 (nat.add_le_add_left k.zero_le m)))],
    refl },
  refine ⟨λ n, (fs n).1 n, ⟨(λ n, ((fs n).2).1.1 n), λ m n mn, _⟩, λ n g hg1 hg2, _⟩,
  { dsimp,
    rw [← subtype.val_eq_coe, h m n (le_of_lt mn)],
    convert (fs n).2.1.2 m n mn },
  { convert (fs n).2.2 g (λ m mn, eq.trans _ (hg1 m mn)) (lt_of_lt_of_le hg2 le_rfl),
    rw ← h m n (le_of_lt mn) },
end

lemma iff_not_exists_is_min_bad_seq (rk : α → ℕ) {s : set α} :
  s.partially_well_ordered_on r ↔ ¬ ∃ f, is_bad_seq r s f ∧ ∀ n, is_min_bad_seq r rk s n f :=
begin
  rw [iff_forall_not_is_bad_seq, ← not_exists, not_congr],
  split,
  { apply exists_min_bad_of_exists_bad },
  rintro ⟨f, hf1, hf2⟩,
  exact ⟨f, hf1⟩,
end

/-- Higman's Lemma, which states that for any reflexive, transitive relation `r` which is
  partially well-ordered on a set `s`, the relation `list.sublist_forall₂ r` is partially
  well-ordered on the set of lists of elements of `s`. That relation is defined so that
  `list.sublist_forall₂ r l₁ l₂` whenever `l₁` related pointwise by `r` to a sublist of `l₂`.  -/
lemma partially_well_ordered_on_sublist_forall₂ (r : α → α → Prop) [is_refl α r] [is_trans α r]
  {s : set α} (h : s.partially_well_ordered_on r) :
  { l : list α | ∀ x, x ∈ l → x ∈ s }.partially_well_ordered_on (list.sublist_forall₂ r) :=
begin
  rcases s.eq_empty_or_nonempty with rfl | ⟨as, has⟩,
  { apply partially_well_ordered_on.mono (finset.partially_well_ordered_on {list.nil}),
    { intros l hl,
      rw [finset.mem_coe, finset.mem_singleton, list.eq_nil_iff_forall_not_mem],
      exact hl, },
    apply_instance },
  haveI : inhabited α := ⟨as⟩,
  rw [iff_not_exists_is_min_bad_seq (list.length)],
  rintro ⟨f, hf1, hf2⟩,
  have hnil : ∀ n, f n ≠ list.nil :=
    λ n con, (hf1).2 n n.succ n.lt_succ_self (con.symm ▸ list.sublist_forall₂.nil),
  obtain ⟨g, hg⟩ := h.exists_monotone_subseq (list.head ∘ f) _,
  swap, { simp only [set.range_subset_iff, function.comp_apply],
    exact λ n, hf1.1 n _ (list.head_mem_self (hnil n)) },
  have hf' := hf2 (g 0) (λ n, if n < g 0 then f n else list.tail (f (g (n - g 0))))
    (λ m hm, (if_pos hm).symm) _,
  swap, { simp only [if_neg (lt_irrefl (g 0)), tsub_self],
    rw [list.length_tail, ← nat.pred_eq_sub_one],
    exact nat.pred_lt (λ con, hnil _ (list.length_eq_zero.1 con)) },
  rw [is_bad_seq] at hf',
  push_neg at hf',
  obtain ⟨m, n, mn, hmn⟩ := hf' _,
  swap,
  { rintro n x hx,
    split_ifs at hx with hn hn,
    { exact hf1.1 _ _ hx },
    { refine hf1.1 _ _ (list.tail_subset _ hx), } },
  by_cases hn : n < g 0,
  { apply hf1.2 m n mn,
    rwa [if_pos hn, if_pos (mn.trans hn)] at hmn },
  { obtain ⟨n', rfl⟩ := exists_add_of_le (not_lt.1 hn),
    rw [if_neg hn, add_comm (g 0) n', add_tsub_cancel_right] at hmn,
    split_ifs at hmn with hm hm,
    { apply hf1.2 m (g n') (lt_of_lt_of_le hm (g.monotone n'.zero_le)),
      exact trans hmn (list.tail_sublist_forall₂_self _) },
    { rw [← (tsub_lt_iff_left (le_of_not_lt hm))] at mn,
      apply hf1.2 _ _ (g.lt_iff_lt.2 mn),
      rw [← list.cons_head_tail (hnil (g (m - g 0))), ← list.cons_head_tail (hnil (g n'))],
      exact list.sublist_forall₂.cons (hg _ _ (le_of_lt mn)) hmn, } }
end

end set.partially_well_ordered_on

lemma well_founded.is_wf [has_lt α] (h : well_founded ((<) : α → α → Prop)) (s : set α) : s.is_wf :=
(set.is_wf_univ_iff.2 h).mono s.subset_univ

/-- A version of **Dickson's lemma** any subset of functions `Π s : σ, α s` is partially well
ordered, when `σ` is a `fintype` and each `α s` is a linear well order.
This includes the classical case of Dickson's lemma that `ℕ ^ n` is a well partial order.
Some generalizations would be possible based on this proof, to include cases where the target is
partially well ordered, and also to consider the case of `set.partially_well_ordered_on` instead of
`set.is_pwo`. -/
lemma pi.is_pwo {α : ι → Type*} [Π i, linear_order (α i)] [∀ i, is_well_order (α i) (<)] [finite ι]
  (s : set (Π i, α i)) : s.is_pwo :=
begin
  casesI nonempty_fintype ι,
  suffices : ∀ s : finset ι, ∀ (f : ℕ → Π s, α s), ∃ g : ℕ ↪o ℕ,
    ∀ ⦃a b : ℕ⦄, a ≤ b → ∀ (x : ι) (hs : x ∈ s), (f ∘ g) a x ≤ (f ∘ g) b x,
  { refine is_pwo_iff_exists_monotone_subseq.2 (λ f hf, _),
    simpa only [finset.mem_univ, true_implies_iff] using this finset.univ f },
  refine finset.cons_induction _ _,
  { intros f, existsi rel_embedding.refl (≤),
    simp only [is_empty.forall_iff, implies_true_iff, forall_const, finset.not_mem_empty], },
  { intros x s hx ih f,
    obtain ⟨g, hg⟩ := (is_well_founded.wf.is_wf univ).is_pwo.exists_monotone_subseq (λ n, f n x)
      mem_univ,
    obtain ⟨g', hg'⟩ := ih (f ∘ g),
    refine ⟨g'.trans g, λ a b hab, (finset.forall_mem_cons _ _).2 _⟩,
    exact ⟨hg (order_hom_class.mono g' hab), hg' hab⟩ }
end
