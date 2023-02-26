/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fintype.basic
import data.finset.card
import data.list.nodup_equiv_fin
import tactic.positivity
import tactic.wlog

/-!
# Cardinalities of finite types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main declarations

* `fintype.card α`: Cardinality of a fintype. Equal to `finset.univ.card`.
* `fintype.trunc_equiv_fin`: A fintype `α` is computably equivalent to `fin (card α)`. The
  `trunc`-free, noncomputable version is `fintype.equiv_fin`.
* `fintype.trunc_equiv_of_card_eq` `fintype.equiv_of_card_eq`: Two fintypes of same cardinality are
  equivalent. See above.
* `fin.equiv_iff_eq`: `fin m ≃ fin n` iff `m = n`.
* `infinite.nat_embedding`: An embedding of `ℕ` into an infinite type.

We also provide the following versions of the pigeonholes principle.
* `fintype.exists_ne_map_eq_of_card_lt` and `is_empty_of_card_lt`: Finitely many pigeons and
  pigeonholes. Weak formulation.
* `finite.exists_ne_map_eq_of_infinite`: Infinitely many pigeons in finitely many pigeonholes.
  Weak formulation.
* `finite.exists_infinite_fiber`: Infinitely many pigeons in finitely many pigeonholes. Strong
  formulation.

Some more pigeonhole-like statements can be found in `data.fintype.card_embedding`.

Types which have an injection from/a surjection to an `infinite` type are themselves `infinite`.
See `infinite.of_injective` and `infinite.of_surjective`.

## Instances

We provide `infinite` instances for
* specific types: `ℕ`, `ℤ`
* type constructors: `multiset α`, `list α`

-/

open function
open_locale nat

universes u v

variables {α β γ : Type*}

open finset function

namespace fintype

/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [fintype α] : ℕ := (@univ α _).card

/-- There is (computably) an equivalence between `α` and `fin (card α)`.

Since it is not unique and depends on which permutation
of the universe list is used, the equivalence is wrapped in `trunc` to
preserve computability.

See `fintype.equiv_fin` for the noncomputable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq`
for an equiv `α ≃ fin n` given `fintype.card α = n`.

See `fintype.trunc_fin_bijection` for a version without `[decidable_eq α]`.
-/
def trunc_equiv_fin (α) [decidable_eq α] [fintype α] : trunc (α ≃ fin (card α)) :=
by { unfold card finset.card,
     exact quot.rec_on_subsingleton (@univ α _).1
       (λ l (h : ∀ x : α, x ∈ l) (nd : l.nodup),
         trunc.mk (nd.nth_le_equiv_of_forall_mem_list _ h).symm)
       mem_univ_val univ.2 }

/-- There is (noncomputably) an equivalence between `α` and `fin (card α)`.

See `fintype.trunc_equiv_fin` for the computable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq`
for an equiv `α ≃ fin n` given `fintype.card α = n`.
-/
noncomputable def equiv_fin (α) [fintype α] : α ≃ fin (card α) :=
by { letI := classical.dec_eq α, exact (trunc_equiv_fin α).out }

/-- There is (computably) a bijection between `fin (card α)` and `α`.

Since it is not unique and depends on which permutation
of the universe list is used, the bijection is wrapped in `trunc` to
preserve computability.

See `fintype.trunc_equiv_fin` for a version that gives an equivalence
given `[decidable_eq α]`.
-/
def trunc_fin_bijection (α) [fintype α] :
  trunc {f : fin (card α) → α // bijective f} :=
by { dunfold card finset.card,
     exact quot.rec_on_subsingleton (@univ α _).1
       (λ l (h : ∀ x : α, x ∈ l) (nd : l.nodup),
         trunc.mk (nd.nth_le_bijection_of_forall_mem_list _ h))
       mem_univ_val univ.2 }

theorem subtype_card {p : α → Prop} (s : finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
  @card {x // p x} (fintype.subtype s H) = s.card :=
multiset.card_pmap _ _ _

theorem card_of_subtype {p : α → Prop} (s : finset α) (H : ∀ x : α, x ∈ s ↔ p x)
  [fintype {x // p x}] :
  card {x // p x} = s.card :=
by { rw ← subtype_card s H, congr }

@[simp] theorem card_of_finset {p : set α} (s : finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) :
  @fintype.card p (of_finset s H) = s.card :=
fintype.subtype_card s H

theorem card_of_finset' {p : set α} (s : finset α)
  (H : ∀ x, x ∈ s ↔ x ∈ p) [fintype p] : fintype.card p = s.card :=
by rw ←card_of_finset s H; congr

end fintype

namespace fintype

theorem of_equiv_card [fintype α] (f : α ≃ β) :
  @card β (of_equiv α f) = card α :=
multiset.card_map _ _

theorem card_congr {α β} [fintype α] [fintype β] (f : α ≃ β) : card α = card β :=
by rw ← of_equiv_card f; congr

@[congr]
lemma card_congr' {α β} [fintype α] [fintype β] (h : α = β) : card α = card β :=
card_congr (by rw h)

section

variables [fintype α] [fintype β]

/-- If the cardinality of `α` is `n`, there is computably a bijection between `α` and `fin n`.

See `fintype.equiv_fin_of_card_eq` for the noncomputable definition,
and `fintype.trunc_equiv_fin` and `fintype.equiv_fin` for the bijection `α ≃ fin (card α)`.
-/
def trunc_equiv_fin_of_card_eq [decidable_eq α] {n : ℕ} (h : fintype.card α = n) :
  trunc (α ≃ fin n) :=
(trunc_equiv_fin α).map (λ e, e.trans (fin.cast h).to_equiv)


/-- If the cardinality of `α` is `n`, there is noncomputably a bijection between `α` and `fin n`.

See `fintype.trunc_equiv_fin_of_card_eq` for the computable definition,
and `fintype.trunc_equiv_fin` and `fintype.equiv_fin` for the bijection `α ≃ fin (card α)`.
-/
noncomputable def equiv_fin_of_card_eq {n : ℕ} (h : fintype.card α = n) :
  α ≃ fin n :=
by { letI := classical.dec_eq α, exact (trunc_equiv_fin_of_card_eq h).out }

/-- Two `fintype`s with the same cardinality are (computably) in bijection.

See `fintype.equiv_of_card_eq` for the noncomputable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq` for
the specialization to `fin`.
-/
def trunc_equiv_of_card_eq [decidable_eq α] [decidable_eq β] (h : card α = card β) :
  trunc (α ≃ β) :=
(trunc_equiv_fin_of_card_eq h).bind (λ e, (trunc_equiv_fin β).map (λ e', e.trans e'.symm))

/-- Two `fintype`s with the same cardinality are (noncomputably) in bijection.

See `fintype.trunc_equiv_of_card_eq` for the computable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq` for
the specialization to `fin`.
-/
noncomputable def equiv_of_card_eq (h : card α = card β) : α ≃ β :=
by { letI := classical.dec_eq α, letI := classical.dec_eq β,
     exact (trunc_equiv_of_card_eq h).out }

end

theorem card_eq {α β} [F : fintype α] [G : fintype β] : card α = card β ↔ nonempty (α ≃ β) :=
⟨λ h, by { haveI := classical.prop_decidable, exact (trunc_equiv_of_card_eq h).nonempty },
 λ ⟨f⟩, card_congr f⟩

/-- Note: this lemma is specifically about `fintype.of_subsingleton`. For a statement about
arbitrary `fintype` instances, use either `fintype.card_le_one_iff_subsingleton` or
`fintype.card_unique`. -/
@[simp] theorem card_of_subsingleton (a : α) [subsingleton α] :
  @fintype.card _ (of_subsingleton a) = 1 := rfl

@[simp] theorem card_unique [unique α] [h : fintype α] :
  fintype.card α = 1 :=
subsingleton.elim (of_subsingleton default) h ▸ card_of_subsingleton _

/-- Note: this lemma is specifically about `fintype.of_is_empty`. For a statement about
arbitrary `fintype` instances, use `fintype.card_eq_zero_iff`. -/
@[simp] theorem card_of_is_empty [is_empty α] : fintype.card α = 0 := rfl

end fintype

namespace set
variables {s t : set α}

-- We use an arbitrary `[fintype s]` instance here,
-- not necessarily coming from a `[fintype α]`.
@[simp]
lemma to_finset_card {α : Type*} (s : set α) [fintype s] :
  s.to_finset.card = fintype.card s :=
multiset.card_map subtype.val finset.univ.val

end set

lemma finset.card_univ [fintype α] : (finset.univ : finset α).card = fintype.card α :=
rfl

lemma finset.eq_univ_of_card [fintype α] (s : finset α) (hs : s.card = fintype.card α) :
  s = univ :=
eq_of_subset_of_card_le (subset_univ _) $ by rw [hs, finset.card_univ]

lemma finset.card_eq_iff_eq_univ [fintype α] (s : finset α) :
  s.card = fintype.card α ↔ s = finset.univ :=
⟨s.eq_univ_of_card, by { rintro rfl, exact finset.card_univ, }⟩

lemma finset.card_le_univ [fintype α] (s : finset α) :
  s.card ≤ fintype.card α :=
card_le_of_subset (subset_univ s)

lemma finset.card_lt_univ_of_not_mem [fintype α] {s : finset α} {x : α} (hx : x ∉ s) :
  s.card < fintype.card α :=
card_lt_card ⟨subset_univ s, not_forall.2 ⟨x, λ hx', hx (hx' $ mem_univ x)⟩⟩

lemma finset.card_lt_iff_ne_univ [fintype α] (s : finset α) :
  s.card < fintype.card α ↔ s ≠ finset.univ :=
s.card_le_univ.lt_iff_ne.trans (not_iff_not_of_iff s.card_eq_iff_eq_univ)

lemma finset.card_compl_lt_iff_nonempty [fintype α] [decidable_eq α] (s : finset α) :
  sᶜ.card < fintype.card α ↔ s.nonempty :=
sᶜ.card_lt_iff_ne_univ.trans s.compl_ne_univ_iff_nonempty

lemma finset.card_univ_diff [decidable_eq α] [fintype α] (s : finset α) :
  (finset.univ \ s).card = fintype.card α - s.card :=
finset.card_sdiff (subset_univ s)

lemma finset.card_compl [decidable_eq α] [fintype α] (s : finset α) :
  sᶜ.card = fintype.card α - s.card :=
finset.card_univ_diff s

lemma fintype.card_compl_set [fintype α] (s : set α) [fintype s] [fintype ↥sᶜ] :
  fintype.card ↥sᶜ = fintype.card α - fintype.card s :=
begin
  classical,
  rw [← set.to_finset_card, ← set.to_finset_card, ← finset.card_compl, set.to_finset_compl]
end

@[simp] theorem fintype.card_fin (n : ℕ) : fintype.card (fin n) = n :=
list.length_fin_range n

@[simp] lemma finset.card_fin (n : ℕ) : finset.card (finset.univ : finset (fin n)) = n :=
by rw [finset.card_univ, fintype.card_fin]

/-- `fin` as a map from `ℕ` to `Type` is injective. Note that since this is a statement about
equality of types, using it should be avoided if possible. -/
lemma fin_injective : function.injective fin :=
λ m n h,
  (fintype.card_fin m).symm.trans $ (fintype.card_congr $ equiv.cast h).trans (fintype.card_fin n)

/-- A reversed version of `fin.cast_eq_cast` that is easier to rewrite with. -/
theorem fin.cast_eq_cast' {n m : ℕ} (h : fin n = fin m) :
  cast h = ⇑(fin.cast $ fin_injective h) :=
(fin.cast_eq_cast _).symm

lemma card_finset_fin_le {n : ℕ} (s : finset (fin n)) : s.card ≤ n :=
by simpa only [fintype.card_fin] using s.card_le_univ

lemma fin.equiv_iff_eq {m n : ℕ} : nonempty (fin m ≃ fin n) ↔ m = n :=
⟨λ ⟨h⟩, by simpa using fintype.card_congr h, λ h, ⟨equiv.cast $ h ▸ rfl ⟩ ⟩


@[simp] lemma fintype.card_subtype_eq (y : α) [fintype {x // x = y}] :
  fintype.card {x // x = y} = 1 :=
fintype.card_unique

@[simp] lemma fintype.card_subtype_eq' (y : α) [fintype {x // y = x}] :
  fintype.card {x // y = x} = 1 :=
fintype.card_unique

@[simp] theorem fintype.card_empty : fintype.card empty = 0 := rfl

@[simp] theorem fintype.card_pempty : fintype.card pempty = 0 := rfl

theorem fintype.card_unit : fintype.card unit = 1 := rfl

@[simp] theorem fintype.card_punit : fintype.card punit = 1 := rfl

@[simp] theorem fintype.card_bool : fintype.card bool = 2 := rfl

@[simp] theorem fintype.card_ulift (α : Type*) [fintype α] :
  fintype.card (ulift α) = fintype.card α :=
fintype.of_equiv_card _

@[simp] theorem fintype.card_plift (α : Type*) [fintype α] :
  fintype.card (plift α) = fintype.card α :=
fintype.of_equiv_card _

@[simp] lemma fintype.card_order_dual (α : Type*) [fintype α] : fintype.card αᵒᵈ = fintype.card α :=
rfl

@[simp] lemma fintype.card_lex (α : Type*) [fintype α] :
  fintype.card (lex α) = fintype.card α := rfl

/-- Given that `α ⊕ β` is a fintype, `α` is also a fintype. This is non-computable as it uses
that `sum.inl` is an injection, but there's no clear inverse if `α` is empty. -/
noncomputable def fintype.sum_left {α β} [fintype (α ⊕ β)] : fintype α :=
fintype.of_injective (sum.inl : α → α ⊕ β) sum.inl_injective

/-- Given that `α ⊕ β` is a fintype, `β` is also a fintype. This is non-computable as it uses
that `sum.inr` is an injection, but there's no clear inverse if `β` is empty. -/
noncomputable def fintype.sum_right {α β} [fintype (α ⊕ β)] : fintype β :=
fintype.of_injective (sum.inr : β → α ⊕ β) sum.inr_injective

/-!
### Relation to `finite`

In this section we prove that `α : Type*` is `finite` if and only if `fintype α` is nonempty.
-/

@[nolint fintype_finite]
protected lemma fintype.finite {α : Type*} (h : fintype α) : finite α := ⟨fintype.equiv_fin α⟩

/-- For efficiency reasons, we want `finite` instances to have higher
priority than ones coming from `fintype` instances. -/
@[nolint fintype_finite, priority 900]
instance finite.of_fintype (α : Type*) [fintype α] : finite α := fintype.finite ‹_›

lemma finite_iff_nonempty_fintype (α : Type*) :
  finite α ↔ nonempty (fintype α) :=
⟨λ h, let ⟨k, ⟨e⟩⟩ := @finite.exists_equiv_fin α h in ⟨fintype.of_equiv _ e.symm⟩,
  λ ⟨_⟩, by exactI infer_instance⟩

/-- See also `nonempty_encodable`, `nonempty_denumerable`. -/
lemma nonempty_fintype (α : Type*) [finite α] : nonempty (fintype α) :=
(finite_iff_nonempty_fintype α).mp ‹_›

/-- Noncomputably get a `fintype` instance from a `finite` instance. This is not an
instance because we want `fintype` instances to be useful for computations. -/
noncomputable def fintype.of_finite (α : Type*) [finite α] : fintype α := (nonempty_fintype α).some

lemma finite.of_injective {α β : Sort*} [finite β] (f : α → β) (H : injective f) : finite α :=
begin
  casesI nonempty_fintype (plift β),
  rw [← equiv.injective_comp equiv.plift f, ← equiv.comp_injective _ equiv.plift.symm] at H,
  haveI := fintype.of_injective _ H,
  exact finite.of_equiv _ equiv.plift,
end

lemma finite.of_surjective {α β : Sort*} [finite α] (f : α → β) (H : surjective f) :
  finite β :=
finite.of_injective _ $ injective_surj_inv H

lemma finite.exists_univ_list (α) [finite α] : ∃ l : list α, l.nodup ∧ ∀ x : α, x ∈ l :=
by { casesI nonempty_fintype α, obtain ⟨l, e⟩ := quotient.exists_rep (@univ α _).1,
  have := and.intro univ.2 mem_univ_val, exact ⟨_, by rwa ←e at this⟩ }

lemma list.nodup.length_le_card {α : Type*} [fintype α] {l : list α} (h : l.nodup) :
  l.length ≤ fintype.card α :=
by { classical, exact list.to_finset_card_of_nodup h ▸ l.to_finset.card_le_univ }

namespace fintype
variables [fintype α] [fintype β]

lemma card_le_of_injective (f : α → β) (hf : function.injective f) : card α ≤ card β :=
finset.card_le_card_of_inj_on f (λ _ _, finset.mem_univ _) (λ _ _ _ _ h, hf h)

lemma card_le_of_embedding (f : α ↪ β) : card α ≤ card β := card_le_of_injective f f.2

lemma card_lt_of_injective_of_not_mem (f : α → β) (h : function.injective f)
  {b : β} (w : b ∉ set.range f) : card α < card β :=
calc card α = (univ.map ⟨f, h⟩).card : (card_map _).symm
... < card β : finset.card_lt_univ_of_not_mem $
                 by rwa [← mem_coe, coe_map, coe_univ, set.image_univ]

lemma card_lt_of_injective_not_surjective (f : α → β) (h : function.injective f)
  (h' : ¬function.surjective f) : card α < card β :=
let ⟨y, hy⟩ := not_forall.1 h' in card_lt_of_injective_of_not_mem f h hy

lemma card_le_of_surjective (f : α → β) (h : function.surjective f) : card β ≤ card α :=
card_le_of_injective _ (function.injective_surj_inv h)

lemma card_range_le {α β : Type*} (f : α → β) [fintype α] [fintype (set.range f)] :
  fintype.card (set.range f) ≤ fintype.card α :=
fintype.card_le_of_surjective (λ a, ⟨f a, by simp⟩) (λ ⟨_, a, ha⟩, ⟨a, by simpa using ha⟩)

lemma card_range {α β F : Type*} [embedding_like F α β] (f : F) [fintype α]
  [fintype (set.range f)] :
  fintype.card (set.range f) = fintype.card α :=
eq.symm $ fintype.card_congr $ equiv.of_injective _ $ embedding_like.injective f

/--
The pigeonhole principle for finitely many pigeons and pigeonholes.
This is the `fintype` version of `finset.exists_ne_map_eq_of_card_lt_of_maps_to`.
-/
lemma exists_ne_map_eq_of_card_lt (f : α → β) (h : fintype.card β < fintype.card α) :
  ∃ x y, x ≠ y ∧ f x = f y :=
let ⟨x, _, y, _, h⟩ := finset.exists_ne_map_eq_of_card_lt_of_maps_to h (λ x _, mem_univ (f x))
in ⟨x, y, h⟩

lemma card_eq_one_iff : card α = 1 ↔ (∃ x : α, ∀ y, y = x) :=
by rw [←card_unit, card_eq]; exact
⟨λ ⟨a⟩, ⟨a.symm (), λ y, a.injective (subsingleton.elim _ _)⟩,
  λ ⟨x, hx⟩, ⟨⟨λ _, (), λ _, x, λ _, (hx _).trans (hx _).symm,
    λ _, subsingleton.elim _ _⟩⟩⟩

lemma card_eq_zero_iff : card α = 0 ↔ is_empty α :=
by rw [card, finset.card_eq_zero, univ_eq_empty_iff]

lemma card_eq_zero [is_empty α] : card α = 0 := card_eq_zero_iff.2 ‹_›

lemma card_eq_one_iff_nonempty_unique : card α = 1 ↔ nonempty (unique α) :=
⟨λ h, let ⟨d, h⟩ := fintype.card_eq_one_iff.mp h in ⟨{ default := d, uniq := h}⟩,
 λ ⟨h⟩, by exactI fintype.card_unique⟩

/-- A `fintype` with cardinality zero is equivalent to `empty`. -/
def card_eq_zero_equiv_equiv_empty : card α = 0 ≃ (α ≃ empty) :=
(equiv.of_iff card_eq_zero_iff).trans (equiv.equiv_empty_equiv α).symm

lemma card_pos_iff : 0 < card α ↔ nonempty α :=
pos_iff_ne_zero.trans $ not_iff_comm.mp $ not_nonempty_iff.trans card_eq_zero_iff.symm

lemma card_pos [h : nonempty α] : 0 < card α :=
card_pos_iff.mpr h

lemma card_ne_zero [nonempty α] : card α ≠ 0 :=
ne_of_gt card_pos

lemma card_le_one_iff : card α ≤ 1 ↔ (∀ a b : α, a = b) :=
let n := card α in
have hn : n = card α := rfl,
match n, hn with
| 0     := λ ha, ⟨λ h, λ a, (card_eq_zero_iff.1 ha.symm).elim a, λ _, ha ▸ nat.le_succ _⟩
| 1     := λ ha, ⟨λ h, λ a b, let ⟨x, hx⟩ := card_eq_one_iff.1 ha.symm in
  by rw [hx a, hx b],
    λ _, ha ▸ le_rfl⟩
| (n+2) := λ ha, ⟨λ h, by rw ← ha at h; exact absurd h dec_trivial,
  (λ h, card_unit ▸ card_le_of_injective (λ _, ())
    (λ _ _ _, h _ _))⟩
end

lemma card_le_one_iff_subsingleton : card α ≤ 1 ↔ subsingleton α :=
card_le_one_iff.trans subsingleton_iff.symm

lemma one_lt_card_iff_nontrivial : 1 < card α ↔ nontrivial α :=
begin
  classical,
  rw ←not_iff_not,
  push_neg,
  rw [not_nontrivial_iff_subsingleton, card_le_one_iff_subsingleton]
end

lemma exists_ne_of_one_lt_card (h : 1 < card α) (a : α) : ∃ b : α, b ≠ a :=
by { haveI : nontrivial α := one_lt_card_iff_nontrivial.1 h, exact exists_ne a }

lemma exists_pair_of_one_lt_card (h : 1 < card α) : ∃ (a b : α), a ≠ b :=
by { haveI : nontrivial α := one_lt_card_iff_nontrivial.1 h, exact exists_pair_ne α }

lemma card_eq_one_of_forall_eq {i : α} (h : ∀ j, j = i) : card α = 1 :=
fintype.card_eq_one_iff.2 ⟨i,h⟩

lemma one_lt_card [h : nontrivial α] : 1 < fintype.card α :=
fintype.one_lt_card_iff_nontrivial.mpr h

lemma one_lt_card_iff : 1 < card α ↔ ∃ a b : α, a ≠ b :=
one_lt_card_iff_nontrivial.trans nontrivial_iff

lemma two_lt_card_iff : 2 < card α ↔ ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c :=
by simp_rw [←finset.card_univ, two_lt_card_iff, mem_univ, true_and]

lemma card_of_bijective {f : α → β} (hf : bijective f) : card α = card β :=
card_congr (equiv.of_bijective f hf)

end fintype

namespace finite
variables [finite α]

lemma injective_iff_surjective {f : α → α} : injective f ↔ surjective f :=
by haveI := classical.prop_decidable; casesI nonempty_fintype α; exact
have ∀ {f : α → α}, injective f → surjective f,
from λ f hinj x,
  have h₁ : image f univ = univ := eq_of_subset_of_card_le (subset_univ _)
    ((card_image_of_injective univ hinj).symm ▸ le_rfl),
  have h₂ : x ∈ image f univ := h₁.symm ▸ mem_univ _,
  exists_of_bex (mem_image.1 h₂),
⟨this,
  λ hsurj, has_left_inverse.injective
    ⟨surj_inv hsurj, left_inverse_of_surjective_of_right_inverse
      (this (injective_surj_inv _)) (right_inverse_surj_inv _)⟩⟩

lemma injective_iff_bijective {f : α → α} : injective f ↔ bijective f :=
by simp [bijective, injective_iff_surjective]

lemma surjective_iff_bijective {f : α → α} : surjective f ↔ bijective f :=
by simp [bijective, injective_iff_surjective]

lemma injective_iff_surjective_of_equiv  {f : α → β} (e : α ≃ β) : injective f ↔ surjective f :=
have injective (e.symm ∘ f) ↔ surjective (e.symm ∘ f), from injective_iff_surjective,
⟨λ hinj, by simpa [function.comp] using
  e.surjective.comp (this.1 (e.symm.injective.comp hinj)),
λ hsurj, by simpa [function.comp] using
  e.injective.comp (this.2 (e.symm.surjective.comp hsurj))⟩


alias injective_iff_bijective ↔ _root_.function.injective.bijective_of_finite _
alias surjective_iff_bijective ↔ _root_.function.surjective.bijective_of_finite _
alias injective_iff_surjective_of_equiv ↔ _root_.function.injective.surjective_of_fintype
  _root_.function.surjective.injective_of_fintype

end finite

namespace fintype
variables [fintype α] [fintype β]

lemma bijective_iff_injective_and_card (f : α → β) :
  bijective f ↔ injective f ∧ card α = card β :=
⟨λ h, ⟨h.1, card_of_bijective h⟩, λ h, ⟨h.1, h.1.surjective_of_fintype $ equiv_of_card_eq h.2⟩⟩

lemma bijective_iff_surjective_and_card (f : α → β) :
  bijective f ↔ surjective f ∧ card α = card β :=
⟨λ h, ⟨h.2, card_of_bijective h⟩, λ h, ⟨h.1.injective_of_fintype $ equiv_of_card_eq h.2, h.1⟩⟩

lemma _root_.function.left_inverse.right_inverse_of_card_le {f : α → β} {g : β → α}
  (hfg : left_inverse f g) (hcard : card α ≤ card β) :
  right_inverse f g :=
have hsurj : surjective f, from surjective_iff_has_right_inverse.2 ⟨g, hfg⟩,
right_inverse_of_injective_of_left_inverse
  ((bijective_iff_surjective_and_card _).2
    ⟨hsurj, le_antisymm hcard (card_le_of_surjective f hsurj)⟩ ).1
  hfg

lemma _root_.function.right_inverse.left_inverse_of_card_le {f : α → β} {g : β → α}
  (hfg : right_inverse f g) (hcard : card β ≤ card α) :
  left_inverse f g :=
function.left_inverse.right_inverse_of_card_le hfg hcard

end fintype

namespace equiv
variables [fintype α] [fintype β]

open fintype

/-- Construct an equivalence from functions that are inverse to each other. -/
@[simps] def of_left_inverse_of_card_le (hβα : card β ≤ card α) (f : α → β) (g : β → α)
  (h : left_inverse g f) : α ≃ β :=
{ to_fun := f,
  inv_fun := g,
  left_inv := h,
  right_inv := h.right_inverse_of_card_le hβα }

/-- Construct an equivalence from functions that are inverse to each other. -/
@[simps] def of_right_inverse_of_card_le (hαβ : card α ≤ card β) (f : α → β) (g : β → α)
  (h : right_inverse g f) : α ≃ β :=
{ to_fun := f,
  inv_fun := g,
  left_inv := h.left_inverse_of_card_le hαβ,
  right_inv := h }

end equiv

@[simp] lemma fintype.card_coe (s : finset α) [fintype s] :
  fintype.card s = s.card := fintype.card_of_finset' s (λ _, iff.rfl)

/-- Noncomputable equivalence between a finset `s` coerced to a type and `fin s.card`. -/
noncomputable def finset.equiv_fin (s : finset α) : s ≃ fin s.card :=
fintype.equiv_fin_of_card_eq (fintype.card_coe _)

/-- Noncomputable equivalence between a finset `s` as a fintype and `fin n`, when there is a
proof that `s.card = n`. -/
noncomputable def finset.equiv_fin_of_card_eq {s : finset α} {n : ℕ} (h : s.card = n) : s ≃ fin n :=
fintype.equiv_fin_of_card_eq ((fintype.card_coe _).trans h)

/-- Noncomputable equivalence between two finsets `s` and `t` as fintypes when there is a proof
that `s.card = t.card`.-/
noncomputable def finset.equiv_of_card_eq {s t : finset α} (h : s.card = t.card) : s ≃ t :=
fintype.equiv_of_card_eq ((fintype.card_coe _).trans (h.trans (fintype.card_coe _).symm))

@[simp] lemma fintype.card_Prop : fintype.card Prop = 2 := rfl

lemma set_fintype_card_le_univ [fintype α] (s : set α) [fintype ↥s] :
  fintype.card ↥s ≤ fintype.card α :=
fintype.card_le_of_embedding (function.embedding.subtype s)

lemma set_fintype_card_eq_univ_iff [fintype α] (s : set α) [fintype ↥s] :
  fintype.card s = fintype.card α ↔ s = set.univ :=
by rw [←set.to_finset_card, finset.card_eq_iff_eq_univ, ←set.to_finset_univ, set.to_finset_inj]

namespace function.embedding

/-- An embedding from a `fintype` to itself can be promoted to an equivalence. -/
noncomputable def equiv_of_fintype_self_embedding [finite α] (e : α ↪ α) : α ≃ α :=
equiv.of_bijective e e.2.bijective_of_finite

@[simp]
lemma equiv_of_fintype_self_embedding_to_embedding [finite α] (e : α ↪ α) :
  e.equiv_of_fintype_self_embedding.to_embedding = e :=
by { ext, refl, }

/-- If `‖β‖ < ‖α‖` there are no embeddings `α ↪ β`.
This is a formulation of the pigeonhole principle.

Note this cannot be an instance as it needs `h`. -/
@[simp] lemma is_empty_of_card_lt [fintype α] [fintype β]
  (h : fintype.card β < fintype.card α) : is_empty (α ↪ β) :=
⟨λ f, let ⟨x, y, ne, feq⟩ := fintype.exists_ne_map_eq_of_card_lt f h in ne $ f.injective feq⟩

/-- A constructive embedding of a fintype `α` in another fintype `β` when `card α ≤ card β`. -/
def trunc_of_card_le [fintype α] [fintype β] [decidable_eq α] [decidable_eq β]
  (h : fintype.card α ≤ fintype.card β) : trunc (α ↪ β) :=
(fintype.trunc_equiv_fin α).bind $ λ ea,
  (fintype.trunc_equiv_fin β).map $ λ eb,
    ea.to_embedding.trans ((fin.cast_le h).to_embedding.trans eb.symm.to_embedding)

lemma nonempty_of_card_le [fintype α] [fintype β]
  (h : fintype.card α ≤ fintype.card β) : nonempty (α ↪ β) :=
by { classical, exact (trunc_of_card_le h).nonempty }

lemma nonempty_iff_card_le [fintype α] [fintype β] :
  nonempty (α ↪ β) ↔ fintype.card α ≤ fintype.card β :=
⟨λ ⟨e⟩, fintype.card_le_of_embedding e, nonempty_of_card_le⟩

lemma exists_of_card_le_finset [fintype α] {s : finset β} (h : fintype.card α ≤ s.card) :
  ∃ (f : α ↪ β), set.range f ⊆ s :=
begin
  rw ← fintype.card_coe at h,
  rcases nonempty_of_card_le h with ⟨f⟩,
  exact ⟨f.trans (embedding.subtype _), by simp [set.range_subset_iff]⟩
end

end function.embedding

@[simp]
lemma finset.univ_map_embedding {α : Type*} [fintype α] (e : α ↪ α) :
  univ.map e = univ :=
by rw [←e.equiv_of_fintype_self_embedding_to_embedding, univ_map_equiv_to_embedding]

namespace fintype

lemma card_lt_of_surjective_not_injective [fintype α] [fintype β] (f : α → β)
  (h : function.surjective f) (h' : ¬function.injective f) : card β < card α :=
card_lt_of_injective_not_surjective _ (function.injective_surj_inv h) $ λ hg,
have w : function.bijective (function.surj_inv h) := ⟨function.injective_surj_inv h, hg⟩,
h' $ h.injective_of_fintype (equiv.of_bijective _ w).symm

end fintype

theorem fintype.card_subtype_le [fintype α] (p : α → Prop) [decidable_pred p] :
  fintype.card {x // p x} ≤ fintype.card α :=
fintype.card_le_of_embedding (function.embedding.subtype _)

theorem fintype.card_subtype_lt [fintype α] {p : α → Prop} [decidable_pred p]
  {x : α} (hx : ¬ p x) : fintype.card {x // p x} < fintype.card α :=
fintype.card_lt_of_injective_of_not_mem coe subtype.coe_injective $ by rwa subtype.range_coe_subtype

lemma fintype.card_subtype [fintype α] (p : α → Prop) [decidable_pred p] :
  fintype.card {x // p x} = ((finset.univ : finset α).filter p).card :=
begin
  refine fintype.card_of_subtype _ _,
  simp
end

@[simp]
lemma fintype.card_subtype_compl [fintype α]
  (p : α → Prop) [fintype {x // p x}] [fintype {x // ¬ p x}] :
  fintype.card {x // ¬ p x} = fintype.card α - fintype.card {x // p x} :=
begin
  classical,
  rw [fintype.card_of_subtype (set.to_finset pᶜ), set.to_finset_compl p, finset.card_compl,
      fintype.card_of_subtype (set.to_finset p)];
  intro; simp only [set.mem_to_finset, set.mem_compl_iff]; refl,
end

theorem fintype.card_subtype_mono (p q : α → Prop) (h : p ≤ q)
  [fintype {x // p x}] [fintype {x // q x}] :
  fintype.card {x // p x} ≤ fintype.card {x // q x} :=
fintype.card_le_of_embedding (subtype.imp_embedding _ _ h)

/-- If two subtypes of a fintype have equal cardinality, so do their complements. -/
lemma fintype.card_compl_eq_card_compl [finite α] (p q : α → Prop)
  [fintype {x // p x}] [fintype {x // ¬ p x}]
  [fintype {x // q x}] [fintype {x // ¬ q x}]
  (h : fintype.card {x // p x} = fintype.card {x // q x}) :
  fintype.card {x // ¬ p x} = fintype.card {x // ¬ q x} :=
by { casesI nonempty_fintype α, simp only [fintype.card_subtype_compl, h] }

theorem fintype.card_quotient_le [fintype α] (s : setoid α) [decidable_rel ((≈) : α → α → Prop)] :
  fintype.card (quotient s) ≤ fintype.card α :=
fintype.card_le_of_surjective _ (surjective_quotient_mk _)

theorem fintype.card_quotient_lt [fintype α] {s : setoid α} [decidable_rel ((≈) : α → α → Prop)]
  {x y : α} (h1 : x ≠ y) (h2 : x ≈ y) : fintype.card (quotient s) < fintype.card α :=
fintype.card_lt_of_surjective_not_injective _ (surjective_quotient_mk _) $ λ w,
h1 (w $ quotient.eq.mpr h2)

lemma univ_eq_singleton_of_card_one {α} [fintype α] (x : α) (h : fintype.card α = 1) :
  (univ : finset α) = {x} :=
begin
  symmetry,
  apply eq_of_subset_of_card_le (subset_univ ({x})),
  apply le_of_eq,
  simp [h, finset.card_univ]
end

namespace finite
variables [finite α]

lemma well_founded_of_trans_of_irrefl (r : α → α → Prop) [is_trans α r] [is_irrefl α r] :
  well_founded r :=
by classical; casesI nonempty_fintype α; exact
have ∀ x y, r x y → (univ.filter (λ z, r z x)).card < (univ.filter (λ z, r z y)).card,
  from λ x y hxy, finset.card_lt_card $
    by simp only [finset.lt_iff_ssubset.symm, lt_iff_le_not_le,
      finset.le_iff_subset, finset.subset_iff, mem_filter, true_and, mem_univ, hxy];
    exact ⟨λ z hzx, trans hzx hxy, not_forall_of_exists_not ⟨x, not_imp.2 ⟨hxy, irrefl x⟩⟩⟩,
subrelation.wf this (measure_wf _)

lemma preorder.well_founded_lt [preorder α] : well_founded ((<) : α → α → Prop) :=
well_founded_of_trans_of_irrefl _

lemma preorder.well_founded_gt [preorder α] : well_founded ((>) : α → α → Prop) :=
well_founded_of_trans_of_irrefl _

@[priority 10] instance linear_order.is_well_order_lt [linear_order α] : is_well_order α (<) :=
{ wf := preorder.well_founded_lt }

@[priority 10] instance linear_order.is_well_order_gt [linear_order α] : is_well_order α (>) :=
{ wf := preorder.well_founded_gt }

end finite

@[nolint fintype_finite]
protected lemma fintype.false [infinite α] (h : fintype α) : false := not_finite α

@[simp] lemma is_empty_fintype {α : Type*} : is_empty (fintype α) ↔ infinite α :=
⟨λ ⟨h⟩, ⟨λ h', (@nonempty_fintype α h').elim h⟩, λ ⟨h⟩, ⟨λ h', h h'.finite⟩⟩

/-- A non-infinite type is a fintype. -/
noncomputable def fintype_of_not_infinite {α : Type*} (h : ¬ infinite α) : fintype α :=
@fintype.of_finite _ (not_infinite_iff_finite.mp h)

section
open_locale classical

/--
Any type is (classically) either a `fintype`, or `infinite`.

One can obtain the relevant typeclasses via `cases fintype_or_infinite α; resetI`.
-/
noncomputable def fintype_or_infinite (α : Type*) : psum (fintype α) (infinite α) :=
if h : infinite α then psum.inr h else psum.inl (fintype_of_not_infinite h)

end

lemma finset.exists_minimal {α : Type*} [preorder α] (s : finset α) (h : s.nonempty) :
  ∃ m ∈ s, ∀ x ∈ s, ¬ (x < m) :=
begin
  obtain ⟨c, hcs : c ∈ s⟩ := h,
  have : well_founded (@has_lt.lt {x // x ∈ s} _) := finite.well_founded_of_trans_of_irrefl _,
  obtain ⟨⟨m, hms : m ∈ s⟩, -, H⟩ := this.has_min set.univ ⟨⟨c, hcs⟩, trivial⟩,
  exact ⟨m, hms, λ x hx hxm, H ⟨x, hx⟩ trivial hxm⟩,
end

lemma finset.exists_maximal {α : Type*} [preorder α] (s : finset α) (h : s.nonempty) :
  ∃ m ∈ s, ∀ x ∈ s, ¬ (m < x) :=
@finset.exists_minimal αᵒᵈ _ s h

namespace infinite

lemma of_not_fintype (h : fintype α → false) : infinite α := is_empty_fintype.mp ⟨h⟩

/-- If `s : set α` is a proper subset of `α` and `f : α → s` is injective, then `α` is infinite. -/
lemma of_injective_to_set {s : set α} (hs : s ≠ set.univ) {f : α → s} (hf : injective f) :
  infinite α :=
of_not_fintype $ λ h, begin
  resetI, classical,
  refine lt_irrefl (fintype.card α) _,
  calc fintype.card α ≤ fintype.card s : fintype.card_le_of_injective f hf
  ... = s.to_finset.card : s.to_finset_card.symm
  ... < fintype.card α : finset.card_lt_card $
    by rwa [set.to_finset_ssubset_univ, set.ssubset_univ_iff]
end

/-- If `s : set α` is a proper subset of `α` and `f : s → α` is surjective, then `α` is infinite. -/
lemma of_surjective_from_set {s : set α} (hs : s ≠ set.univ) {f : s → α} (hf : surjective f) :
  infinite α :=
of_injective_to_set hs (injective_surj_inv hf)

lemma exists_not_mem_finset [infinite α] (s : finset α) : ∃ x, x ∉ s :=
not_forall.1 $ λ h, fintype.false ⟨s, h⟩

@[priority 100] -- see Note [lower instance priority]
instance (α : Type*) [H : infinite α] : nontrivial α :=
⟨let ⟨x, hx⟩ := exists_not_mem_finset (∅ : finset α) in
let ⟨y, hy⟩ := exists_not_mem_finset ({x} : finset α) in
⟨y, x, by simpa only [mem_singleton] using hy⟩⟩

protected lemma nonempty (α : Type*) [infinite α] : nonempty α :=
by apply_instance

lemma of_injective {α β} [infinite β] (f : β → α) (hf : injective f) : infinite α :=
⟨λ I, by exactI (finite.of_injective f hf).false⟩

lemma of_surjective {α β} [infinite β] (f : α → β) (hf : surjective f) : infinite α :=
⟨λ I, by exactI (finite.of_surjective f hf).false⟩

end infinite

instance : infinite ℕ :=
infinite.of_not_fintype $ by { introI h,
  exact (finset.range _).card_le_univ.not_lt ((nat.lt_succ_self _).trans_eq (card_range _).symm) }

instance : infinite ℤ :=
infinite.of_injective int.of_nat (λ _ _, int.of_nat.inj)

instance [nonempty α] : infinite (multiset α) :=
let ⟨x⟩ := ‹nonempty α› in
  infinite.of_injective (λ n, multiset.replicate n x) (multiset.replicate_left_injective _)

instance [nonempty α] : infinite (list α) :=
infinite.of_surjective (coe : list α → multiset α) (surjective_quot_mk _)

instance infinite.set [infinite α] : infinite (set α) :=
infinite.of_injective singleton set.singleton_injective

instance [infinite α] : infinite (finset α) :=
infinite.of_injective singleton finset.singleton_injective

instance [infinite α] : infinite (option α) :=
infinite.of_injective some (option.some_injective α)

instance sum.infinite_of_left [infinite α] : infinite (α ⊕ β) :=
infinite.of_injective sum.inl sum.inl_injective

instance sum.infinite_of_right [infinite β] : infinite (α ⊕ β) :=
infinite.of_injective sum.inr sum.inr_injective

instance prod.infinite_of_right [nonempty α] [infinite β] : infinite (α × β) :=
infinite.of_surjective prod.snd prod.snd_surjective

instance prod.infinite_of_left [infinite α] [nonempty β] : infinite (α × β) :=
infinite.of_surjective prod.fst prod.fst_surjective

namespace infinite

private noncomputable def nat_embedding_aux (α : Type*) [infinite α] : ℕ → α
| n := by letI := classical.dec_eq α; exact classical.some (exists_not_mem_finset
  ((multiset.range n).pmap (λ m (hm : m < n), nat_embedding_aux m)
    (λ _, multiset.mem_range.1)).to_finset)

private lemma nat_embedding_aux_injective (α : Type*) [infinite α] :
  function.injective (nat_embedding_aux α) :=
begin
  rintro m n h,
  letI := classical.dec_eq α,
  wlog hmlen : m ≤ n generalizing m n,
  { exact (this h.symm $ le_of_not_le hmlen).symm },
  by_contradiction hmn,
  have hmn : m < n, from lt_of_le_of_ne hmlen hmn,
  refine (classical.some_spec (exists_not_mem_finset
    ((multiset.range n).pmap (λ m (hm : m < n), nat_embedding_aux α m)
      (λ _, multiset.mem_range.1)).to_finset)) _,
  refine multiset.mem_to_finset.2 (multiset.mem_pmap.2
    ⟨m, multiset.mem_range.2 hmn, _⟩),
  rw [h, nat_embedding_aux]
end

/-- Embedding of `ℕ` into an infinite type. -/
noncomputable def nat_embedding (α : Type*) [infinite α] : ℕ ↪ α :=
⟨_, nat_embedding_aux_injective α⟩

/-- See `infinite.exists_superset_card_eq` for a version that, for a `s : finset α`,
provides a superset `t : finset α`, `s ⊆ t` such that `t.card` is fixed. -/
lemma exists_subset_card_eq (α : Type*) [infinite α] (n : ℕ) :
  ∃ s : finset α, s.card = n :=
⟨(range n).map (nat_embedding α), by rw [card_map, card_range]⟩

/-- See `infinite.exists_subset_card_eq` for a version that provides an arbitrary
`s : finset α` for any cardinality. -/
lemma exists_superset_card_eq [infinite α] (s : finset α) (n : ℕ) (hn : s.card ≤ n) :
  ∃ t : finset α, s ⊆ t ∧ t.card = n :=
begin
  induction n with n IH generalizing s,
  { exact ⟨s, subset_refl _, nat.eq_zero_of_le_zero hn⟩ },
  { cases hn.eq_or_lt with hn' hn',
    { exact ⟨s, subset_refl _, hn'⟩ },
    obtain ⟨t, hs, ht⟩ := IH _ (nat.le_of_lt_succ hn'),
    obtain ⟨x, hx⟩ := exists_not_mem_finset t,
    refine ⟨finset.cons x t hx, hs.trans (finset.subset_cons _), _⟩,
    simp [hx, ht] }
end

end infinite

/-- If every finset in a type has bounded cardinality, that type is finite. -/
noncomputable def fintype_of_finset_card_le {ι : Type*} (n : ℕ)
  (w : ∀ s : finset ι, s.card ≤ n) : fintype ι :=
begin
  apply fintype_of_not_infinite,
  introI i,
  obtain ⟨s, c⟩ := infinite.exists_subset_card_eq ι (n+1),
  specialize w s,
  rw c at w,
  exact nat.not_succ_le_self n w,
end

lemma not_injective_infinite_finite {α β} [infinite α] [finite β] (f : α → β) : ¬ injective f :=
λ hf, (finite.of_injective f hf).false

/--
The pigeonhole principle for infinitely many pigeons in finitely many pigeonholes. If there are
infinitely many pigeons in finitely many pigeonholes, then there are at least two pigeons in the
same pigeonhole.

See also: `fintype.exists_ne_map_eq_of_card_lt`, `finite.exists_infinite_fiber`.
-/
lemma finite.exists_ne_map_eq_of_infinite {α β} [infinite α] [finite β] (f : α → β) :
  ∃ x y : α, x ≠ y ∧ f x = f y :=
by simpa only [injective, not_forall, not_imp, and.comm] using not_injective_infinite_finite f

instance function.embedding.is_empty {α β} [infinite α] [finite β] : is_empty (α ↪ β) :=
⟨λ f, not_injective_infinite_finite f f.2⟩

/--
The strong pigeonhole principle for infinitely many pigeons in
finitely many pigeonholes.  If there are infinitely many pigeons in
finitely many pigeonholes, then there is a pigeonhole with infinitely
many pigeons.

See also: `finite.exists_ne_map_eq_of_infinite`
-/
lemma finite.exists_infinite_fiber [infinite α] [finite β] (f : α → β) :
  ∃ y : β, infinite (f ⁻¹' {y}) :=
begin
  classical,
  by_contra' hf,
  casesI nonempty_fintype β,
  haveI := λ y, fintype_of_not_infinite $ hf y,
  let key : fintype α :=
  { elems := univ.bUnion (λ (y : β), (f ⁻¹' {y}).to_finset),
    complete := by simp },
  exact key.false,
end

lemma not_surjective_finite_infinite {α β} [finite α] [infinite β] (f : α → β) : ¬ surjective f :=
λ hf, (infinite.of_surjective f hf).not_finite ‹_›

section trunc

/--
A `fintype` with positive cardinality constructively contains an element.
-/
def trunc_of_card_pos {α} [fintype α] (h : 0 < fintype.card α) : trunc α :=
by { letI := (fintype.card_pos_iff.mp h), exact trunc_of_nonempty_fintype α }

end trunc

/-- A custom induction principle for fintypes. The base case is a subsingleton type,
and the induction step is for non-trivial types, and one can assume the hypothesis for
smaller types (via `fintype.card`).

The major premise is `fintype α`, so to use this with the `induction` tactic you have to give a name
to that instance and use that name.
-/
@[elab_as_eliminator]
lemma fintype.induction_subsingleton_or_nontrivial
  {P : Π α [fintype α], Prop} (α : Type*) [fintype α]
  (hbase : ∀ α [fintype α] [subsingleton α], by exactI P α)
  (hstep : ∀ α [fintype α] [nontrivial α],
    by exactI ∀ (ih : ∀ β [fintype β], by exactI ∀ (h : fintype.card β < fintype.card α), P β),
    P α) :
  P α :=
begin
  obtain ⟨ n, hn ⟩ : ∃ n, fintype.card α = n := ⟨fintype.card α, rfl⟩,
  unfreezingI { induction n using nat.strong_induction_on with n ih generalizing α },
  casesI (subsingleton_or_nontrivial α) with hsing hnontriv,
  { apply hbase, },
  { apply hstep,
    introsI β _ hlt,
    rw hn at hlt,
    exact (ih (fintype.card β) hlt _ rfl), }
end

namespace tactic
open positivity

private lemma card_univ_pos (α : Type*) [fintype α] [nonempty α] :
  0 < (finset.univ : finset α).card :=
finset.univ_nonempty.card_pos

/-- Extension for the `positivity` tactic: `finset.card s` is positive if `s` is nonempty. -/
@[positivity]
meta def positivity_finset_card : expr → tactic strictness
| `(finset.card %%s) := do -- TODO: Partial decision procedure for `finset.nonempty`
                          p ← to_expr ``(finset.nonempty %%s) >>= find_assumption,
                          positive <$> mk_app ``finset.nonempty.card_pos [p]
| `(@fintype.card %%α %%i) := positive <$> mk_mapp ``fintype.card_pos [α, i, none]
| e := pp e >>= fail ∘ format.bracket "The expression `"
    "` isn't of the form `finset.card s` or `fintype.card α`"

end tactic
