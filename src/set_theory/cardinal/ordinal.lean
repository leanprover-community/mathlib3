/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/

import data.finsupp.multiset
import order.bounded
import set_theory.ordinal.principal
import tactic.linarith

/-!
# Cardinals and ordinals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Relationships between cardinals and ordinals, properties of cardinals that are proved
using ordinals.

## Main definitions

* The function `cardinal.aleph'` gives the cardinals listed by their ordinal
  index, and is the inverse of `cardinal.aleph_idx`.
  `aleph' n = n`, `aleph' ω = ℵ₀`, `aleph' (ω + 1) = succ ℵ₀`, etc.
  It is an order isomorphism between ordinals and cardinals.
* The function `cardinal.aleph` gives the infinite cardinals listed by their
  ordinal index. `aleph 0 = ℵ₀`, `aleph 1 = succ ℵ₀` is the first
  uncountable cardinal, and so on.
* The function `cardinal.beth` enumerates the Beth cardinals. `beth 0 = ℵ₀`,
  `beth (succ o) = 2 ^ beth o`, and for a limit ordinal `o`, `beth o` is the supremum of `beth a`
  for `a < o`.

## Main Statements

* `cardinal.mul_eq_max` and `cardinal.add_eq_max` state that the product (resp. sum) of two infinite
  cardinals is just their maximum. Several variations around this fact are also given.
* `cardinal.mk_list_eq_mk` : when `α` is infinite, `α` and `list α` have the same cardinality.
* simp lemmas for inequalities between `bit0 a` and `bit1 b` are registered, making `simp`
  able to prove inequalities about numeral cardinals.

## Tags

cardinal arithmetic (for infinite cardinals)
-/

noncomputable theory

open function cardinal set equiv order
open_locale classical cardinal ordinal

universes u v w

namespace cardinal
section using_ordinals
open ordinal

theorem ord_is_limit {c} (co : ℵ₀ ≤ c) : (ord c).is_limit :=
begin
  refine ⟨λ h, aleph_0_ne_zero _, λ a, lt_imp_lt_of_le_imp_le (λ h, _)⟩,
  { rw [←ordinal.le_zero, ord_le] at h,
    simpa only [card_zero, nonpos_iff_eq_zero] using co.trans h },
  { rw ord_le at h ⊢,
    rwa [←@add_one_of_aleph_0_le (card a), ←card_succ],
    rw [←ord_le, ←le_succ_of_is_limit, ord_le],
    { exact co.trans h },
    { rw ord_aleph_0, exact omega_is_limit } }
end

/-! ### Aleph cardinals -/

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ω = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)
  In this definition, we register additionally that this function is an initial segment,
  i.e., it is order preserving and its range is an initial segment of the ordinals.
  For the basic function version, see `aleph_idx`.
  For an upgraded version stating that the range is everything, see `aleph_idx.rel_iso`. -/
def aleph_idx.initial_seg : @initial_seg cardinal ordinal (<) (<) :=
@rel_embedding.collapse cardinal ordinal (<) (<) _ cardinal.ord.order_embedding.lt_embedding

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ω = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)
  For an upgraded version stating that the range is everything, see `aleph_idx.rel_iso`. -/
def aleph_idx : cardinal → ordinal := aleph_idx.initial_seg

@[simp] theorem aleph_idx.initial_seg_coe :
  (aleph_idx.initial_seg : cardinal → ordinal) = aleph_idx := rfl

@[simp] theorem aleph_idx_lt {a b} : aleph_idx a < aleph_idx b ↔ a < b :=
aleph_idx.initial_seg.to_rel_embedding.map_rel_iff

@[simp] theorem aleph_idx_le {a b} : aleph_idx a ≤ aleph_idx b ↔ a ≤ b :=
by rw [← not_lt, ← not_lt, aleph_idx_lt]

theorem aleph_idx.init {a b} : b < aleph_idx a → ∃ c, aleph_idx c = b :=
aleph_idx.initial_seg.init

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ℵ₀ = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)
  In this version, we register additionally that this function is an order isomorphism
  between cardinals and ordinals.
  For the basic function version, see `aleph_idx`. -/
def aleph_idx.rel_iso : @rel_iso cardinal.{u} ordinal.{u} (<) (<) :=
@rel_iso.of_surjective cardinal.{u} ordinal.{u} (<) (<) aleph_idx.initial_seg.{u} $
(initial_seg.eq_or_principal aleph_idx.initial_seg.{u}).resolve_right $
λ ⟨o, e⟩, begin
  have : ∀ c, aleph_idx c < o := λ c, (e _).2 ⟨_, rfl⟩,
  refine ordinal.induction_on o _ this, introsI α r _ h,
  let s := ⨆ a, inv_fun aleph_idx (ordinal.typein r a),
  apply (lt_succ s).not_le,
  have I : injective aleph_idx := aleph_idx.initial_seg.to_embedding.injective,
  simpa only [typein_enum, left_inverse_inv_fun I (succ s)] using le_csupr
    (cardinal.bdd_above_range.{u u} (λ a : α, inv_fun aleph_idx (ordinal.typein r a)))
    (ordinal.enum r _ (h (succ s)))
end

@[simp] theorem aleph_idx.rel_iso_coe :
  (aleph_idx.rel_iso : cardinal → ordinal) = aleph_idx := rfl

@[simp] theorem type_cardinal : @type cardinal (<) _ = ordinal.univ.{u (u+1)} :=
by rw ordinal.univ_id; exact quotient.sound ⟨aleph_idx.rel_iso⟩

@[simp] theorem mk_cardinal : #cardinal = univ.{u (u+1)} :=
by simpa only [card_type, card_univ] using congr_arg card type_cardinal

/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = succ ℵ₀`, etc.
  In this version, we register additionally that this function is an order isomorphism
  between ordinals and cardinals.
  For the basic function version, see `aleph'`. -/
def aleph'.rel_iso := cardinal.aleph_idx.rel_iso.symm

/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = succ ℵ₀`, etc. -/
def aleph' : ordinal → cardinal := aleph'.rel_iso

@[simp] theorem aleph'.rel_iso_coe :
  (aleph'.rel_iso : ordinal → cardinal) = aleph' := rfl

@[simp] theorem aleph'_lt {o₁ o₂ : ordinal} : aleph' o₁ < aleph' o₂ ↔ o₁ < o₂ :=
aleph'.rel_iso.map_rel_iff

@[simp] theorem aleph'_le {o₁ o₂ : ordinal} : aleph' o₁ ≤ aleph' o₂ ↔ o₁ ≤ o₂ :=
le_iff_le_iff_lt_iff_lt.2 aleph'_lt

@[simp] theorem aleph'_aleph_idx (c : cardinal) : aleph' c.aleph_idx = c :=
cardinal.aleph_idx.rel_iso.to_equiv.symm_apply_apply c

@[simp] theorem aleph_idx_aleph' (o : ordinal) : (aleph' o).aleph_idx = o :=
cardinal.aleph_idx.rel_iso.to_equiv.apply_symm_apply o

@[simp] theorem aleph'_zero : aleph' 0 = 0 :=
by { rw [← nonpos_iff_eq_zero, ← aleph'_aleph_idx 0, aleph'_le], apply ordinal.zero_le }

@[simp] theorem aleph'_succ {o : ordinal} : aleph' (succ o) = succ (aleph' o) :=
begin
  apply (succ_le_of_lt $ aleph'_lt.2 $ lt_succ o).antisymm' (cardinal.aleph_idx_le.1 $ _),
  rw [aleph_idx_aleph', succ_le_iff, ← aleph'_lt, aleph'_aleph_idx],
  apply lt_succ
end

@[simp] theorem aleph'_nat : ∀ n : ℕ, aleph' n = n
| 0     := aleph'_zero
| (n+1) := show aleph' (succ n) = n.succ,
           by rw [aleph'_succ, aleph'_nat, nat_succ]

theorem aleph'_le_of_limit {o : ordinal} (l : o.is_limit) {c} :
  aleph' o ≤ c ↔ ∀ o' < o, aleph' o' ≤ c :=
⟨λ h o' h', (aleph'_le.2 $ h'.le).trans h,
 λ h, begin
  rw [←aleph'_aleph_idx c, aleph'_le, limit_le l],
  intros x h',
  rw [←aleph'_le, aleph'_aleph_idx],
  exact h _ h'
end⟩

theorem aleph'_limit {o : ordinal} (ho : is_limit o) : aleph' o = ⨆ a : Iio o, aleph' a :=
begin
  refine le_antisymm _ (csupr_le' (λ i, aleph'_le.2 (le_of_lt i.2))),
  rw aleph'_le_of_limit ho,
  exact λ a ha, le_csupr (bdd_above_of_small _) (⟨a, ha⟩ : Iio o)
end

@[simp] theorem aleph'_omega : aleph' ω = ℵ₀ :=
eq_of_forall_ge_iff $ λ c, begin
  simp only [aleph'_le_of_limit omega_is_limit, lt_omega, exists_imp_distrib, aleph_0_le],
  exact forall_swap.trans (forall_congr $ λ n, by simp only [forall_eq, aleph'_nat]),
end

/-- `aleph'` and `aleph_idx` form an equivalence between `ordinal` and `cardinal` -/
@[simp] def aleph'_equiv : ordinal ≃ cardinal :=
⟨aleph', aleph_idx, aleph_idx_aleph', aleph'_aleph_idx⟩

/-- The `aleph` function gives the infinite cardinals listed by their
  ordinal index. `aleph 0 = ℵ₀`, `aleph 1 = succ ℵ₀` is the first
  uncountable cardinal, and so on. -/
def aleph (o : ordinal) : cardinal := aleph' (ω + o)

@[simp] theorem aleph_lt {o₁ o₂ : ordinal} : aleph o₁ < aleph o₂ ↔ o₁ < o₂ :=
aleph'_lt.trans (add_lt_add_iff_left _)

@[simp] theorem aleph_le {o₁ o₂ : ordinal} : aleph o₁ ≤ aleph o₂ ↔ o₁ ≤ o₂ :=
le_iff_le_iff_lt_iff_lt.2 aleph_lt

@[simp] theorem max_aleph_eq (o₁ o₂ : ordinal) : max (aleph o₁) (aleph o₂) = aleph (max o₁ o₂) :=
begin
  cases le_total (aleph o₁) (aleph o₂) with h h,
  { rw [max_eq_right h, max_eq_right (aleph_le.1 h)] },
  { rw [max_eq_left h, max_eq_left (aleph_le.1 h)] }
end

@[simp] theorem aleph_succ {o : ordinal} : aleph (succ o) = succ (aleph o) :=
by rw [aleph, add_succ, aleph'_succ, aleph]

@[simp] theorem aleph_zero : aleph 0 = ℵ₀ :=
by rw [aleph, add_zero, aleph'_omega]

theorem aleph_limit {o : ordinal} (ho : is_limit o) : aleph o = ⨆ a : Iio o, aleph a :=
begin
  apply le_antisymm _ (csupr_le' _),
  { rw [aleph, aleph'_limit (ho.add _)],
    refine csupr_mono' (bdd_above_of_small _) _,
    rintro ⟨i, hi⟩,
    cases lt_or_le i ω,
    { rcases lt_omega.1 h with ⟨n, rfl⟩,
      use ⟨0, ho.pos⟩,
      simpa using (nat_lt_aleph_0 n).le },
    { exact ⟨⟨_, (sub_lt_of_le h).2 hi⟩, aleph'_le.2 (le_add_sub _ _)⟩ } },
  { exact λ i, aleph_le.2 (le_of_lt i.2) }
end

theorem aleph_0_le_aleph' {o : ordinal} : ℵ₀ ≤ aleph' o ↔ ω ≤ o :=
by rw [← aleph'_omega, aleph'_le]

theorem aleph_0_le_aleph (o : ordinal) : ℵ₀ ≤ aleph o :=
by { rw [aleph, aleph_0_le_aleph'], apply ordinal.le_add_right }

theorem aleph'_pos {o : ordinal} (ho : 0 < o) : 0 < aleph' o :=
by rwa [←aleph'_zero, aleph'_lt]

theorem aleph_pos (o : ordinal) : 0 < aleph o :=
aleph_0_pos.trans_le (aleph_0_le_aleph o)

@[simp] theorem aleph_to_nat (o : ordinal) : (aleph o).to_nat = 0 :=
to_nat_apply_of_aleph_0_le $ aleph_0_le_aleph o

@[simp] theorem aleph_to_part_enat (o : ordinal) : (aleph o).to_part_enat = ⊤ :=
to_part_enat_apply_of_aleph_0_le $ aleph_0_le_aleph o

instance nonempty_out_aleph (o : ordinal) : nonempty (aleph o).ord.out.α :=
begin
  rw [out_nonempty_iff_ne_zero, ←ord_zero],
  exact λ h, (ord_injective h).not_gt (aleph_pos o)
end

theorem ord_aleph_is_limit (o : ordinal) : is_limit (aleph o).ord :=
ord_is_limit $ aleph_0_le_aleph _

instance (o : ordinal) : no_max_order (aleph o).ord.out.α :=
out_no_max_of_succ_lt (ord_aleph_is_limit o).2

theorem exists_aleph {c : cardinal} : ℵ₀ ≤ c ↔ ∃ o, c = aleph o :=
⟨λ h, ⟨aleph_idx c - ω,
  by { rw [aleph, ordinal.add_sub_cancel_of_le, aleph'_aleph_idx],
       rwa [← aleph_0_le_aleph', aleph'_aleph_idx] }⟩,
 λ ⟨o, e⟩, e.symm ▸ aleph_0_le_aleph _⟩

theorem aleph'_is_normal : is_normal (ord ∘ aleph') :=
⟨λ o, ord_lt_ord.2 $ aleph'_lt.2 $ lt_succ o,
 λ o l a, by simp only [ord_le, aleph'_le_of_limit l]⟩

theorem aleph_is_normal : is_normal (ord ∘ aleph) :=
aleph'_is_normal.trans $ add_is_normal ω

theorem succ_aleph_0 : succ ℵ₀ = aleph 1 :=
by rw [←aleph_zero, ←aleph_succ, ordinal.succ_zero]

lemma aleph_0_lt_aleph_one : ℵ₀ < aleph 1 :=
by { rw ←succ_aleph_0, apply lt_succ }

lemma countable_iff_lt_aleph_one {α : Type*} (s : set α) : s.countable ↔ #s < aleph 1 :=
by rw [←succ_aleph_0, lt_succ_iff, le_aleph_0_iff_set_countable]

/-- Ordinals that are cardinals are unbounded. -/
theorem ord_card_unbounded : unbounded (<) {b : ordinal | b.card.ord = b} :=
unbounded_lt_iff.2 $ λ a, ⟨_, ⟨(by { dsimp, rw card_ord }), (lt_ord_succ_card a).le⟩⟩

theorem eq_aleph'_of_eq_card_ord {o : ordinal} (ho : o.card.ord = o) : ∃ a, (aleph' a).ord = o :=
⟨cardinal.aleph_idx.rel_iso o.card, by simpa using ho⟩

/-- `ord ∘ aleph'` enumerates the ordinals that are cardinals. -/
theorem ord_aleph'_eq_enum_card : ord ∘ aleph' = enum_ord {b : ordinal | b.card.ord = b} :=
begin
  rw [←eq_enum_ord _ ord_card_unbounded, range_eq_iff],
  exact ⟨aleph'_is_normal.strict_mono, ⟨(λ a, (by { dsimp, rw card_ord })),
    λ b hb, eq_aleph'_of_eq_card_ord hb⟩⟩
end

/-- Infinite ordinals that are cardinals are unbounded. -/
theorem ord_card_unbounded' : unbounded (<) {b : ordinal | b.card.ord = b ∧ ω ≤ b} :=
(unbounded_lt_inter_le ω).2 ord_card_unbounded

theorem eq_aleph_of_eq_card_ord {o : ordinal} (ho : o.card.ord = o) (ho' : ω ≤ o) :
  ∃ a, (aleph a).ord = o :=
begin
  cases eq_aleph'_of_eq_card_ord ho with a ha,
  use a - ω,
  unfold aleph,
  rwa ordinal.add_sub_cancel_of_le,
  rwa [←aleph_0_le_aleph', ←ord_le_ord, ha, ord_aleph_0]
end

/-- `ord ∘ aleph` enumerates the infinite ordinals that are cardinals. -/
theorem ord_aleph_eq_enum_card :
  ord ∘ aleph = enum_ord {b : ordinal | b.card.ord = b ∧ ω ≤ b} :=
begin
  rw ←eq_enum_ord _ ord_card_unbounded',
  use aleph_is_normal.strict_mono,
  rw range_eq_iff,
  refine ⟨(λ a, ⟨_, _⟩), λ b hb, eq_aleph_of_eq_card_ord hb.1 hb.2⟩,
  { rw card_ord },
  { rw [←ord_aleph_0, ord_le_ord],
    exact aleph_0_le_aleph _ }
end

/-! ### Beth cardinals -/

/-- Beth numbers are defined so that `beth 0 = ℵ₀`, `beth (succ o) = 2 ^ (beth o)`, and when `o` is
a limit ordinal, `beth o` is the supremum of `beth o'` for `o' < o`.

Assuming the generalized continuum hypothesis, which is undecidable in ZFC, `beth o = aleph o` for
every `o`. -/
def beth (o : ordinal.{u}) : cardinal.{u} :=
limit_rec_on o aleph_0 (λ _ x, 2 ^ x) (λ a ha IH, ⨆ b : Iio a, IH b.1 b.2)

@[simp] theorem beth_zero : beth 0 = aleph_0 :=
limit_rec_on_zero _ _ _

@[simp] theorem beth_succ (o : ordinal) : beth (succ o) = 2 ^ beth o :=
limit_rec_on_succ _ _ _ _

theorem beth_limit {o : ordinal} : is_limit o → beth o = ⨆ a : Iio o, beth a :=
limit_rec_on_limit _ _ _ _

theorem beth_strict_mono : strict_mono beth :=
begin
  intros a b,
  induction b using ordinal.induction with b IH generalizing a,
  intro h,
  rcases zero_or_succ_or_limit b with rfl | ⟨c, rfl⟩ | hb,
  { exact (ordinal.not_lt_zero a h).elim },
  { rw lt_succ_iff at h,
    rw beth_succ,
    apply lt_of_le_of_lt _ (cantor _),
    rcases eq_or_lt_of_le h with rfl | h, { refl },
    exact (IH c (lt_succ c) h).le },
  { apply (cantor _).trans_le,
    rw [beth_limit hb, ←beth_succ],
    exact le_csupr (bdd_above_of_small _) (⟨_, hb.succ_lt h⟩ : Iio b) }
end

lemma beth_mono : monotone beth := beth_strict_mono.monotone

@[simp] theorem beth_lt {o₁ o₂ : ordinal} : beth o₁ < beth o₂ ↔ o₁ < o₂ :=
beth_strict_mono.lt_iff_lt

@[simp] theorem beth_le {o₁ o₂ : ordinal} : beth o₁ ≤ beth o₂ ↔ o₁ ≤ o₂ :=
beth_strict_mono.le_iff_le

theorem aleph_le_beth (o : ordinal) : aleph o ≤ beth o :=
begin
  apply limit_rec_on o,
  { simp },
  { intros o h,
    rw [aleph_succ, beth_succ, succ_le_iff],
    exact (cantor _).trans_le (power_le_power_left two_ne_zero h) },
  { intros o ho IH,
    rw [aleph_limit ho, beth_limit ho],
    exact csupr_mono (bdd_above_of_small _) (λ x, IH x.1 x.2) }
end

theorem aleph_0_le_beth (o : ordinal) : ℵ₀ ≤ beth o :=
(aleph_0_le_aleph o).trans $ aleph_le_beth o

theorem beth_pos (o : ordinal) : 0 < beth o :=
aleph_0_pos.trans_le $ aleph_0_le_beth o

theorem beth_ne_zero (o : ordinal) : beth o ≠ 0 :=
(beth_pos o).ne'

lemma beth_normal : is_normal.{u} (λ o, (beth o).ord) :=
(is_normal_iff_strict_mono_limit _).2 ⟨ord_strict_mono.comp beth_strict_mono, λ o ho a ha,
  by { rw [beth_limit ho, ord_le], exact csupr_le' (λ b, ord_le.1 (ha _ b.2)) }⟩

/-! ### Properties of `mul` -/

/-- If `α` is an infinite type, then `α × α` and `α` have the same cardinality. -/
theorem mul_eq_self {c : cardinal} (h : ℵ₀ ≤ c) : c * c = c :=
begin
  refine le_antisymm _
    (by simpa only [mul_one] using
      mul_le_mul_left' (one_le_aleph_0.trans h) c),
  -- the only nontrivial part is `c * c ≤ c`. We prove it inductively.
  refine acc.rec_on (cardinal.lt_wf.apply c) (λ c _,
    quotient.induction_on c $ λ α IH ol, _) h,
  -- consider the minimal well-order `r` on `α` (a type with cardinality `c`).
  rcases ord_eq α with ⟨r, wo, e⟩, resetI,
  letI := linear_order_of_STO r,
  haveI : is_well_order α (<) := wo,
  -- Define an order `s` on `α × α` by writing `(a, b) < (c, d)` if `max a b < max c d`, or
  -- the max are equal and `a < c`, or the max are equal and `a = c` and `b < d`.
  let g : α × α → α := λ p, max p.1 p.2,
  let f : α × α ↪ ordinal × (α × α) :=
    ⟨λ p:α×α, (typein (<) (g p), p), λ p q, congr_arg prod.snd⟩,
  let s := f ⁻¹'o (prod.lex (<) (prod.lex (<) (<))),
  -- this is a well order on `α × α`.
  haveI : is_well_order _ s := (rel_embedding.preimage _ _).is_well_order,
  /- it suffices to show that this well order is smaller than `r`
     if it were larger, then `r` would be a strict prefix of `s`. It would be contained in
    `β × β` for some `β` of cardinality `< c`. By the inductive assumption, this set has the
    same cardinality as `β` (or it is finite if `β` is finite), so it is `< c`, which is a
    contradiction. -/
  suffices : type s ≤ type r, {exact card_le_card this},
  refine le_of_forall_lt (λ o h, _),
  rcases typein_surj s h with ⟨p, rfl⟩,
  rw [← e, lt_ord],
  refine lt_of_le_of_lt
    (_ : _ ≤ card (succ (typein (<) (g p))) * card (succ (typein (<) (g p)))) _,
  { have : {q | s q p} ⊆ insert (g p) {x | x < g p} ×ˢ insert (g p) {x | x < g p},
    { intros q h,
      simp only [s, embedding.coe_fn_mk, order.preimage, typein_lt_typein, prod.lex_def, typein_inj]
        at h,
      exact max_le_iff.1 (le_iff_lt_or_eq.2 $ h.imp_right and.left) },
    suffices H : (insert (g p) {x | r x (g p)} : set α) ≃ ({x | r x (g p)} ⊕ punit),
    { exact ⟨(set.embedding_of_subset _ _ this).trans
        ((equiv.set.prod _ _).trans (H.prod_congr H)).to_embedding⟩ },
    refine (equiv.set.insert _).trans
      ((equiv.refl _).sum_congr punit_equiv_punit),
    apply @irrefl _ r },
  cases lt_or_le (card (succ (typein (<) (g p)))) ℵ₀ with qo qo,
  { exact (mul_lt_aleph_0 qo qo).trans_le ol },
  { suffices, {exact (IH _ this qo).trans_lt this},
    rw ← lt_ord, apply (ord_is_limit ol).2,
    rw [mk_def, e], apply typein_lt_type }
end

end using_ordinals

/-- If `α` and `β` are infinite types, then the cardinality of `α × β` is the maximum
of the cardinalities of `α` and `β`. -/
theorem mul_eq_max {a b : cardinal} (ha : ℵ₀ ≤ a) (hb : ℵ₀ ≤ b) : a * b = max a b :=
le_antisymm
  (mul_eq_self (ha.trans (le_max_left a b)) ▸
    mul_le_mul' (le_max_left _ _) (le_max_right _ _)) $
max_le
  (by simpa only [mul_one] using
    mul_le_mul_left' (one_le_aleph_0.trans hb) a)
  (by simpa only [one_mul] using
    mul_le_mul_right' (one_le_aleph_0.trans ha) b)

@[simp] theorem mul_mk_eq_max {α β : Type*} [infinite α] [infinite β] : #α * #β = max (#α) (#β) :=
mul_eq_max (aleph_0_le_mk α) (aleph_0_le_mk β)

@[simp] theorem aleph_mul_aleph (o₁ o₂ : ordinal) : aleph o₁ * aleph o₂ = aleph (max o₁ o₂) :=
by rw [cardinal.mul_eq_max (aleph_0_le_aleph o₁) (aleph_0_le_aleph o₂), max_aleph_eq]

@[simp] theorem aleph_0_mul_eq {a : cardinal} (ha : ℵ₀ ≤ a) : ℵ₀ * a = a :=
(mul_eq_max le_rfl ha).trans (max_eq_right ha)

@[simp] theorem mul_aleph_0_eq {a : cardinal} (ha : ℵ₀ ≤ a) : a * ℵ₀ = a :=
(mul_eq_max ha le_rfl).trans (max_eq_left ha)

@[simp] theorem aleph_0_mul_mk_eq {α : Type*} [infinite α] : ℵ₀ * #α = #α :=
aleph_0_mul_eq (aleph_0_le_mk α)

@[simp] theorem mk_mul_aleph_0_eq {α : Type*} [infinite α] : #α * ℵ₀ = #α :=
mul_aleph_0_eq (aleph_0_le_mk α)

@[simp] theorem aleph_0_mul_aleph (o : ordinal) : ℵ₀ * aleph o = aleph o :=
aleph_0_mul_eq (aleph_0_le_aleph o)

@[simp] theorem aleph_mul_aleph_0 (o : ordinal) : aleph o * ℵ₀ = aleph o :=
mul_aleph_0_eq (aleph_0_le_aleph o)

theorem mul_lt_of_lt {a b c : cardinal} (hc : ℵ₀ ≤ c) (h1 : a < c) (h2 : b < c) : a * b < c :=
(mul_le_mul' (le_max_left a b) (le_max_right a b)).trans_lt $
(lt_or_le (max a b) ℵ₀).elim
  (λ h, (mul_lt_aleph_0 h h).trans_le hc)
  (λ h, by { rw mul_eq_self h, exact max_lt h1 h2 })

lemma mul_le_max_of_aleph_0_le_left {a b : cardinal} (h : ℵ₀ ≤ a) : a * b ≤ max a b :=
begin
  convert mul_le_mul' (le_max_left a b) (le_max_right a b),
  rw mul_eq_self,
  refine h.trans (le_max_left a b)
end

lemma mul_eq_max_of_aleph_0_le_left {a b : cardinal} (h : ℵ₀ ≤ a) (h' : b ≠ 0) : a * b = max a b :=
begin
  cases le_or_lt ℵ₀ b with hb hb, { exact mul_eq_max h hb },
  refine (mul_le_max_of_aleph_0_le_left h).antisymm _,
  have : b ≤ a, from hb.le.trans h,
  rw [max_eq_left this],
  convert mul_le_mul_left' (one_le_iff_ne_zero.mpr h') _, rw [mul_one],
end

lemma mul_le_max_of_aleph_0_le_right {a b : cardinal} (h : ℵ₀ ≤ b) : a * b ≤ max a b :=
by simpa only [mul_comm, max_comm] using mul_le_max_of_aleph_0_le_left h

lemma mul_eq_max_of_aleph_0_le_right {a b : cardinal} (h' : a ≠ 0) (h : ℵ₀ ≤ b) : a * b = max a b :=
begin
  rw [mul_comm, max_comm],
  exact mul_eq_max_of_aleph_0_le_left h h'
end

lemma mul_eq_max' {a b : cardinal} (h : ℵ₀ ≤ a * b) : a * b = max a b :=
begin
  rcases aleph_0_le_mul_iff.mp h with ⟨ha, hb, ha' | hb'⟩,
  { exact mul_eq_max_of_aleph_0_le_left ha' hb },
  { exact mul_eq_max_of_aleph_0_le_right ha hb' }
end

theorem mul_le_max (a b : cardinal) : a * b ≤ max (max a b) ℵ₀ :=
begin
  rcases eq_or_ne a 0 with rfl | ha0, { simp },
  rcases eq_or_ne b 0 with rfl | hb0, { simp },
  cases le_or_lt ℵ₀ a with ha ha,
  { rw [mul_eq_max_of_aleph_0_le_left ha hb0],
    exact le_max_left _ _ },
  { cases le_or_lt ℵ₀ b with hb hb,
    { rw [mul_comm, mul_eq_max_of_aleph_0_le_left hb ha0, max_comm],
      exact le_max_left _ _ },
    { exact le_max_of_le_right (mul_lt_aleph_0 ha hb).le } }
end

lemma mul_eq_left {a b : cardinal} (ha : ℵ₀ ≤ a) (hb : b ≤ a) (hb' : b ≠ 0) : a * b = a :=
by { rw [mul_eq_max_of_aleph_0_le_left ha hb', max_eq_left hb] }

lemma mul_eq_right {a b : cardinal} (hb : ℵ₀ ≤ b) (ha : a ≤ b) (ha' : a ≠ 0) : a * b = b :=
by { rw [mul_comm, mul_eq_left hb ha ha'] }

lemma le_mul_left {a b : cardinal} (h : b ≠ 0) : a ≤ b * a :=
by { convert mul_le_mul_right' (one_le_iff_ne_zero.mpr h) _,
  rw [one_mul] }

lemma le_mul_right {a b : cardinal} (h : b ≠ 0) : a ≤ a * b :=
by { rw [mul_comm], exact le_mul_left h }

lemma mul_eq_left_iff {a b : cardinal} : a * b = a ↔ ((max ℵ₀ b ≤ a ∧ b ≠ 0) ∨ b = 1 ∨ a = 0) :=
begin
  rw max_le_iff,
  refine ⟨λ h, _, _⟩,
  { cases le_or_lt ℵ₀ a with ha ha,
    { have : a ≠ 0, { rintro rfl, exact ha.not_lt aleph_0_pos },
      left, use ha,
      { rw ←not_lt, exact λ hb, ne_of_gt (hb.trans_le (le_mul_left this)) h },
      { rintro rfl, apply this, rw mul_zero at h, exact h.symm }},
    right, by_cases h2a : a = 0, { exact or.inr h2a },
    have hb : b ≠ 0, { rintro rfl, apply h2a, rw mul_zero at h, exact h.symm },
    left, rw [←h, mul_lt_aleph_0_iff, lt_aleph_0, lt_aleph_0] at ha,
    rcases ha with rfl|rfl|⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩, contradiction, contradiction,
    rw ←ne at h2a, rw ←one_le_iff_ne_zero at h2a hb, norm_cast at h2a hb h ⊢,
    apply le_antisymm _ hb, rw ←not_lt,
    apply λ h2b, ne_of_gt _ h, conv_lhs { rw ←mul_one n },
    rwa mul_lt_mul_left, apply nat.lt_of_succ_le h2a },
  { rintro (⟨⟨ha, hab⟩, hb⟩|rfl|rfl),
    { rw [mul_eq_max_of_aleph_0_le_left ha hb, max_eq_left hab] },
    all_goals { simp }}
end

/-! ### Properties of `add` -/

/-- If `α` is an infinite type, then `α ⊕ α` and `α` have the same cardinality. -/
theorem add_eq_self {c : cardinal} (h : ℵ₀ ≤ c) : c + c = c :=
le_antisymm
  (by simpa only [nat.cast_bit0, nat.cast_one, mul_eq_self h, two_mul] using
     mul_le_mul_right' ((nat_lt_aleph_0 2).le.trans h) c)
  (self_le_add_left c c)

/-- If `α` is an infinite type, then the cardinality of `α ⊕ β` is the maximum
of the cardinalities of `α` and `β`. -/
theorem add_eq_max {a b : cardinal} (ha : ℵ₀ ≤ a) : a + b = max a b :=
le_antisymm
  (add_eq_self (ha.trans (le_max_left a b)) ▸
    add_le_add (le_max_left _ _) (le_max_right _ _)) $
max_le (self_le_add_right _ _) (self_le_add_left _ _)

theorem add_eq_max' {a b : cardinal} (ha : ℵ₀ ≤ b) : a + b = max a b :=
by rw [add_comm, max_comm, add_eq_max ha]

@[simp] theorem add_mk_eq_max {α β : Type*} [infinite α] : #α + #β = max (#α) (#β) :=
add_eq_max (aleph_0_le_mk α)

@[simp] theorem add_mk_eq_max' {α β : Type*} [infinite β] : #α + #β = max (#α) (#β) :=
add_eq_max' (aleph_0_le_mk β)

theorem add_le_max (a b : cardinal) : a + b ≤ max (max a b) ℵ₀ :=
begin
  cases le_or_lt ℵ₀ a with ha ha,
  { rw [add_eq_max ha],
    exact le_max_left _ _ },
  { cases le_or_lt ℵ₀ b with hb hb,
    { rw [add_comm, add_eq_max hb, max_comm],
      exact le_max_left _ _ },
    { exact le_max_of_le_right (add_lt_aleph_0 ha hb).le } }
end

theorem add_le_of_le {a b c : cardinal} (hc : ℵ₀ ≤ c) (h1 : a ≤ c) (h2 : b ≤ c) : a + b ≤ c :=
(add_le_add h1 h2).trans $ le_of_eq $ add_eq_self hc

theorem add_lt_of_lt {a b c : cardinal} (hc : ℵ₀ ≤ c) (h1 : a < c) (h2 : b < c) : a + b < c :=
(add_le_add (le_max_left a b) (le_max_right a b)).trans_lt $
(lt_or_le (max a b) ℵ₀).elim
  (λ h, (add_lt_aleph_0 h h).trans_le hc)
  (λ h, by rw add_eq_self h; exact max_lt h1 h2)

lemma eq_of_add_eq_of_aleph_0_le {a b c : cardinal} (h : a + b = c) (ha : a < c) (hc : ℵ₀ ≤ c) :
  b = c :=
begin
  apply le_antisymm,
  { rw [← h], apply self_le_add_left },
  rw[← not_lt], intro hb,
  have : a + b < c := add_lt_of_lt hc ha hb,
  simpa [h, lt_irrefl] using this
end

lemma add_eq_left {a b : cardinal} (ha : ℵ₀ ≤ a) (hb : b ≤ a) : a + b = a :=
by { rw [add_eq_max ha, max_eq_left hb] }

lemma add_eq_right {a b : cardinal} (hb : ℵ₀ ≤ b) (ha : a ≤ b) : a + b = b :=
by { rw [add_comm, add_eq_left hb ha] }

lemma add_eq_left_iff {a b : cardinal} : a + b = a ↔ (max ℵ₀ b ≤ a ∨ b = 0) :=
begin
  rw max_le_iff,
  refine ⟨λ h, _, _⟩,
  { cases (le_or_lt ℵ₀ a) with ha ha,
    { left, use ha, rw ←not_lt, apply λ hb, ne_of_gt _ h,
      exact hb.trans_le (self_le_add_left b a) },
    right, rw [←h, add_lt_aleph_0_iff, lt_aleph_0, lt_aleph_0] at ha,
    rcases ha with ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩, norm_cast at h ⊢,
    rw [←add_right_inj, h, add_zero] },
  { rintro (⟨h1, h2⟩|h3),
    { rw [add_eq_max h1, max_eq_left h2] },
    { rw [h3, add_zero] } }
end

lemma add_eq_right_iff {a b : cardinal} : a + b = b ↔ (max ℵ₀ a ≤ b ∨ a = 0) :=
by { rw [add_comm, add_eq_left_iff] }

lemma add_nat_eq {a : cardinal} (n : ℕ) (ha : ℵ₀ ≤ a) : a + n = a :=
add_eq_left ha ((nat_lt_aleph_0 _).le.trans ha)

lemma add_one_eq {a : cardinal} (ha : ℵ₀ ≤ a) : a + 1 = a :=
add_eq_left ha (one_le_aleph_0.trans ha)

@[simp] lemma mk_add_one_eq {α : Type*} [infinite α] : #α + 1 = #α :=
add_one_eq (aleph_0_le_mk α)

protected lemma eq_of_add_eq_add_left {a b c : cardinal} (h : a + b = a + c) (ha : a < ℵ₀) :
  b = c :=
begin
  cases le_or_lt ℵ₀ b with hb hb,
  { have : a < b := ha.trans_le hb,
    rw [add_eq_right hb this.le, eq_comm] at h,
    rw [eq_of_add_eq_of_aleph_0_le h this hb] },
  { have hc : c < ℵ₀,
    { rw ←not_le, intro hc,
      apply lt_irrefl ℵ₀, apply (hc.trans (self_le_add_left _ a)).trans_lt,
      rw ←h, apply add_lt_aleph_0 ha hb },
    rw lt_aleph_0 at *,
    rcases ha with ⟨n, rfl⟩, rcases hb with ⟨m, rfl⟩, rcases hc with ⟨k, rfl⟩,
    norm_cast at h ⊢, apply add_left_cancel h }
end

protected lemma eq_of_add_eq_add_right {a b c : cardinal} (h : a + b = c + b) (hb : b < ℵ₀) :
  a = c :=
by { rw [add_comm a b, add_comm c b] at h, exact cardinal.eq_of_add_eq_add_left h hb }

@[simp] theorem aleph_add_aleph (o₁ o₂ : ordinal) : aleph o₁ + aleph o₂ = aleph (max o₁ o₂) :=
by rw [cardinal.add_eq_max (aleph_0_le_aleph o₁), max_aleph_eq]

theorem principal_add_ord {c : cardinal} (hc : ℵ₀ ≤ c) : ordinal.principal (+) c.ord :=
λ a b ha hb, by { rw [lt_ord, ordinal.card_add] at *, exact add_lt_of_lt hc ha hb }

theorem principal_add_aleph (o : ordinal) : ordinal.principal (+) (aleph o).ord :=
principal_add_ord $ aleph_0_le_aleph o

lemma add_right_inj_of_lt_aleph_0 {α β γ : cardinal} (γ₀ : γ < aleph_0) :
  α + γ = β + γ ↔ α = β :=
⟨λ h, cardinal.eq_of_add_eq_add_right h γ₀, λ h, congr_fun (congr_arg (+) h) γ⟩

@[simp] lemma add_nat_inj {α β : cardinal} (n : ℕ) :
  α + n = β + n ↔ α = β :=
add_right_inj_of_lt_aleph_0 (nat_lt_aleph_0 _)

@[simp] lemma add_one_inj {α β : cardinal} :
  α + 1 = β + 1 ↔ α = β :=
add_right_inj_of_lt_aleph_0 one_lt_aleph_0

lemma add_le_add_iff_of_lt_aleph_0 {α β γ : cardinal} (γ₀ : γ < cardinal.aleph_0) :
  α + γ ≤ β + γ ↔ α ≤ β :=
begin
  refine ⟨λ h, _, λ h, add_le_add_right h γ⟩,
  contrapose h,
  rw [not_le, lt_iff_le_and_ne, ne] at h ⊢,
  exact ⟨add_le_add_right h.1 γ, mt (add_right_inj_of_lt_aleph_0 γ₀).1 h.2⟩,
end

@[simp] lemma add_nat_le_add_nat_iff_of_lt_aleph_0 {α β : cardinal} (n : ℕ) :
  α + n ≤ β + n ↔ α ≤ β :=
add_le_add_iff_of_lt_aleph_0 (nat_lt_aleph_0 n)

@[simp] lemma add_one_le_add_one_iff_of_lt_aleph_0 {α β : cardinal} :
  α + 1 ≤ β + 1 ↔ α ≤ β :=
add_le_add_iff_of_lt_aleph_0 one_lt_aleph_0

/-! ### Properties about power -/

theorem pow_le {κ μ : cardinal.{u}} (H1 : ℵ₀ ≤ κ) (H2 : μ < ℵ₀) : κ ^ μ ≤ κ :=
let ⟨n, H3⟩ := lt_aleph_0.1 H2 in
H3.symm ▸ (quotient.induction_on κ (λ α H1, nat.rec_on n
  (lt_of_lt_of_le (by { rw [nat.cast_zero, power_zero], exact one_lt_aleph_0 }) H1).le
  (λ n ih, trans_rel_left _
    (by { rw [nat.cast_succ, power_add, power_one], exact mul_le_mul_right' ih _ })
    (mul_eq_self H1))) H1)

theorem pow_eq {κ μ : cardinal.{u}} (H1 : ℵ₀ ≤ κ) (H2 : 1 ≤ μ) (H3 : μ < ℵ₀) : κ ^ μ = κ :=
(pow_le H1 H3).antisymm $ self_le_power κ H2

lemma power_self_eq {c : cardinal} (h : ℵ₀ ≤ c) : c ^ c = 2 ^ c :=
begin
  apply ((power_le_power_right $ (cantor c).le).trans _).antisymm,
  { convert power_le_power_right ((nat_lt_aleph_0 2).le.trans h), apply nat.cast_two.symm },
  { rw [←power_mul, mul_eq_self h] }
end

lemma prod_eq_two_power {ι : Type u} [infinite ι] {c : ι → cardinal.{v}} (h₁ : ∀ i, 2 ≤ c i)
  (h₂ : ∀ i, lift.{u} (c i) ≤ lift.{v} (#ι)) :
  prod c = 2 ^ lift.{v} (#ι) :=
begin
  rw [← lift_id' (prod c), lift_prod, ← lift_two_power],
  apply le_antisymm,
  { refine (prod_le_prod _ _ h₂).trans_eq _,
    rw [prod_const, lift_lift, ← lift_power, power_self_eq (aleph_0_le_mk ι), lift_umax.{u v}] },
  { rw [← prod_const', lift_prod],
    refine prod_le_prod _ _ (λ i, _),
    rw [lift_two, ← lift_two.{u v}, lift_le],
    exact h₁ i }
end

lemma power_eq_two_power {c₁ c₂ : cardinal} (h₁ : ℵ₀ ≤ c₁) (h₂ : 2 ≤ c₂) (h₂' : c₂ ≤ c₁) :
  c₂ ^ c₁ = 2 ^ c₁ :=
le_antisymm (power_self_eq h₁ ▸ power_le_power_right h₂') (power_le_power_right h₂)

lemma nat_power_eq {c : cardinal.{u}} (h : ℵ₀ ≤ c) {n : ℕ} (hn : 2 ≤ n) :
  (n : cardinal.{u}) ^ c = 2 ^ c :=
power_eq_two_power h (by assumption_mod_cast) ((nat_lt_aleph_0 n).le.trans h)

lemma power_nat_le {c : cardinal.{u}} {n : ℕ} (h : ℵ₀ ≤ c) : c ^ n ≤ c :=
pow_le h (nat_lt_aleph_0 n)

lemma power_nat_eq {c : cardinal.{u}} {n : ℕ} (h1 : ℵ₀ ≤ c) (h2 : 1 ≤ n) : c ^ n = c :=
pow_eq h1 (by exact_mod_cast h2) (nat_lt_aleph_0 n)

lemma power_nat_le_max {c : cardinal.{u}} {n : ℕ} : c ^ (n : cardinal.{u}) ≤ max c ℵ₀ :=
begin
  cases le_or_lt ℵ₀ c with hc hc,
  { exact le_max_of_le_left (power_nat_le hc) },
  { exact le_max_of_le_right ((power_lt_aleph_0 hc (nat_lt_aleph_0 _)).le) }
end

lemma powerlt_aleph_0 {c : cardinal} (h : ℵ₀ ≤ c) : c ^< ℵ₀ = c :=
begin
  apply le_antisymm,
  { rw powerlt_le, intro c', rw lt_aleph_0, rintro ⟨n, rfl⟩, apply power_nat_le h },
  convert le_powerlt c one_lt_aleph_0, rw power_one
end

lemma powerlt_aleph_0_le (c : cardinal) : c ^< ℵ₀ ≤ max c ℵ₀ :=
begin
  cases le_or_lt ℵ₀ c,
  { rw powerlt_aleph_0 h, apply le_max_left },
  rw powerlt_le,
  exact λ c' hc', (power_lt_aleph_0 h hc').le.trans (le_max_right _ _)
end

/-! ### Computing cardinality of various types -/

@[simp] theorem mk_list_eq_mk (α : Type u) [infinite α] : #(list α) = #α :=
have H1 : ℵ₀ ≤ #α := aleph_0_le_mk α,
eq.symm $ le_antisymm ⟨⟨λ x, [x], λ x y H, (list.cons.inj H).1⟩⟩ $
calc  #(list α)
    = sum (λ n : ℕ, #α ^ (n : cardinal.{u})) : mk_list_eq_sum_pow α
... ≤ sum (λ n : ℕ, #α) : sum_le_sum _ _ $ λ n, pow_le H1 $ nat_lt_aleph_0 n
... = #α : by simp [H1]

theorem mk_list_eq_aleph_0 (α : Type u) [countable α] [nonempty α] : #(list α) = ℵ₀ :=
mk_le_aleph_0.antisymm (aleph_0_le_mk _)

theorem mk_list_eq_max_mk_aleph_0 (α : Type u) [nonempty α] : #(list α) = max (#α) ℵ₀ :=
begin
  casesI finite_or_infinite α,
  { rw [mk_list_eq_aleph_0, eq_comm, max_eq_right],
    exact mk_le_aleph_0 },
  { rw [mk_list_eq_mk, eq_comm, max_eq_left],
    exact aleph_0_le_mk α }
end

theorem mk_list_le_max (α : Type u) : #(list α) ≤ max ℵ₀ (#α) :=
begin
  casesI finite_or_infinite α,
  { exact mk_le_aleph_0.trans (le_max_left _ _) },
  { rw mk_list_eq_mk,
    apply le_max_right }
end

@[simp] theorem mk_finset_of_infinite (α : Type u) [infinite α] : #(finset α) = #α :=
eq.symm $ le_antisymm (mk_le_of_injective (λ x y, finset.singleton_inj.1)) $
calc #(finset α) ≤ #(list α) : mk_le_of_surjective list.to_finset_surjective
... = #α : mk_list_eq_mk α

@[simp] lemma mk_finsupp_lift_of_infinite (α : Type u) (β : Type v) [infinite α] [has_zero β]
  [nontrivial β] : #(α →₀ β) = max (lift.{v} (#α)) (lift.{u} (#β)) :=
begin
  apply le_antisymm,
  { calc #(α →₀ β) ≤ # (finset (α × β)) : mk_le_of_injective (finsupp.graph_injective α β)
    ... = #(α × β) : mk_finset_of_infinite _
    ... = max (lift.{v} (#α)) (lift.{u} (#β)) :
      by rw [mk_prod, mul_eq_max_of_aleph_0_le_left]; simp },
  { apply max_le;
    rw [←lift_id (# (α →₀ β)), ←lift_umax],
    { cases exists_ne (0 : β) with b hb,
      exact lift_mk_le.{u (max u v) v}.2 ⟨⟨_, finsupp.single_left_injective hb⟩⟩ },
    { inhabit α,
      exact lift_mk_le.{v (max u v) u}.2 ⟨⟨_, finsupp.single_injective default⟩⟩ } }
end

lemma mk_finsupp_of_infinite (α β : Type u) [infinite α] [has_zero β]
  [nontrivial β] : #(α →₀ β) = max (#α) (#β) :=
by simp

@[simp] lemma mk_finsupp_lift_of_infinite' (α : Type u) (β : Type v) [nonempty α]
  [has_zero β] [infinite β] : #(α →₀ β) = max (lift.{v} (#α)) (lift.{u} (#β)) :=
begin
  casesI fintype_or_infinite α,
  { rw mk_finsupp_lift_of_fintype,
    have : ℵ₀ ≤ (#β).lift := aleph_0_le_lift.2 (aleph_0_le_mk β),
    rw [max_eq_right (le_trans _ this), power_nat_eq this],
    exacts [fintype.card_pos, lift_le_aleph_0.2 (lt_aleph_0_of_finite _).le] },
  { apply mk_finsupp_lift_of_infinite },
end

lemma mk_finsupp_of_infinite' (α β : Type u) [nonempty α] [has_zero β] [infinite β] :
  #(α →₀ β) = max (#α) (#β) := by simp

lemma mk_finsupp_nat (α : Type u) [nonempty α] : #(α →₀ ℕ) = max (#α) ℵ₀ := by simp

@[simp] lemma mk_multiset_of_nonempty (α : Type u) [nonempty α] : #(multiset α) = max (#α) ℵ₀ :=
multiset.to_finsupp.to_equiv.cardinal_eq.trans (mk_finsupp_nat α)

lemma mk_multiset_of_infinite (α : Type u) [infinite α] : #(multiset α) = #α := by simp

@[simp] lemma mk_multiset_of_is_empty (α : Type u) [is_empty α] : #(multiset α) = 1 :=
multiset.to_finsupp.to_equiv.cardinal_eq.trans (by simp)

lemma mk_multiset_of_countable (α : Type u) [countable α] [nonempty α] : #(multiset α) = ℵ₀ :=
multiset.to_finsupp.to_equiv.cardinal_eq.trans (by simp)

lemma mk_bounded_set_le_of_infinite (α : Type u) [infinite α] (c : cardinal) :
  #{t : set α // #t ≤ c} ≤ #α ^ c :=
begin
  refine le_trans _ (by rw [←add_one_eq (aleph_0_le_mk α)]),
  induction c using cardinal.induction_on with β,
  fapply mk_le_of_surjective,
  { intro f, use sum.inl ⁻¹' range f,
    refine le_trans (mk_preimage_of_injective _ _ (λ x y, sum.inl.inj)) _,
    apply mk_range_le },
  rintro ⟨s, ⟨g⟩⟩,
  use λ y, if h : ∃(x : s), g x = y then sum.inl (classical.some h).val else sum.inr ⟨⟩,
  apply subtype.eq, ext,
  split,
  { rintro ⟨y, h⟩, dsimp only at h, by_cases h' : ∃ (z : s), g z = y,
    { rw [dif_pos h'] at h, cases sum.inl.inj h, exact (classical.some h').2 },
    { rw [dif_neg h'] at h, cases h }},
  { intro h, have : ∃(z : s), g z = g ⟨x, h⟩, exact ⟨⟨x, h⟩, rfl⟩,
    use g ⟨x, h⟩, dsimp only, rw [dif_pos this], congr',
    suffices : classical.some this = ⟨x, h⟩, exact congr_arg subtype.val this,
    apply g.2, exact classical.some_spec this }
end

lemma mk_bounded_set_le (α : Type u) (c : cardinal) :
  #{t : set α // #t ≤ c} ≤ max (#α) ℵ₀ ^ c :=
begin
  transitivity #{t : set (ulift.{u} ℕ ⊕ α) // #t ≤ c},
  { refine ⟨embedding.subtype_map _ _⟩, apply embedding.image,
    use sum.inr, apply sum.inr.inj, intros s hs, exact mk_image_le.trans hs },
  apply (mk_bounded_set_le_of_infinite (ulift.{u} ℕ ⊕ α) c).trans,
  rw [max_comm, ←add_eq_max]; refl
end

lemma mk_bounded_subset_le {α : Type u} (s : set α) (c : cardinal.{u}) :
  #{t : set α // t ⊆ s ∧ #t ≤ c} ≤ max (#s) ℵ₀ ^ c :=
begin
  refine le_trans _ (mk_bounded_set_le s c),
  refine ⟨embedding.cod_restrict _ _ _⟩,
  use λ t, coe ⁻¹' t.1,
  { rintros ⟨t, ht1, ht2⟩ ⟨t', h1t', h2t'⟩ h, apply subtype.eq, dsimp only at h ⊢,
    refine (preimage_eq_preimage' _ _).1 h; rw [subtype.range_coe]; assumption },
  rintro ⟨t, h1t, h2t⟩, exact (mk_preimage_of_injective _ _ subtype.val_injective).trans h2t
end

/-! ### Properties of `compl` -/

lemma mk_compl_of_infinite {α : Type*} [infinite α] (s : set α) (h2 : #s < #α) :
  #(sᶜ : set α) = #α :=
by { refine eq_of_add_eq_of_aleph_0_le _ h2 (aleph_0_le_mk α), exact mk_sum_compl s }

lemma mk_compl_finset_of_infinite {α : Type*} [infinite α] (s : finset α) :
  #((↑s)ᶜ : set α) = #α :=
by { apply mk_compl_of_infinite, exact (finset_card_lt_aleph_0 s).trans_le (aleph_0_le_mk α) }

lemma mk_compl_eq_mk_compl_infinite {α : Type*} [infinite α] {s t : set α} (hs : #s < #α)
  (ht : #t < #α) : #(sᶜ : set α) = #(tᶜ : set α) :=
by { rw [mk_compl_of_infinite s hs, mk_compl_of_infinite t ht] }

lemma mk_compl_eq_mk_compl_finite_lift {α : Type u} {β : Type v} [finite α]
  {s : set α} {t : set β} (h1 : lift.{max v w} (#α) = lift.{max u w} (#β))
  (h2 : lift.{max v w} (#s) = lift.{max u w} (#t)) :
  lift.{max v w} (#(sᶜ : set α)) = lift.{max u w} (#(tᶜ : set β)) :=
begin
  casesI nonempty_fintype α,
  rcases lift_mk_eq.1 h1 with ⟨e⟩, letI : fintype β := fintype.of_equiv α e,
  replace h1 : fintype.card α = fintype.card β := (fintype.of_equiv_card _).symm,
  classical,
  lift s to finset α using s.to_finite,
  lift t to finset β using t.to_finite,
  simp only [finset.coe_sort_coe, mk_coe_finset, lift_nat_cast, nat.cast_inj] at h2,
  simp only [← finset.coe_compl, finset.coe_sort_coe, mk_coe_finset, finset.card_compl,
    lift_nat_cast, nat.cast_inj, h1, h2]
end

lemma mk_compl_eq_mk_compl_finite {α β : Type u} [finite α] {s : set α} {t : set β}
  (h1 : #α = #β) (h : #s = #t) : #(sᶜ : set α) = #(tᶜ : set β) :=
by { rw ← lift_inj, apply mk_compl_eq_mk_compl_finite_lift; rwa [lift_inj] }

lemma mk_compl_eq_mk_compl_finite_same {α : Type*} [finite α] {s t : set α}
  (h : #s = #t) : #(sᶜ : set α) = #(tᶜ : set α) :=
mk_compl_eq_mk_compl_finite rfl h

/-! ### Extending an injection to an equiv -/

theorem extend_function {α β : Type*} {s : set α} (f : s ↪ β)
  (h : nonempty ((sᶜ : set α) ≃ ((range f)ᶜ : set β))) :
  ∃ (g : α ≃ β), ∀ x : s, g x = f x :=
begin
  intros, have := h, cases this with g,
  let h : α ≃ β := (set.sum_compl (s : set α)).symm.trans
    ((sum_congr (equiv.of_injective f f.2) g).trans
    (set.sum_compl (range f))),
  refine ⟨h, _⟩, rintro ⟨x, hx⟩, simp [set.sum_compl_symm_apply_of_mem, hx]
end

theorem extend_function_finite {α β : Type*} [finite α] {s : set α} (f : s ↪ β)
  (h : nonempty (α ≃ β)) : ∃ (g : α ≃ β), ∀ x : s, g x = f x :=
begin
  apply extend_function f,
  cases id h with g,
  rw [← lift_mk_eq] at h,
  rw [←lift_mk_eq, mk_compl_eq_mk_compl_finite_lift h],
  rw [mk_range_eq_lift], exact f.2
end

theorem extend_function_of_lt {α β : Type*} {s : set α} (f : s ↪ β) (hs : #s < #α)
  (h : nonempty (α ≃ β)) : ∃ (g : α ≃ β), ∀ x : s, g x = f x :=
begin
  casesI fintype_or_infinite α,
  { exact extend_function_finite f h },
  { apply extend_function f, cases id h with g, haveI := infinite.of_injective _ g.injective,
    rw [← lift_mk_eq'] at h ⊢,
    rwa [mk_compl_of_infinite s hs, mk_compl_of_infinite],
    rwa [← lift_lt, mk_range_eq_of_injective f.injective, ← h, lift_lt] },
end

section bit
/-!
This section proves inequalities for `bit0` and `bit1`, enabling `simp` to solve inequalities
for numeral cardinals. The complexity of the resulting algorithm is not good, as in some cases
`simp` reduces an inequality to a disjunction of two situations, depending on whether a cardinal
is finite or infinite. Since the evaluation of the branches is not lazy, this is bad. It is good
enough for practical situations, though.

For specific numbers, these inequalities could also be deduced from the corresponding
inequalities of natural numbers using `norm_cast`:
```
example : (37 : cardinal) < 42 :=
by { norm_cast, norm_num }
```
-/

lemma bit0_ne_zero (a : cardinal) : ¬bit0 a = 0 ↔ ¬a = 0 :=
by simp [bit0]

@[simp] lemma bit1_ne_zero (a : cardinal) : ¬bit1 a = 0 :=
by simp [bit1]

@[simp] lemma zero_lt_bit0 (a : cardinal) : 0 < bit0 a ↔ 0 < a :=
by { rw ←not_iff_not, simp [bit0], }

@[simp] lemma zero_lt_bit1 (a : cardinal) : 0 < bit1 a :=
zero_lt_one.trans_le (self_le_add_left _ _)

@[simp] lemma one_le_bit0 (a : cardinal) : 1 ≤ bit0 a ↔ 0 < a :=
⟨λ h, (zero_lt_bit0 a).mp (zero_lt_one.trans_le h),
 λ h, (one_le_iff_pos.mpr h).trans (self_le_add_left a a)⟩

@[simp] lemma one_le_bit1 (a : cardinal) : 1 ≤ bit1 a :=
self_le_add_left _ _

theorem bit0_eq_self {c : cardinal} (h : ℵ₀ ≤ c) : bit0 c = c :=
add_eq_self h

@[simp] theorem bit0_lt_aleph_0 {c : cardinal} : bit0 c < ℵ₀ ↔ c < ℵ₀ :=
by simp [bit0, add_lt_aleph_0_iff]

@[simp] theorem aleph_0_le_bit0 {c : cardinal} : ℵ₀ ≤ bit0 c ↔ ℵ₀ ≤ c :=
by { rw ←not_iff_not, simp }

@[simp] theorem bit1_eq_self_iff {c : cardinal} : bit1 c = c ↔ ℵ₀ ≤ c :=
begin
  by_cases h : ℵ₀ ≤ c,
  { simp only [bit1, bit0_eq_self h, h, eq_self_iff_true, add_one_of_aleph_0_le] },
  { refine iff_of_false (ne_of_gt _) h,
    rcases lt_aleph_0.1 (not_le.1 h) with ⟨n, rfl⟩,
    norm_cast,
    dsimp [bit1, bit0],
    linarith }
end

@[simp] theorem bit1_lt_aleph_0 {c : cardinal} : bit1 c < ℵ₀ ↔ c < ℵ₀ :=
by simp [bit1, bit0, add_lt_aleph_0_iff, one_lt_aleph_0]

@[simp] theorem aleph_0_le_bit1 {c : cardinal} : ℵ₀ ≤ bit1 c ↔ ℵ₀ ≤ c :=
by { rw ←not_iff_not, simp }

@[simp] lemma bit0_le_bit0 {a b : cardinal} : bit0 a ≤ bit0 b ↔ a ≤ b :=
begin
  cases le_or_lt ℵ₀ a with ha ha; cases le_or_lt ℵ₀ b with hb hb,
  { rw [bit0_eq_self ha, bit0_eq_self hb] },
  { rw bit0_eq_self ha,
    refine iff_of_false (λ h, _) (hb.trans_le ha).not_le,
    have A : bit0 b < ℵ₀, by simpa using hb,
    exact lt_irrefl _ ((A.trans_le ha).trans_le h) },
  { rw bit0_eq_self hb,
    exact iff_of_true ((bit0_lt_aleph_0.2 ha).le.trans hb) (ha.le.trans hb) },
  { rcases lt_aleph_0.1 ha with ⟨m, rfl⟩,
    rcases lt_aleph_0.1 hb with ⟨n, rfl⟩,
    norm_cast,
    exact bit0_le_bit0 }
end

@[simp] lemma bit0_le_bit1 {a b : cardinal} : bit0 a ≤ bit1 b ↔ a ≤ b :=
begin
  cases le_or_lt ℵ₀ a with ha ha; cases le_or_lt ℵ₀ b with hb hb,
  { rw [bit0_eq_self ha, bit1_eq_self_iff.2 hb] },
  { rw bit0_eq_self ha,
    refine iff_of_false (λ h, _) (hb.trans_le ha).not_le,
    have A : bit1 b < ℵ₀, by simpa using hb,
    exact lt_irrefl _ ((A.trans_le ha).trans_le h) },
  { rw bit1_eq_self_iff.2 hb,
    exact iff_of_true ((bit0_lt_aleph_0.2 ha).le.trans hb) (ha.le.trans hb) },
  { rcases lt_aleph_0.1 ha with ⟨m, rfl⟩,
    rcases lt_aleph_0.1 hb with ⟨n, rfl⟩,
    norm_cast,
    exact nat.bit0_le_bit1_iff }
end

@[simp] lemma bit1_le_bit1 {a b : cardinal} : bit1 a ≤ bit1 b ↔ a ≤ b :=
⟨λ h, bit0_le_bit1.1 ((self_le_add_right (bit0 a) 1).trans h), λ h,
  (add_le_add_right (add_le_add_left h a) 1).trans (add_le_add_right (add_le_add_right h b) 1)⟩

@[simp] lemma bit1_le_bit0 {a b : cardinal} : bit1 a ≤ bit0 b ↔ (a < b ∨ (a ≤ b ∧ ℵ₀ ≤ a)) :=
begin
  cases le_or_lt ℵ₀ a with ha ha; cases le_or_lt ℵ₀ b with hb hb,
  { simp only [bit1_eq_self_iff.mpr ha, bit0_eq_self hb, ha, and_true],
    refine ⟨λ h, or.inr h, λ h, _⟩,
    cases h,
    { exact le_of_lt h },
    { exact h } },
  { rw bit1_eq_self_iff.2 ha,
    refine iff_of_false (λ h, _) (λ h, _),
    { have A : bit0 b < ℵ₀, by simpa using hb,
      exact lt_irrefl _ ((A.trans_le ha).trans_le h) },
    { exact not_le_of_lt (hb.trans_le ha) (h.elim le_of_lt and.left) } },
  { rw bit0_eq_self hb,
    exact iff_of_true ((bit1_lt_aleph_0.2 ha).le.trans hb) (or.inl $ ha.trans_le hb) },
  { rcases lt_aleph_0.1 ha with ⟨m, rfl⟩,
    rcases lt_aleph_0.1 hb with ⟨n, rfl⟩,
    norm_cast,
    simp [not_le.mpr ha] }
end

@[simp] lemma bit0_lt_bit0 {a b : cardinal} : bit0 a < bit0 b ↔ a < b :=
begin
  cases le_or_lt ℵ₀ a with ha ha; cases le_or_lt ℵ₀ b with hb hb,
  { rw [bit0_eq_self ha, bit0_eq_self hb] },
  { rw bit0_eq_self ha,
    refine iff_of_false (λ h, _) (hb.le.trans ha).not_lt,
    have A : bit0 b < ℵ₀, by simpa using hb,
    exact lt_irrefl _ ((A.trans_le ha).trans h) },
  { rw bit0_eq_self hb,
    exact iff_of_true ((bit0_lt_aleph_0.2 ha).trans_le hb) (ha.trans_le hb) },
  { rcases lt_aleph_0.1 ha with ⟨m, rfl⟩,
    rcases lt_aleph_0.1 hb with ⟨n, rfl⟩,
    norm_cast,
    exact bit0_lt_bit0 }
end

@[simp] lemma bit1_lt_bit0 {a b : cardinal} : bit1 a < bit0 b ↔ a < b :=
begin
  cases le_or_lt ℵ₀ a with ha ha; cases le_or_lt ℵ₀ b with hb hb,
  { rw [bit1_eq_self_iff.2 ha, bit0_eq_self hb] },
  { rw bit1_eq_self_iff.2 ha,
    refine iff_of_false (λ h, _) (hb.le.trans ha).not_lt,
    have A : bit0 b < ℵ₀, by simpa using hb,
    exact lt_irrefl _ ((A.trans_le ha).trans h) },
  { rw bit0_eq_self hb,
    exact iff_of_true ((bit1_lt_aleph_0.2 ha).trans_le hb) (ha.trans_le hb) },
  { rcases lt_aleph_0.1 ha with ⟨m, rfl⟩,
    rcases lt_aleph_0.1 hb with ⟨n, rfl⟩,
    norm_cast,
    exact nat.bit1_lt_bit0_iff }
end

@[simp] lemma bit1_lt_bit1 {a b : cardinal} : bit1 a < bit1 b ↔ a < b :=
begin
  cases le_or_lt ℵ₀ a with ha ha; cases le_or_lt ℵ₀ b with hb hb,
  { rw [bit1_eq_self_iff.2 ha, bit1_eq_self_iff.2 hb] },
  { rw bit1_eq_self_iff.2 ha,
    refine iff_of_false (λ h, _) (hb.le.trans ha).not_lt,
    have A : bit1 b < ℵ₀, by simpa using hb,
    exact lt_irrefl _ ((A.trans_le ha).trans h) },
  { rw bit1_eq_self_iff.2 hb,
    exact iff_of_true ((bit1_lt_aleph_0.2 ha).trans_le hb) (ha.trans_le hb) },
  { rcases lt_aleph_0.1 ha with ⟨m, rfl⟩,
    rcases lt_aleph_0.1 hb with ⟨n, rfl⟩,
    norm_cast,
    exact bit1_lt_bit1 }
end

@[simp] lemma bit0_lt_bit1 {a b : cardinal} : bit0 a < bit1 b ↔ (a < b ∨ (a ≤ b ∧ a < ℵ₀)) :=
begin
  cases le_or_lt ℵ₀ a with ha ha; cases le_or_lt ℵ₀ b with hb hb,
  { simp [bit0_eq_self ha, bit1_eq_self_iff.2 hb, not_lt.mpr ha] },
  { rw bit0_eq_self ha,
    refine iff_of_false (λ h, _) (λ h, _),
    { have A : bit1 b < ℵ₀, by simpa using hb,
      exact lt_irrefl _ ((A.trans_le ha).trans h) },
    { exact (hb.trans_le ha).not_le (h.elim le_of_lt and.left) } },
  { rw [bit1_eq_self_iff.2 hb],
    exact iff_of_true ((bit0_lt_aleph_0.2 ha).trans_le hb) (or.inl $ ha.trans_le hb) },
  { rcases lt_aleph_0.1 ha with ⟨m, rfl⟩,
    rcases lt_aleph_0.1 hb with ⟨n, rfl⟩,
    norm_cast,
    simp only [ha, and_true, nat.bit0_lt_bit1_iff, or_iff_right_of_imp le_of_lt] }
end

lemma one_lt_two : (1 : cardinal) < 2 :=
-- This strategy works generally to prove inequalities between numerals in `cardinality`.
by { norm_cast, norm_num }

@[simp] lemma one_lt_bit0 {a : cardinal} : 1 < bit0 a ↔ 0 < a :=
by simp [←bit1_zero]

@[simp] lemma one_lt_bit1 (a : cardinal) : 1 < bit1 a ↔ 0 < a :=
by simp [←bit1_zero]

end bit

end cardinal
