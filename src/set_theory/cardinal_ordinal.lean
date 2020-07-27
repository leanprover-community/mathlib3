/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl, Mario Carneiro
-/

import set_theory.ordinal_arithmetic
import tactic.omega

/-!
# Cardinals and ordinals

Relationships between cardinals and ordinals, properties of cardinals that are proved
using ordinals.

## Main definitions and results

* The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = ℵ₁`, etc. It is an order isomorphism
  between ordinals and cardinals.
* The `aleph` function gives the infinite cardinals listed by their
  ordinal index. `aleph 0 = ω`, `aleph 1 = succ ω` is the first
  uncountable cardinal, and so on.

* `mul_eq_max` and `add_eq_max` state that the product (resp. sum) of two infinite cardinals
  is just their maximum. Several variations around this fact are also given.
* `mk_list_eq_mk` : when `α` is infinite, `α` and `list α` have the same cardinality.
* simp lemmas for inequalities between `bit0 a` and `bit1 b` are registered, making simp
  able to prove inequalities about numeral cardinals.
-/

noncomputable theory

open function cardinal set equiv
open_locale classical cardinal

universes u v w

namespace cardinal
section using_ordinals
open ordinal

theorem ord_is_limit {c} (co : omega ≤ c) : (ord c).is_limit :=
begin
  refine ⟨λ h, omega_ne_zero _, λ a, lt_imp_lt_of_le_imp_le _⟩,
  { rw [← ordinal.le_zero, ord_le] at h,
    simpa only [card_zero, le_zero] using le_trans co h },
  { intro h, rw [ord_le] at h ⊢,
    rwa [← @add_one_of_omega_le (card a), ← card_succ],
    rw [← ord_le, ← le_succ_of_is_limit, ord_le],
    { exact le_trans co h },
    { rw ord_omega, exact omega_is_limit } }
end

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ω = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)
  In this definition, we register additionally that this function is an initial segment,
  i.e., it is order preserving and its range is an initial segment of the ordinals.
  For the basic function version, see `aleph_idx`.
  For an upgraded version stating that the range is everything, see `aleph_idx.order_iso`. -/
def aleph_idx.initial_seg : @initial_seg cardinal ordinal (<) (<) :=
@order_embedding.collapse cardinal ordinal (<) (<) _ cardinal.ord.order_embedding

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ω = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)
  For an upgraded version stating that the range is everything, see `aleph_idx.order_iso`. -/
def aleph_idx : cardinal → ordinal := aleph_idx.initial_seg

@[simp] theorem aleph_idx.initial_seg_coe :
  (aleph_idx.initial_seg : cardinal → ordinal) = aleph_idx := rfl

@[simp] theorem aleph_idx_lt {a b} : aleph_idx a < aleph_idx b ↔ a < b :=
aleph_idx.initial_seg.to_order_embedding.ord.symm

@[simp] theorem aleph_idx_le {a b} : aleph_idx a ≤ aleph_idx b ↔ a ≤ b :=
by rw [← not_lt, ← not_lt, aleph_idx_lt]

theorem aleph_idx.init {a b} : b < aleph_idx a → ∃ c, aleph_idx c = b :=
aleph_idx.initial_seg.init _ _

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ω = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)
  In this version, we register additionally that this function is an order isomorphism
  between cardinals and ordinals.
  For the basic function version, see `aleph_idx`. -/
def aleph_idx.order_iso : @order_iso cardinal.{u} ordinal.{u} (<) (<) :=
@order_iso.of_surjective cardinal.{u} ordinal.{u} (<) (<) aleph_idx.initial_seg.{u} $
(initial_seg.eq_or_principal aleph_idx.initial_seg.{u}).resolve_right $
λ ⟨o, e⟩, begin
  have : ∀ c, aleph_idx c < o := λ c, (e _).2 ⟨_, rfl⟩,
  refine ordinal.induction_on o _ this, introsI α r _ h,
  let s := sup.{u u} (λ a:α, inv_fun aleph_idx (ordinal.typein r a)),
  apply not_le_of_gt (lt_succ_self s),
  have I : injective aleph_idx := aleph_idx.initial_seg.to_embedding.injective,
  simpa only [typein_enum, left_inverse_inv_fun I (succ s)] using
    le_sup.{u u} (λ a, inv_fun aleph_idx (ordinal.typein r a))
      (ordinal.enum r _ (h (succ s))),
end

@[simp] theorem aleph_idx.order_iso_coe :
  (aleph_idx.order_iso : cardinal → ordinal) = aleph_idx := rfl

@[simp] theorem type_cardinal : @ordinal.type cardinal (<) _ = ordinal.univ.{u (u+1)} :=
by rw ordinal.univ_id; exact quotient.sound ⟨aleph_idx.order_iso⟩

@[simp] theorem mk_cardinal : mk cardinal = univ.{u (u+1)} :=
by simpa only [card_type, card_univ] using congr_arg card type_cardinal

/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = ℵ₁`, etc.
  In this version, we register additionally that this function is an order isomorphism
  between ordinals and cardinals.
  For the basic function version, see `aleph'`. -/
def aleph'.order_iso := cardinal.aleph_idx.order_iso.symm

/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = ℵ₁`, etc. -/
def aleph' : ordinal → cardinal := aleph'.order_iso

@[simp] theorem aleph'.order_iso_coe :
  (aleph'.order_iso : ordinal → cardinal) = aleph' := rfl

@[simp] theorem aleph'_lt {o₁ o₂ : ordinal.{u}} : aleph' o₁ < aleph' o₂ ↔ o₁ < o₂ :=
aleph'.order_iso.ord.symm

@[simp] theorem aleph'_le {o₁ o₂ : ordinal.{u}} : aleph' o₁ ≤ aleph' o₂ ↔ o₁ ≤ o₂ :=
le_iff_le_iff_lt_iff_lt.2 aleph'_lt

@[simp] theorem aleph'_aleph_idx (c : cardinal.{u}) : aleph' c.aleph_idx = c :=
cardinal.aleph_idx.order_iso.to_equiv.symm_apply_apply c

@[simp] theorem aleph_idx_aleph' (o : ordinal.{u}) : (aleph' o).aleph_idx = o :=
cardinal.aleph_idx.order_iso.to_equiv.apply_symm_apply o

@[simp] theorem aleph'_zero : aleph' 0 = 0 :=
by rw [← le_zero, ← aleph'_aleph_idx 0, aleph'_le];
   apply ordinal.zero_le

@[simp] theorem aleph'_succ {o : ordinal.{u}} : aleph' o.succ = (aleph' o).succ :=
le_antisymm
 (cardinal.aleph_idx_le.1 $
  by rw [aleph_idx_aleph', ordinal.succ_le, ← aleph'_lt, aleph'_aleph_idx];
     apply cardinal.lt_succ_self)
 (cardinal.succ_le.2 $ aleph'_lt.2 $ ordinal.lt_succ_self _)

@[simp] theorem aleph'_nat : ∀ n : ℕ, aleph' n = n
| 0     := aleph'_zero
| (n+1) := show aleph' (ordinal.succ n) = n.succ,
           by rw [aleph'_succ, aleph'_nat, nat_succ]

theorem aleph'_le_of_limit {o : ordinal.{u}} (l : o.is_limit) {c} :
  aleph' o ≤ c ↔ ∀ o' < o, aleph' o' ≤ c :=
⟨λ h o' h', le_trans (aleph'_le.2 $ le_of_lt h') h,
 λ h, begin
  rw [← aleph'_aleph_idx c, aleph'_le, ordinal.limit_le l],
  intros x h',
  rw [← aleph'_le, aleph'_aleph_idx],
  exact h _ h'
end⟩

@[simp] theorem aleph'_omega : aleph' ordinal.omega = omega :=
eq_of_forall_ge_iff $ λ c, begin
  simp only [aleph'_le_of_limit omega_is_limit, ordinal.lt_omega, exists_imp_distrib, omega_le],
  exact forall_swap.trans (forall_congr $ λ n, by simp only [forall_eq, aleph'_nat]),
end

/-- `aleph'` and `aleph_idx` form an equivalence between `ordinal` and `cardinal` -/
@[simp] def aleph'_equiv : ordinal ≃ cardinal :=
⟨aleph', aleph_idx, aleph_idx_aleph', aleph'_aleph_idx⟩

/-- The `aleph` function gives the infinite cardinals listed by their
  ordinal index. `aleph 0 = ω`, `aleph 1 = succ ω` is the first
  uncountable cardinal, and so on. -/
def aleph (o : ordinal) : cardinal := aleph' (ordinal.omega + o)

@[simp] theorem aleph_lt {o₁ o₂ : ordinal.{u}} : aleph o₁ < aleph o₂ ↔ o₁ < o₂ :=
aleph'_lt.trans (ordinal.add_lt_add_iff_left _)

@[simp] theorem aleph_le {o₁ o₂ : ordinal.{u}} : aleph o₁ ≤ aleph o₂ ↔ o₁ ≤ o₂ :=
le_iff_le_iff_lt_iff_lt.2 aleph_lt

@[simp] theorem aleph_succ {o : ordinal.{u}} : aleph o.succ = (aleph o).succ :=
by rw [aleph, ordinal.add_succ, aleph'_succ]; refl

@[simp] theorem aleph_zero : aleph 0 = omega :=
by simp only [aleph, add_zero, aleph'_omega]

theorem omega_le_aleph' {o : ordinal} : omega ≤ aleph' o ↔ ordinal.omega ≤ o :=
by rw [← aleph'_omega, aleph'_le]

theorem omega_le_aleph (o : ordinal) : omega ≤ aleph o :=
by rw [aleph, omega_le_aleph']; apply ordinal.le_add_right

theorem ord_aleph_is_limit (o : ordinal) : is_limit (aleph o).ord :=
ord_is_limit $ omega_le_aleph _

theorem exists_aleph {c : cardinal} : omega ≤ c ↔ ∃ o, c = aleph o :=
⟨λ h, ⟨aleph_idx c - ordinal.omega,
  by rw [aleph, ordinal.add_sub_cancel_of_le, aleph'_aleph_idx];
     rwa [← omega_le_aleph', aleph'_aleph_idx]⟩,
 λ ⟨o, e⟩, e.symm ▸ omega_le_aleph _⟩

theorem aleph'_is_normal : is_normal (ord ∘ aleph') :=
⟨λ o, ord_lt_ord.2 $ aleph'_lt.2 $ ordinal.lt_succ_self _,
 λ o l a, by simp only [ord_le, aleph'_le_of_limit l]⟩

theorem aleph_is_normal : is_normal (ord ∘ aleph) :=
aleph'_is_normal.trans $ add_is_normal ordinal.omega

/-! ### Properties of `mul` -/

/-- If `α` is an infinite type, then `α × α` and `α` have the same cardinality. -/
theorem mul_eq_self {c : cardinal} (h : omega ≤ c) : c * c = c :=
begin
  refine le_antisymm _
    (by simpa only [mul_one] using mul_le_mul_left c (le_trans (le_of_lt one_lt_omega) h)),
  -- the only nontrivial part is `c * c ≤ c`. We prove it inductively.
  refine acc.rec_on (cardinal.wf.apply c) (λ c _,
    quotient.induction_on c $ λ α IH ol, _) h,
  -- consider the minimal well-order `r` on `α` (a type with cardinality `c`).
  rcases ord_eq α with ⟨r, wo, e⟩, resetI,
  letI := decidable_linear_order_of_STO' r,
  haveI : is_well_order α (<) := wo,
  -- Define an order `s` on `α × α` by writing `(a, b) < (c, d)` if `max a b < max c d`, or
  -- the max are equal and `a < c`, or the max are equal and `a = c` and `b < d`.
  let g : α × α → α := λ p, max p.1 p.2,
  let f : α × α ↪ ordinal × (α × α) :=
    ⟨λ p:α×α, (typein (<) (g p), p), λ p q, congr_arg prod.snd⟩,
  let s := f ⁻¹'o (prod.lex (<) (prod.lex (<) (<))),
  -- this is a well order on `α × α`.
  haveI : is_well_order _ s := (order_embedding.preimage _ _).is_well_order,
  /- it suffices to show that this well order is smaller than `r`
     if it were larger, then `r` would be a strict prefix of `s`. It would be contained in
    `β × β` for some `β` of cardinality `< c`. By the inductive assumption, this set has the
    same cardinality as `β` (or it is finite if `β` is finite), so it is `< c`, which is a
    contradiction. -/
  suffices : type s ≤ type r, {exact card_le_card this},
  refine le_of_forall_lt (λ o h, _),
  rcases typein_surj s h with ⟨p, rfl⟩,
  rw [← e, lt_ord],
  refine lt_of_le_of_lt (_ : _ ≤ card (typein (<) (g p)).succ * card (typein (<) (g p)).succ) _,
  { have : {q|s q p} ⊆ (insert (g p) {x | x < (g p)}).prod (insert (g p) {x | x < (g p)}),
    { intros q h,
      simp only [s, embedding.coe_fn_mk, order.preimage, typein_lt_typein, prod.lex_def, typein_inj] at h,
      exact max_le_iff.1 (le_iff_lt_or_eq.2 $ h.imp_right and.left) },
    suffices H : (insert (g p) {x | r x (g p)} : set α) ≃ ({x | r x (g p)} ⊕ punit),
    { exact ⟨(set.embedding_of_subset _ _ this).trans
        ((equiv.set.prod _ _).trans (H.prod_congr H)).to_embedding⟩ },
    refine (equiv.set.insert _).trans
      ((equiv.refl _).sum_congr punit_equiv_punit),
    apply @irrefl _ r },
  cases lt_or_ge (card (typein (<) (g p)).succ) omega with qo qo,
  { exact lt_of_lt_of_le (mul_lt_omega qo qo) ol },
  { suffices, {exact lt_of_le_of_lt (IH _ this qo) this},
    rw ← lt_ord, apply (ord_is_limit ol).2,
    rw [mk_def, e], apply typein_lt_type }
end

end using_ordinals

/-- If `α` and `β` are infinite types, then the cardinality of `α × β` is the maximum
of the cardinalities of `α` and `β`. -/
theorem mul_eq_max {a b : cardinal} (ha : omega ≤ a) (hb : omega ≤ b) : a * b = max a b :=
le_antisymm
  (mul_eq_self (le_trans ha (le_max_left a b)) ▸
    mul_le_mul (le_max_left _ _) (le_max_right _ _)) $
max_le
  (by simpa only [mul_one] using mul_le_mul_left a (le_trans (le_of_lt one_lt_omega) hb))
  (by simpa only [one_mul] using mul_le_mul_right b (le_trans (le_of_lt one_lt_omega) ha))

theorem mul_lt_of_lt {a b c : cardinal} (hc : omega ≤ c)
  (h1 : a < c) (h2 : b < c) : a * b < c :=
lt_of_le_of_lt (mul_le_mul (le_max_left a b) (le_max_right a b)) $
(lt_or_le (max a b) omega).elim
  (λ h, lt_of_lt_of_le (mul_lt_omega h h) hc)
  (λ h, by rw mul_eq_self h; exact max_lt h1 h2)

lemma mul_le_max_of_omega_le_left {a b : cardinal} (h : omega ≤ a) : a * b ≤ max a b :=
begin
  convert mul_le_mul (le_max_left a b) (le_max_right a b), rw [mul_eq_self],
  refine le_trans h (le_max_left a b)
end

lemma mul_eq_max_of_omega_le_left {a b : cardinal} (h : omega ≤ a) (h' : b ≠ 0) : a * b = max a b :=
begin
  apply le_antisymm, apply mul_le_max_of_omega_le_left h,
  cases le_or_gt omega b with hb hb, rw [mul_eq_max h hb],
  have : b ≤ a, exact le_trans (le_of_lt hb) h,
  rw [max_eq_left this], convert mul_le_mul_left _ (one_le_iff_ne_zero.mpr h'), rw [mul_one],
end

lemma mul_eq_left {a b : cardinal} (ha : omega ≤ a) (hb : b ≤ a) (hb' : b ≠ 0) : a * b = a :=
by { rw [mul_eq_max_of_omega_le_left ha hb', max_eq_left hb] }

lemma mul_eq_right {a b : cardinal} (hb : omega ≤ b) (ha : a ≤ b) (ha' : a ≠ 0) : a * b = b :=
by { rw [mul_comm, mul_eq_left hb ha ha'] }

lemma le_mul_left {a b : cardinal} (h : b ≠ 0) : a ≤ b * a :=
by { convert mul_le_mul_right _ (one_le_iff_ne_zero.mpr h), rw [one_mul] }

lemma le_mul_right {a b : cardinal} (h : b ≠ 0) : a ≤ a * b :=
by { rw [mul_comm], exact le_mul_left h }

lemma mul_eq_left_iff {a b : cardinal} : a * b = a ↔ ((max omega b ≤ a ∧ b ≠ 0) ∨ b = 1 ∨ a = 0) :=
begin
  rw [max_le_iff], split,
  { intro h,
    cases (le_or_lt omega a) with ha ha,
    { have : a ≠ 0, { rintro rfl, exact not_lt_of_le ha omega_pos },
      left, use ha,
      { rw [← not_lt], intro hb, apply ne_of_gt _ h, refine lt_of_lt_of_le hb (le_mul_left this) },
      { rintro rfl, apply this, rw [_root_.mul_zero] at h, subst h }},
    right, by_cases h2a : a = 0, { right, exact h2a },
    have hb : b ≠ 0, { rintro rfl, apply h2a, rw [mul_zero] at h, subst h },
    left, rw [← h, mul_lt_omega_iff, lt_omega, lt_omega] at ha,
    rcases ha with rfl|rfl|⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩, contradiction, contradiction,
    rw [← ne] at h2a, rw [← one_le_iff_ne_zero] at h2a hb, norm_cast at h2a hb h ⊢,
    apply le_antisymm _ hb, rw [← not_lt], intro h2b,
    apply ne_of_gt _ h, rw [gt], conv_lhs { rw [← mul_one n] },
    rwa [mul_lt_mul_left], apply nat.lt_of_succ_le h2a },
  { rintro (⟨⟨ha, hab⟩, hb⟩|rfl|rfl),
    { rw [mul_eq_max_of_omega_le_left ha hb, max_eq_left hab] },
    all_goals {simp}}
end

/-! ### Properties of `add` -/

/-- If `α` is an infinite type, then `α ⊕ α` and `α` have the same cardinality. -/
theorem add_eq_self {c : cardinal} (h : omega ≤ c) : c + c = c :=
le_antisymm
  (by simpa only [nat.cast_bit0, nat.cast_one, mul_eq_self h, two_mul] using
     mul_le_mul_right c (le_trans (le_of_lt $ nat_lt_omega 2) h))
  (le_add_left c c)

/-- If `α` is an infinite type, then the cardinality of `α ⊕ β` is the maximum
of the cardinalities of `α` and `β`. -/
theorem add_eq_max {a b : cardinal} (ha : omega ≤ a) : a + b = max a b :=
le_antisymm
  (add_eq_self (le_trans ha (le_max_left a b)) ▸
    add_le_add (le_max_left _ _) (le_max_right _ _)) $
max_le (le_add_right _ _) (le_add_left _ _)

theorem add_lt_of_lt {a b c : cardinal} (hc : omega ≤ c)
  (h1 : a < c) (h2 : b < c) : a + b < c :=
lt_of_le_of_lt (add_le_add (le_max_left a b) (le_max_right a b)) $
(lt_or_le (max a b) omega).elim
  (λ h, lt_of_lt_of_le (add_lt_omega h h) hc)
  (λ h, by rw add_eq_self h; exact max_lt h1 h2)

lemma eq_of_add_eq_of_omega_le {a b c : cardinal} (h : a + b = c) (ha : a < c) (hc : omega ≤ c) :
  b = c :=
begin
  apply le_antisymm,
  { rw [← h], apply cardinal.le_add_left },
  rw[← not_lt], intro hb,
  have : a + b < c := add_lt_of_lt hc ha hb,
  simpa [h, lt_irrefl] using this
end

lemma add_eq_left {a b : cardinal} (ha : omega ≤ a) (hb : b ≤ a) : a + b = a :=
by { rw [add_eq_max ha, max_eq_left hb] }

lemma add_eq_right {a b : cardinal} (hb : omega ≤ b) (ha : a ≤ b) : a + b = b :=
by { rw [add_comm, add_eq_left hb ha] }

lemma add_eq_left_iff {a b : cardinal} : a + b = a ↔ (max omega b ≤ a ∨ b = 0) :=
begin
  rw [max_le_iff], split,
  { intro h, cases (le_or_lt omega a) with ha ha,
    { left, use ha, rw [← not_lt], intro hb, apply ne_of_gt _ h,
      exact lt_of_lt_of_le hb (le_add_left b a) },
    right, rw [← h, add_lt_omega_iff, lt_omega, lt_omega] at ha,
    rcases ha with ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩, norm_cast at h ⊢,
    rw [← add_right_inj, h, add_zero] },
  { rintro (⟨h1, h2⟩|h3), rw [add_eq_max h1, max_eq_left h2], rw [h3, add_zero] }
end

lemma add_eq_right_iff {a b : cardinal} : a + b = b ↔ (max omega a ≤ b ∨ a = 0) :=
by { rw [add_comm, add_eq_left_iff] }

lemma add_one_eq {a : cardinal} (ha : omega ≤ a) : a + 1 = a :=
have 1 ≤ a, from le_trans (le_of_lt one_lt_omega) ha,
add_eq_left ha this

protected lemma eq_of_add_eq_add_left {a b c : cardinal} (h : a + b = a + c) (ha : a < omega) :
  b = c :=
begin
  cases le_or_lt omega b with hb hb,
  { have : a < b := lt_of_lt_of_le ha hb,
    rw [add_eq_right hb (le_of_lt this), eq_comm] at h,
    rw [eq_of_add_eq_of_omega_le h this hb] },
  { have hc : c < omega,
    { rw [← not_le], intro hc,
      apply lt_irrefl omega, apply lt_of_le_of_lt (le_trans hc (le_add_left _ a)),
      rw [← h], apply add_lt_omega ha hb },
    rw [lt_omega] at *,
    rcases ha with ⟨n, rfl⟩, rcases hb with ⟨m, rfl⟩, rcases hc with ⟨k, rfl⟩,
    norm_cast at h ⊢, apply add_left_cancel h }
end

protected lemma eq_of_add_eq_add_right {a b c : cardinal} (h : a + b = c + b) (hb : b < omega) :
  a = c :=
by { rw [add_comm a b, add_comm c b] at h, exact cardinal.eq_of_add_eq_add_left h hb }

/-! ### Properties about power -/

theorem pow_le {κ μ : cardinal.{u}} (H1 : omega ≤ κ) (H2 : μ < omega) : κ ^ μ ≤ κ :=
let ⟨n, H3⟩ := lt_omega.1 H2 in
H3.symm ▸ (quotient.induction_on κ (λ α H1, nat.rec_on n
  (le_of_lt $ lt_of_lt_of_le (by rw [nat.cast_zero, power_zero];
    from one_lt_omega) H1)
  (λ n ih, trans_rel_left _
    (by rw [nat.cast_succ, power_add, power_one];
      from mul_le_mul_right _ ih)
    (mul_eq_self H1))) H1)

lemma power_self_eq {c : cardinal} (h : omega ≤ c) : c ^ c = 2 ^ c :=
begin
  apply le_antisymm,
  { apply le_trans (power_le_power_right $ le_of_lt $ cantor c), rw [power_mul, mul_eq_self h] },
  { convert power_le_power_right (le_trans (le_of_lt $ nat_lt_omega 2) h), apply nat.cast_two.symm }
end

lemma power_nat_le {c : cardinal.{u}} {n : ℕ} (h  : omega ≤ c) : c ^ (n : cardinal.{u}) ≤ c :=
pow_le h (nat_lt_omega n)

lemma powerlt_omega {c : cardinal} (h : omega ≤ c) : c ^< omega = c :=
begin
  apply le_antisymm,
  { rw [powerlt_le], intro c', rw [lt_omega], rintro ⟨n, rfl⟩, apply power_nat_le h },
  convert le_powerlt one_lt_omega, rw [power_one]
end
lemma powerlt_omega_le (c : cardinal) : c ^< omega ≤ max c omega :=
begin
  cases le_or_gt omega c,
  { rw [powerlt_omega h], apply le_max_left },
  rw [powerlt_le], intros c' hc',
  refine le_trans (le_of_lt $ power_lt_omega h hc') (le_max_right _ _)
end

/-! ### Computing cardinality of various types -/

theorem mk_list_eq_mk {α : Type u} (H1 : omega ≤ mk α) : mk (list α) = mk α :=
eq.symm $ le_antisymm ⟨⟨λ x, [x], λ x y H, (list.cons.inj H).1⟩⟩ $
calc  mk (list α)
    = sum (λ n : ℕ, mk α ^ (n : cardinal.{u})) : mk_list_eq_sum_pow α
... ≤ sum (λ n : ℕ, mk α) : sum_le_sum _ _ $ λ n, pow_le H1 $ nat_lt_omega n
... = sum (λ n : ulift.{u} ℕ, mk α) : quotient.sound
  ⟨@sigma_congr_left _ _ (λ _, quotient.out (mk α)) equiv.ulift.symm⟩
... = omega * mk α : sum_const _ _
... = max (omega) (mk α) : mul_eq_max (le_refl _) H1
... = mk α : max_eq_right H1

theorem mk_finset_eq_mk {α : Type u} (h : omega ≤ mk α) : mk (finset α) = mk α :=
eq.symm $ le_antisymm (mk_le_of_injective (λ x y, finset.singleton_inj.1)) $
calc mk (finset α) ≤ mk (list α) : mk_le_of_surjective list.to_finset_surjective
... = mk α : mk_list_eq_mk h

lemma mk_bounded_set_le_of_omega_le (α : Type u) (c : cardinal) (hα : omega ≤ mk α) :
  mk {t : set α // mk t ≤ c} ≤ mk α ^ c :=
begin
  refine le_trans _ (by rw [←add_one_eq hα]), refine quotient.induction_on c _, clear c, intro β,
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
  mk {t : set α // mk t ≤ c} ≤ max (mk α) omega ^ c :=
begin
  transitivity mk {t : set (ulift.{u} nat ⊕ α) // mk t ≤ c},
  { refine ⟨embedding.subtype_map _ _⟩, apply embedding.image,
    use sum.inr, apply sum.inr.inj, intros s hs, exact le_trans mk_image_le hs },
  refine le_trans
    (mk_bounded_set_le_of_omega_le (ulift.{u} nat ⊕ α) c (le_add_right omega (mk α))) _,
  rw [max_comm, ←add_eq_max]; refl
end

lemma mk_bounded_subset_le {α : Type u} (s : set α) (c : cardinal.{u}) :
  mk {t : set α // t ⊆ s ∧ mk t ≤ c} ≤ max (mk s) omega ^ c :=
begin
  refine le_trans _ (mk_bounded_set_le s c),
  refine ⟨embedding.cod_restrict _ _ _⟩,
  use λ t, coe ⁻¹' t.1,
  { rintros ⟨t, ht1, ht2⟩ ⟨t', h1t', h2t'⟩ h, apply subtype.eq, dsimp only at h ⊢,
    refine (preimage_eq_preimage' _ _).1 h; rw [subtype.range_coe]; assumption },
  rintro ⟨t, h1t, h2t⟩, exact le_trans (mk_preimage_of_injective _ _ subtype.val_injective) h2t
end

/-! ### Properties of `compl` -/

lemma mk_compl_of_omega_le {α : Type*} (s : set α) (h : omega ≤ #α) (h2 : #s < #α) :
  #(sᶜ : set α) = #α :=
by { refine eq_of_add_eq_of_omega_le _ h2 h, exact mk_sum_compl s }

lemma mk_compl_finset_of_omega_le {α : Type*} (s : finset α) (h : omega ≤ #α) :
  #((↑s)ᶜ : set α) = #α :=
by { apply mk_compl_of_omega_le _ h, exact lt_of_lt_of_le (finset_card_lt_omega s) h }

lemma mk_compl_eq_mk_compl_infinite {α : Type*} {s t : set α} (h : omega ≤ #α) (hs : #s < #α)
  (ht : #t < #α) : #(sᶜ : set α) = #(tᶜ : set α) :=
by { rw [mk_compl_of_omega_le s h hs, mk_compl_of_omega_le t h ht] }

lemma mk_compl_eq_mk_compl_finite_lift {α : Type u} {β : Type v} {s : set α} {t : set β}
  (hα : #α < omega) (h1 : lift.{u (max v w)} (#α) = lift.{v (max u w)} (#β))
  (h2 : lift.{u (max v w)} (#s) = lift.{v (max u w)} (#t)) :
  lift.{u (max v w)} (#(sᶜ : set α)) = lift.{v (max u w)} (#(tᶜ : set β)) :=
begin
  have hα' := hα, have h1' := h1,
  rw [← mk_sum_compl s, ← mk_sum_compl t] at h1,
  rw [← mk_sum_compl s, add_lt_omega_iff] at hα,
  lift #s to ℕ using hα.1 with n hn,
  lift #(sᶜ : set α) to ℕ using hα.2 with m hm,
  have : #(tᶜ : set β) < omega,
  { refine lt_of_le_of_lt (mk_subtype_le _) _,
    rw [← lift_lt, lift_omega, ← h1', ← lift_omega.{u (max v w)}, lift_lt], exact hα' },
  lift #(tᶜ : set β) to ℕ using this with k hk,
  simp [nat_eq_lift_eq_iff] at h2, rw [nat_eq_lift_eq_iff.{v (max u w)}] at h2,
  simp [h2.symm] at h1 ⊢, norm_cast at h1, simp at h1, exact h1
end

lemma mk_compl_eq_mk_compl_finite {α β : Type u} {s : set α} {t : set β}
  (hα : #α < omega) (h1 : #α = #β) (h : #s = #t) : #(sᶜ : set α) = #(tᶜ : set β) :=
by { rw [← lift_inj], apply mk_compl_eq_mk_compl_finite_lift hα; rw [lift_inj]; assumption }

lemma mk_compl_eq_mk_compl_finite_same {α : Type*} {s t : set α} (hα : #α < omega)
  (h : #s = #t) : #(sᶜ : set α) = #(tᶜ : set α) :=
mk_compl_eq_mk_compl_finite hα rfl h

/-! ### Extending an injection to an equiv -/

theorem extend_function {α β : Type*} {s : set α} (f : s ↪ β)
  (h : nonempty ((sᶜ : set α) ≃ ((range f)ᶜ : set β))) :
  ∃ (g : α ≃ β), ∀ x : s, g x = f x :=
begin
  intros, have := h, cases this with g,
  let h : α ≃ β := (set.sum_compl (s : set α)).symm.trans
    ((sum_congr (equiv.set.range f f.2) g).trans
    (set.sum_compl (range f))),
  refine ⟨h, _⟩, rintro ⟨x, hx⟩, simp [set.sum_compl_symm_apply_of_mem, hx]
end

theorem extend_function_finite {α β : Type*} {s : set α} (f : s ↪ β)
  (hs : #α < omega) (h : nonempty (α ≃ β)) : ∃ (g : α ≃ β), ∀ x : s, g x = f x :=
begin
  apply extend_function f,
  have := h, cases this with g,
  rw [← lift_mk_eq] at h,
  rw [←lift_mk_eq, mk_compl_eq_mk_compl_finite_lift hs h],
  rw [mk_range_eq_lift], exact f.2
end

theorem extend_function_of_lt {α β : Type*} {s : set α} (f : s ↪ β) (hs : #s < #α)
  (h : nonempty (α ≃ β)) : ∃ (g : α ≃ β), ∀ x : s, g x = f x :=
begin
  cases (le_or_lt omega (#α)) with hα hα,
  { apply extend_function f, have := h, cases this with g, rw [← lift_mk_eq] at h,
    cases cardinal.eq.mp (mk_compl_of_omega_le s hα hs) with g2,
    cases cardinal.eq.mp (mk_compl_of_omega_le (range f) _ _) with g3,
    { constructor, exact g2.trans (g.trans g3.symm) },
    { rw [← lift_le, ← h], refine le_trans _ (lift_le.mpr hα), simp },
    rwa [← lift_lt, ← h, mk_range_eq_lift, lift_lt], exact f.2 },
  { exact extend_function_finite f hα h }
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

@[simp] lemma bit0_ne_zero (a : cardinal) : ¬bit0 a = 0 ↔ ¬a = 0 :=
by simp [bit0]

@[simp] lemma bit1_ne_zero (a : cardinal) : ¬bit1 a = 0 :=
by simp [bit1]

@[simp] lemma zero_lt_bit0 (a : cardinal) : 0 < bit0 a ↔ 0 < a :=
by { rw ←not_iff_not, simp [bit0], }

@[simp] lemma zero_lt_bit1 (a : cardinal) : 0 < bit1 a :=
lt_of_lt_of_le zero_lt_one (le_add_left _ _)

@[simp] lemma one_le_bit0 (a : cardinal) : 1 ≤ bit0 a ↔ 0 < a :=
⟨λ h, (zero_lt_bit0 a).mp (lt_of_lt_of_le zero_lt_one h),
 λ h, le_trans (one_le_iff_pos.mpr h) (le_add_left a a)⟩

@[simp] lemma one_le_bit1 (a : cardinal) : 1 ≤ bit1 a :=
le_add_left _ _

theorem bit0_eq_self {c : cardinal} (h : omega ≤ c) : bit0 c = c :=
add_eq_self h

@[simp] theorem bit0_lt_omega {c : cardinal} : bit0 c < omega ↔ c < omega :=
by simp [bit0, add_lt_omega_iff]

@[simp] theorem omega_le_bit0 {c : cardinal} : omega ≤ bit0 c ↔ omega ≤ c :=
by { rw ← not_iff_not, simp }

@[simp] theorem bit1_eq_self_iff {c : cardinal} : bit1 c = c ↔ omega ≤ c :=
begin
  by_cases h : omega ≤ c,
  { simp only [bit1, bit0_eq_self h, h, eq_self_iff_true, add_one_of_omega_le] },
  { simp only [h, iff_false],
    apply ne_of_gt,
    rcases lt_omega.1 (not_le.1 h) with ⟨n, rfl⟩,
    norm_cast,
    dsimp [bit1, bit0],
    omega }
end

@[simp] theorem bit1_lt_omega {c : cardinal} : bit1 c < omega ↔ c < omega :=
by simp [bit1, bit0, add_lt_omega_iff, one_lt_omega]

@[simp] theorem omega_le_bit1 {c : cardinal} : omega ≤ bit1 c ↔ omega ≤ c :=
by { rw ← not_iff_not, simp }

@[simp] lemma bit0_le_bit0 {a b : cardinal} : bit0 a ≤ bit0 b ↔ a ≤ b :=
begin
  by_cases ha : omega ≤ a; by_cases hb : omega ≤ b,
  { rw [bit0_eq_self ha, bit0_eq_self hb] },
  { rw bit0_eq_self ha,
    have I1 : ¬ (a ≤ b),
    { assume h, apply hb, exact le_trans ha h },
    have I2 : ¬ (a ≤ bit0 b),
    { assume h,
      have A : bit0 b < omega, by simpa using hb,
      exact lt_irrefl _ (lt_of_lt_of_le (lt_of_lt_of_le A ha) h) },
    simp [I1, I2] },
  { rw [bit0_eq_self hb],
    simp only [not_le] at ha,
    have I1 : a ≤ b := le_of_lt (lt_of_lt_of_le ha hb),
    have I2 : bit0 a ≤ b := le_trans (le_of_lt (bit0_lt_omega.2 ha)) hb,
    simp [I1, I2] },
  { simp at ha hb,
    rcases lt_omega.1 ha with ⟨m, rfl⟩,
    rcases lt_omega.1 hb with ⟨n, rfl⟩,
    norm_cast,
    simp }
end

@[simp] lemma bit0_le_bit1 {a b : cardinal} : bit0 a ≤ bit1 b ↔ a ≤ b :=
begin
  by_cases ha : omega ≤ a; by_cases hb : omega ≤ b,
  { rw [bit0_eq_self ha, bit1_eq_self_iff.2 hb], },
  { rw bit0_eq_self ha,
    have I1 : ¬ (a ≤ b),
    { assume h, apply hb, exact le_trans ha h },
    have I2 : ¬ (a ≤ bit1 b),
    { assume h,
      have A : bit1 b < omega, by simpa using hb,
      exact lt_irrefl _ (lt_of_lt_of_le (lt_of_lt_of_le A ha) h) },
    simp [I1, I2] },
  { rw [bit1_eq_self_iff.2 hb],
    simp only [not_le] at ha,
    have I1 : a ≤ b := le_of_lt (lt_of_lt_of_le ha hb),
    have I2 : bit0 a ≤ b := le_trans (le_of_lt (bit0_lt_omega.2 ha)) hb,
    simp [I1, I2] },
  { simp at ha hb,
    rcases lt_omega.1 ha with ⟨m, rfl⟩,
    rcases lt_omega.1 hb with ⟨n, rfl⟩,
    norm_cast,
    simp }
end

@[simp] lemma bit1_le_bit1 {a b : cardinal} : bit1 a ≤ bit1 b ↔ a ≤ b :=
begin
  split,
  { assume h,
    apply bit0_le_bit1.1 (le_trans ((bit0 a).le_add_right 1) h) },
  { assume h,
    calc a + a + 1 ≤ a + b + 1 : add_le_add_right 1 (add_le_add_left a h)
           ... ≤ b + b + 1 : add_le_add_right 1 (add_le_add_right b h) }
end

@[simp] lemma bit1_le_bit0 {a b : cardinal} : bit1 a ≤ bit0 b ↔ (a < b ∨ (a ≤ b ∧ omega ≤ a)) :=
begin
  by_cases ha : omega ≤ a; by_cases hb : omega ≤ b,
  { simp only [bit1_eq_self_iff.mpr ha, bit0_eq_self hb, ha, and_true],
    refine ⟨λ h, or.inr h, λ h, _⟩,
    cases h,
    { exact le_of_lt h },
    { exact h } },
  { rw bit1_eq_self_iff.2 ha,
    have I1 : ¬ (a ≤ b),
    { assume h, apply hb, exact le_trans ha h },
    have I2 : ¬ (a ≤ bit0 b),
    { assume h,
      have A : bit0 b < omega, by simpa using hb,
      exact lt_irrefl _ (lt_of_lt_of_le (lt_of_lt_of_le A ha) h) },
    simp [I1, I2, le_of_not_ge I1] },
  { rw [bit0_eq_self hb],
    simp only [not_le] at ha,
    have I1 : a < b := lt_of_lt_of_le ha hb,
    have I2 : bit1 a ≤ b := le_trans (le_of_lt (bit1_lt_omega.2 ha)) hb,
    simp [I1, I2] },
  { simp at ha hb,
    rcases lt_omega.1 ha with ⟨m, rfl⟩,
    rcases lt_omega.1 hb with ⟨n, rfl⟩,
    norm_cast,
    simp [not_le.mpr ha], }
end

@[simp] lemma bit0_lt_bit0 {a b : cardinal} : bit0 a < bit0 b ↔ a < b :=
begin
  by_cases ha : omega ≤ a; by_cases hb : omega ≤ b,
  { rw [bit0_eq_self ha, bit0_eq_self hb] },
  { rw bit0_eq_self ha,
    have I1 : ¬ (a < b),
    { assume h, apply hb, exact le_trans ha (le_of_lt h) },
    have I2 : ¬ (a < bit0 b),
    { assume h,
      have A : bit0 b < omega, by simpa using hb,
      exact lt_irrefl _ (lt_trans (lt_of_lt_of_le A ha) h) },
    simp [I1, I2] },
  { rw [bit0_eq_self hb],
    simp only [not_le] at ha,
    have I1 : a < b := lt_of_lt_of_le ha hb,
    have I2 : bit0 a < b := lt_of_lt_of_le (bit0_lt_omega.2 ha) hb,
    simp [I1, I2] },
  { simp at ha hb,
    rcases lt_omega.1 ha with ⟨m, rfl⟩,
    rcases lt_omega.1 hb with ⟨n, rfl⟩,
    norm_cast,
    simp }
end

@[simp] lemma bit1_lt_bit0 {a b : cardinal} : bit1 a < bit0 b ↔ a < b :=
begin
  by_cases ha : omega ≤ a; by_cases hb : omega ≤ b,
  { rw [bit1_eq_self_iff.2 ha, bit0_eq_self hb], },
  { rw bit1_eq_self_iff.2 ha,
    have I1 : ¬ (a < b),
    { assume h, apply hb, exact le_of_lt (lt_of_le_of_lt ha h) },
    have I2 : ¬ (a < bit0 b),
    { assume h,
      have A : bit0 b < omega, by simpa using hb,
      exact lt_irrefl _ (lt_trans (lt_of_lt_of_le A ha) h) },
    simp [I1, I2] },
  { rw [bit0_eq_self hb],
    simp only [not_le] at ha,
    have I1 : a < b := (lt_of_lt_of_le ha hb),
    have I2 : bit1 a < b := lt_of_lt_of_le (bit1_lt_omega.2 ha) hb,
    simp [I1, I2] },
  { simp at ha hb,
    rcases lt_omega.1 ha with ⟨m, rfl⟩,
    rcases lt_omega.1 hb with ⟨n, rfl⟩,
    norm_cast,
    simp }
end

@[simp] lemma bit1_lt_bit1 {a b : cardinal} : bit1 a < bit1 b ↔ a < b :=
begin
  by_cases ha : omega ≤ a; by_cases hb : omega ≤ b,
  { rw [bit1_eq_self_iff.2 ha, bit1_eq_self_iff.2 hb], },
  { rw bit1_eq_self_iff.2 ha,
    have I1 : ¬ (a < b),
    { assume h, apply hb, exact le_of_lt (lt_of_le_of_lt ha h) },
    have I2 : ¬ (a < bit1 b),
    { assume h,
      have A : bit1 b < omega, by simpa using hb,
      exact lt_irrefl _ (lt_trans (lt_of_lt_of_le A ha) h) },
    simp [I1, I2] },
  { rw [bit1_eq_self_iff.2 hb],
    simp only [not_le] at ha,
    have I1 : a < b := (lt_of_lt_of_le ha hb),
    have I2 : bit1 a < b := lt_of_lt_of_le (bit1_lt_omega.2 ha) hb,
    simp [I1, I2] },
  { simp at ha hb,
    rcases lt_omega.1 ha with ⟨m, rfl⟩,
    rcases lt_omega.1 hb with ⟨n, rfl⟩,
    norm_cast,
    simp }
end

@[simp] lemma bit0_lt_bit1 {a b : cardinal} : bit0 a < bit1 b ↔ (a < b ∨ (a ≤ b ∧ a < omega)) :=
begin
  by_cases ha : omega ≤ a; by_cases hb : omega ≤ b,
  { simp [bit0_eq_self ha, bit1_eq_self_iff.2 hb, not_lt.mpr ha] },
  { rw bit0_eq_self ha,
    have I1 : ¬ (a < b),
    { assume h, apply hb, exact le_of_lt (lt_of_le_of_lt ha h) },
    have I2 : ¬ (a < bit1 b),
    { assume h,
      have A : bit1 b < omega, by simpa using hb,
      exact lt_irrefl _ (lt_trans (lt_of_lt_of_le A ha) h) },
    simp [I1, I2, not_lt.mpr ha] },
  { rw [bit1_eq_self_iff.2 hb],
    simp only [not_le] at ha,
    have I1 : a < b := (lt_of_lt_of_le ha hb),
    have I2 : bit0 a < b := lt_of_lt_of_le (bit0_lt_omega.2 ha) hb,
    simp [I1, I2] },
  { simp at ha hb,
    rcases lt_omega.1 ha with ⟨m, rfl⟩,
    rcases lt_omega.1 hb with ⟨n, rfl⟩,
    norm_cast,
    simp only [ha, and_true, nat.bit0_lt_bit1_iff],
    refine ⟨λ h, or.inr h, λ h, _⟩,
    cases h,
    { exact le_of_lt h },
    { exact h } }
end

lemma one_lt_two : (1 : cardinal) < 2 :=
-- This strategy works generally to prove inequalities between numerals in `cardinality`.
by { norm_cast, norm_num }

@[simp] lemma one_lt_bit0 {a : cardinal} : 1 < bit0 a ↔ 0 < a :=
by simp [← bit1_zero]

@[simp] lemma one_lt_bit1 (a : cardinal) : 1 < bit1 a ↔ 0 < a :=
by simp [← bit1_zero]

@[simp] lemma one_le_one : (1 : cardinal) ≤ 1 :=
le_refl _

end bit

end cardinal
