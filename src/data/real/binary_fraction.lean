/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import set_theory.continuum
import data.stream.basic
import data.setoid.basic
import order.pilex
import order.conditionally_complete_lattice

/-- A binary fraction is a sequence of zeros and ones. We use a map `ℕ → bool` to represent it, with
`ff` encoding zero and `tt` encoding one. -/
def binary_fraction : Type := ℕ → bool

variables {x y z : binary_fraction}

open_locale cardinal
open cardinal function set bool

namespace binary_fraction

instance : inhabited binary_fraction := pi.inhabited _

noncomputable instance : linear_order binary_fraction := pilex.linear_order nat.lt_wf

/-- Two binary fractions `x` and `y` are related by `binary_fraction.tail_rel` if they have the form
`x = x₀...xₙ ff tt tt tt tt ...` and `y = x₀...xₙ tt ff ff ff ff ...`. Two fractions related by
`tail_rel` define the same real number. -/
def tail_rel (x y : binary_fraction) :=
∃ k, (∀ i < k, x i = y i) ∧ x k = ff ∧ y k = tt ∧ (∀ i > k, x i = tt) ∧ (∀ i > k, y i = ff)

namespace tail_rel
protected lemma lt (h : tail_rel x y) : x < y :=
h.imp $ λ K hK, ⟨hK.1, bool.lt_iff.2 ⟨hK.2.1, hK.2.2.1⟩⟩

lemma comp_bnot_symm (h : tail_rel x y) : tail_rel (bnot ∘ y) (bnot ∘ x) :=
begin
  rcases h with ⟨K, hlt, hxk, hyk, hgtx, hgty⟩,
  refine ⟨K, λ i hi, (congr_arg bnot (hlt i hi)).symm, by simp [hyk], by simp [hxk],
    λ i hi, by simp [hgty i hi], λ i hi, by simp [hgtx i hi]⟩
end

/-- The same fraction can not have a tail of `ff`s and a tail of `tt`s at the same time. -/
lemma strong_asymm (h : tail_rel x y) (z : binary_fraction) : ¬ tail_rel y z :=
begin
  rcases h with ⟨k, -, -, -, -, hk⟩, rintro ⟨l, -, -, -, hl, -⟩,
  specialize hk (max k l + 1) ((le_max_left k l).trans_lt $ nat.lt_succ_self _),
  specialize hl (max k l + 1) ((le_max_right k l).trans_lt $ nat.lt_succ_self _),
  exact ff_ne_tt (hk.symm.trans hl)
end

lemma right_le_of_left_lt (h₁ : tail_rel x y) (h₂ : x < z) : y ≤ z :=
begin
  rcases h₁ with ⟨K, hlt, hxk, hyk, hxgt, hygt⟩,
  rcases h₂ with ⟨N, hltN, hN⟩,
  rcases lt_trichotomy K N with (hKN|rfl|hNK),
  { rw hxgt N hKN at hN, exact (le_tt.not_lt hN).elim },
  { refine pilex.le_of_forall_le nat.lt_wf (λ i, _),
    rcases lt_trichotomy i K with (hiK|rfl|hKi),
    exacts [hlt i hiK ▸ (hltN _ hiK).le, (bool.lt_iff.1 hN).2.symm ▸ le_tt,
      (hygt _ hKi).symm ▸ ff_le] },
  { exact le_of_lt ⟨N, λ j hj, hlt j (hj.trans hNK) ▸ hltN _ hj, hlt N hNK ▸ hN⟩ }
end

lemma le_left_of_lt_right (h₁ : tail_rel y z) (h₂ : x < z) : x ≤ y :=
le_of_not_lt $ λ h, (h₁.right_le_of_left_lt h).not_lt h₂

protected lemma left_unique (h₁ : tail_rel x z) (h₂ : tail_rel y z) : x = y :=
le_antisymm (h₂.le_left_of_lt_right h₁.lt) (h₁.le_left_of_lt_right h₂.lt)

protected lemma right_unique (h₁ : tail_rel x y) (h₂ : tail_rel x z) : y = z :=
le_antisymm (h₁.right_le_of_left_lt h₂.lt) (h₂.right_le_of_left_lt h₁.lt)

end tail_rel

instance : setoid binary_fraction :=
{ r := λ x y, x = y ∨ tail_rel x y ∨ tail_rel y x,
  iseqv :=
    begin
      refine ⟨λ x, or.inl rfl, λ x y, or.imp eq.symm or.symm, _⟩,
      rintro x y z (rfl|hxy|hyx),
      { exact id },
      { rintro (rfl|hyz|hzy),
        exacts [or.inr (or.inl hxy), (hxy.strong_asymm _ hyz).elim, or.inl (hxy.left_unique hzy)] },
      { rintro (rfl|hyz|hzy),
        exacts [or.inr (or.inr hyx), or.inl $ hyx.right_unique hyz, (hzy.strong_asymm _ hyx).elim] }
    end }

lemma tail_rel.equiv (h : tail_rel x y) : x ≈ y := or.inr (or.inl h)
lemma tail_rel.equiv' (h : tail_rel x y) : y ≈ x := or.inr (or.inr h)

lemma lt_of_lt_of_equiv_not_equiv {a a' b b' : binary_fraction} (hlt : a < b) (ha : a ≈ a')
  (hb : b ≈ b') (hne : ¬ a ≈ b) :
  a' < b' :=
begin
  rcases ⟨ha, hb⟩ with ⟨(rfl|ha|ha), (rfl|hb|hb)⟩,
  { exact hlt },
  { exact hlt.trans hb.lt },
  { exact (hb.le_left_of_lt_right hlt).lt_of_ne (λ hab', hne $ hab'.symm ▸ hb.equiv) },
  { exact (ha.right_le_of_left_lt hlt).lt_of_ne (λ ha'b, hne $ ha'b ▸ ha.equiv) },
  { exact (ha.right_le_of_left_lt hlt).trans_lt hb.lt },
  { refine (ha.right_le_of_left_lt ((hb.le_left_of_lt_right hlt).lt_of_ne $ _)).lt_of_ne _,
    { rintro rfl, obtain rfl : a' = b := ha.right_unique hb, exact hne hb.equiv },
    { rintro rfl, exact ha.strong_asymm _ hb } },
  { exact ha.lt.trans hlt },
  { exact ha.lt.trans (hlt.trans hb.lt) },
  { exact ha.lt.trans_le (hb.le_left_of_lt_right hlt) }
end

lemma not_tail_rel_interleave : ¬tail_rel (x ⋈ z) (y ⋈ z) :=
begin
  rintro ⟨K, -, -, -, hK₁, hK₂⟩,
  have : K < 2 * K + 1, by simp [two_mul, add_assoc],
  refine ff_ne_tt _,
  calc ff = (y ⋈ z).nth (2 * K + 1) : (hK₂ _ this).symm
  ... = z K : stream.nth_interleave_right _ _ _
  ... = (x ⋈ z).nth (2 * K + 1) : (stream.nth_interleave_right _ _ _).symm
  ... = tt : hK₁ _ this
end

lemma eq_of_eqv_interleave (h : binary_fraction.setoid.rel (x ⋈ z) (y ⋈ z)) : x = y :=
begin
  rcases h with (eq|h|h),
  { rw [← stream.even_interleave x z, eq, stream.even_interleave] },
  exacts [(not_tail_rel_interleave h).elim, (not_tail_rel_interleave h).elim] 
end

noncomputable instance : linear_order (quotient binary_fraction.setoid) :=
linear_order.lift quotient.out $ (λ _ _, quotient.out_inj.1)

lemma mkq_lt_mkq : ⟦x⟧ < ⟦y⟧ ↔ x < y ∧ ¬ x ≈ y :=
begin
  refine ⟨λ hlt, _, λ hlt, _⟩,
  { refine ⟨lt_of_lt_of_equiv_not_equiv hlt (quotient.mk_out _) (quotient.mk_out _) (λ h, _), _⟩,
    exacts [hlt.ne (quotient.out_equiv_out.1 h), λ h, hlt.ne (quotient.sound h)] },
  { exact lt_of_lt_of_equiv_not_equiv hlt.1 (setoid.symm $ quotient.mk_out _)
      (setoid.symm $ quotient.mk_out _) hlt.2 }
end

lemma mkq_le_mkq : ⟦x⟧ ≤ ⟦y⟧ ↔ x ≤ y ∨ x ≈ y :=
begin
  simp only [← not_lt, mkq_lt_mkq, not_and_distrib, not_not],
  exact or_congr iff.rfl ⟨setoid.symm, setoid.symm⟩
end

variables {α : Type*}

section preorder

variable [preorder α]

variable (choice : Π I : nontrivial_interval α, I.Ioo)

/-- Given a choice function `choice : Π I : nontrivial_interval α, I.Ioo`, a boolean value `b`, and
a nontrivial interval `I`, returns either `[I.left, choice I]` (if `b = ff`), or
`[choice I, I.right]` (if `b = tt`). -/
def next_interval (b : bool) (I : nontrivial_interval α) : nontrivial_interval α :=
cond b ⟨choice I, I.right, (choice I).2.2⟩ ⟨I.left, choice I, (choice I).2.1⟩

lemma next_interval_lt (I : nontrivial_interval α) :
  ∀ b, next_interval choice b I < I
| ff := ⟨⟨le_rfl, (choice I).2.2.le⟩, λ h, h.2.not_lt (choice I).2.2⟩
| tt := ⟨⟨(choice I).2.1.le, le_rfl⟩, λ h, h.1.not_lt (choice I).2.1⟩

/-- Given a choice function `choice : Π I : nontrivial_interval α, I.Ioo`, a binary fraction `x`
and an initial interval `I`, returns the strictly antitone sequence of nontrivial intervals given by
`nth_interval choice x I 0 = I` and
`nth_interval choice x I (n + 1) = next_interval choice (x n) (nth_interval choice x I n)`. -/
def nth_interval (x : binary_fraction) (I : nontrivial_interval α) : ℕ → nontrivial_interval α
| 0 := I
| (n + 1) := next_interval choice (x n) (nth_interval n)

@[simp] lemma nth_interval_zero (x : binary_fraction) (I : nontrivial_interval α) :
  nth_interval choice x I 0 = I := rfl

lemma nth_interval_succ (x : binary_fraction) (I : nontrivial_interval α) (n : ℕ) :
  nth_interval choice x I (n + 1) = next_interval choice (x n) (nth_interval choice x I n) :=
rfl

lemma nth_interval_succ' (x : binary_fraction) (I : nontrivial_interval α) (n : ℕ) :
  nth_interval choice x I (n + 1) =
    nth_interval choice (stream.tail x) (next_interval choice (x 0) I) n :=
begin
  induction n with n ihn generalizing I, { refl },
  rw [nth_interval_succ, nat.succ_eq_add_one, ihn, nth_interval_succ],
  refl
end

lemma strict_anti_nth_interval (x : binary_fraction) (I : nontrivial_interval α) :
  strict_anti (x.nth_interval choice I) :=
strict_anti_nat_of_succ_lt $ λ n, next_interval_lt _ _ _

lemma antitone_nth_interval (x : binary_fraction) (I : nontrivial_interval α) :
  antitone (x.nth_interval choice I) :=
(strict_anti_nth_interval choice x I).antitone

lemma nth_interval_congr (n : ℕ) (h : ∀ k < n, x k = y k) (I : nontrivial_interval α) :
  x.nth_interval choice I n = y.nth_interval choice I n :=
begin
  induction n with n ihn, { refl },
  rw [nth_interval, nth_interval, ihn, h n n.lt_succ_self],
  exact λ k hk, h k (hk.trans n.lt_succ_self)
end

end preorder

variables [conditionally_complete_lattice α] (choice : Π I : nontrivial_interval α, I.Ioo)

/-- “Decode” an element of a conditionally complete lattice `α` encoded by `x : binary_fraction`
given a choice function and an initial interval. In the case of real numbers,
`I = ⟨0, 1, zero_lt_one⟩`, and `(choice J : ℝ) = (J.left + J.right) / 2`, this corresponds to the
classical binary representation of a real number. -/
def decode (I : nontrivial_interval α) (x : binary_fraction) : α :=
⨆ n, (x.nth_interval choice I n).left

lemma decode_mem_Inter_Icc (I : nontrivial_interval α) (x : binary_fraction) :
  x.decode choice I ∈ ⋂ n, (x.nth_interval choice I n).Icc :=
csupr_mem_Inter_Icc_of_antitone_nontrivial_interval (x.antitone_nth_interval choice I)

lemma decode_mem_Icc (I : nontrivial_interval α) (x : binary_fraction) (n : ℕ) :
  x.decode choice I ∈ (x.nth_interval choice I n).Icc :=
by convert mem_Inter.1 (x.decode_mem_Inter_Icc choice I) n

lemma decode_lt_of_lt_not_equiv (I : nontrivial_interval α) (h₁ : x < y) (h₂ : ¬ x ≈ y) :
  x.decode choice I < y.decode choice I :=
begin
  rcases h₁ with ⟨N, lt_N, xy_N⟩,
  rw bool.lt_iff at xy_N,
  rcases em (∃ n > N, x n = ff) with ⟨n, hNn, hxn⟩|Hx,
  { calc x.decode choice I ≤ (x.nth_interval choice I (n + 1)).right :
      (x.decode_mem_Icc choice I _).2
    ... < (x.nth_interval choice I n).right :
      by { rw [nth_interval, hxn], exact (choice _).2.2 }
    ... ≤ (x.nth_interval choice I (N + 1)).right :
      nontrivial_interval.monotone_right $ antitone_nth_interval _ _ _ hNn
    ... = (y.nth_interval choice I (N + 1)).left :
      by { rw [nth_interval, nth_interval, xy_N.1, xy_N.2, nth_interval_congr _ _ lt_N], refl }
    ... ≤ y.decode choice I : (y.decode_mem_Icc choice I _).1 },
  { rcases em (∃ n > N, y n = tt) with ⟨n, hNn, hyn⟩|Hy,
    { calc x.decode choice I ≤ (x.nth_interval choice I (N + 1)).right :
        (x.decode_mem_Icc choice I _).2
      ... = (y.nth_interval choice I (N + 1)).left :
        by { rw [nth_interval, nth_interval, xy_N.1, xy_N.2, nth_interval_congr _ _ lt_N], refl }
      ... ≤ (y.nth_interval choice I n).left :
        nontrivial_interval.antitone_left $ antitone_nth_interval _ _ _ hNn
      ... < (y.nth_interval choice I (n + 1)).left :
        by { rw [nth_interval, hyn], exact (choice _).2.1 }
      ... ≤ y.decode choice I : (y.decode_mem_Icc choice I _).1 },
    suffices : tail_rel x y, from (h₂ this.equiv).elim,
    push_neg at Hx Hy,
    exact ⟨N, lt_N, xy_N.1, xy_N.2, λ i hi, eq_tt_of_ne_ff (Hx i hi),
      λ i hi, eq_ff_of_ne_tt (Hy i hi)⟩ }
end

lemma strict_mono_decode_out (I : nontrivial_interval α) :
  strict_mono (λ x : quotient binary_fraction.setoid, x.out.decode choice I) :=
λ x y h, decode_lt_of_lt_not_equiv _ _ h $ λ H, h.ne $ quotient.out_equiv_out.1 H

instance : has_card_continuum binary_fraction := pi.has_card_continuum _ _

instance : has_card_continuum (quotient binary_fraction.setoid) :=
⟨begin
  rw ← mk_eq_continuum binary_fraction,
  refine mk_quotient_le.antisymm _,
  set f : binary_fraction → quotient binary_fraction.setoid :=
    λ x, quotient.mk (x ⋈ (λ _, ff)),
  have inj : injective f := λ x y h, eq_of_eqv_interleave (quotient.exact h),
  exact mk_le_of_injective inj
end⟩

end binary_fraction

namespace cardinal

open binary_fraction

universe u

variables {α : Type u} [conditionally_complete_lattice α] [densely_ordered α]

section

variables {a b : α}

lemma continuum_le_mk_Icc (h : a < b) : 𝔠 ≤ #(Icc a b) :=
begin
  set c : Π I : nontrivial_interval α, I.Ioo :=
    λ I, classical.indefinite_description _ I.nonempty_Ioo,
  set f : quotient binary_fraction.setoid → Icc a b :=
    λ x, ⟨x.out.decode c ⟨a, b, h⟩, x.out.decode_mem_Icc _ _ 0⟩,
  have hf : strict_mono f := strict_mono_decode_out c _,
  simpa using lift_mk_le'.2 ⟨⟨f, hf.injective⟩⟩,
end

lemma continuum_le_mk_Ioo (h : a < b) : 𝔠 ≤ #(Ioo a b) :=
begin
  rcases exists_between h with ⟨a₁, ha, hlt⟩, rcases exists_between hlt with ⟨b₁, hab, hb⟩,
  calc 𝔠 ≤ #(Icc a₁ b₁) : continuum_le_mk_Icc hab
  ... ≤ #(Ioo a b) : mk_le_mk_of_subset (Icc_subset_Ioo ha hb)
end

lemma continuum_le_mk_Ico (h : a < b) : 𝔠 ≤ #(Ico a b) :=
(continuum_le_mk_Ioo h).trans (mk_le_mk_of_subset Ioo_subset_Ico_self)

lemma continuum_le_mk_Ioc (h : a < b) : 𝔠 ≤ #(Ioc a b) :=
(continuum_le_mk_Ioo h).trans (mk_le_mk_of_subset Ioo_subset_Ioc_self)

lemma continuum_le_mk_Ioi' (h : (Ioi a).nonempty) : 𝔠 ≤ #(Ioi a) :=
exists.elim h $ λ b hb, (continuum_le_mk_Ioo hb).trans $ mk_le_mk_of_subset Ioo_subset_Ioi_self

lemma continuum_le_mk_Ioi [no_top_order α] (a : α) : 𝔠 ≤ #(Ioi a) :=
continuum_le_mk_Ioi' (no_top a)

lemma continuum_le_mk_Ici' (h : (Ioi a).nonempty) : 𝔠 ≤ #(Ici a) :=
(continuum_le_mk_Ioi' h).trans $ mk_le_mk_of_subset Ioi_subset_Ici_self

lemma continuum_le_mk_Ici [no_top_order α] (a : α) : 𝔠 ≤ #(Ici a) :=
continuum_le_mk_Ici' (no_top a)

lemma continuum_le_mk_Iio' (h : (Iio a).nonempty) : 𝔠 ≤ #(Iio a) :=
@continuum_le_mk_Ioi' (order_dual α) _ _ a h

lemma continuum_le_mk_Iio [no_bot_order α] (a : α) : 𝔠 ≤ #(Iio a) :=
@continuum_le_mk_Ioi (order_dual α) _ _ _ a

lemma continuum_le_mk_Iic' (h : (Iio a).nonempty) : 𝔠 ≤ #(Iic a) :=
@continuum_le_mk_Ici' (order_dual α) _ _ a h

lemma continuum_le_mk_Iic [no_bot_order α] (a : α) : 𝔠 ≤ #(Iic a) :=
@continuum_le_mk_Ici (order_dual α) _ _ _ a

variable (α)

lemma continuum_le_mk [nontrivial α] : 𝔠 ≤ #α :=
let ⟨a, b, h⟩ := exists_lt_of_inf α in (continuum_le_mk_Icc h).trans $ mk_set_le _

end

variables [has_card_continuum α] {a b : α}

@[simp] lemma mk_Icc_eq_continuum (h : a < b) : #(Icc a b) = 𝔠 :=
le_antisymm ((mk_set_le _).trans_eq $ mk_eq_continuum α) (continuum_le_mk_Icc h)

@[simp] lemma mk_Ico_eq_continuum (h : a < b) : #(Ico a b) = 𝔠 :=
le_antisymm ((mk_set_le _).trans_eq $ mk_eq_continuum α) (continuum_le_mk_Ico h)

@[simp] lemma mk_Ioc_eq_continuum (h : a < b) : #(Ioc a b) = 𝔠 :=
le_antisymm ((mk_set_le _).trans_eq $ mk_eq_continuum α) (continuum_le_mk_Ioc h)

@[simp] lemma mk_Ioo_eq_continuum (h : a < b) : #(Ioo a b) = 𝔠 :=
le_antisymm ((mk_set_le _).trans_eq $ mk_eq_continuum α) (continuum_le_mk_Ioo h)

lemma mk_Ici_eq_continuum' (h : (Ioi a).nonempty) : #(Ici a) = 𝔠 :=
le_antisymm ((mk_set_le _).trans_eq $ mk_eq_continuum α) (continuum_le_mk_Ici' h)

@[simp] lemma mk_Ici_eq_continuum [no_top_order α] (a : α) : #(Ici a) = 𝔠 :=
mk_Ici_eq_continuum' (no_top a)

lemma mk_Ioi_eq_continuum' (h : (Ioi a).nonempty) : #(Ioi a) = 𝔠 :=
le_antisymm ((mk_set_le _).trans_eq $ mk_eq_continuum α) (continuum_le_mk_Ioi' h)

@[simp] lemma mk_Ioi_eq_continuum [no_top_order α] (a : α) : #(Ioi a) = 𝔠 :=
mk_Ioi_eq_continuum' (no_top a)

lemma mk_Iic_eq_continuum' (h : (Iio a).nonempty) : #(Iic a) = 𝔠 :=
le_antisymm ((mk_set_le _).trans_eq $ mk_eq_continuum α) (continuum_le_mk_Iic' h)

@[simp] lemma mk_Iic_eq_continuum [no_bot_order α] (a : α) : #(Iic a) = 𝔠 :=
mk_Iic_eq_continuum' (no_bot a)

lemma mk_Iio_eq_continuum' (h : (Iio a).nonempty) : #(Iio a) = 𝔠 :=
le_antisymm ((mk_set_le _).trans_eq $ mk_eq_continuum α) (continuum_le_mk_Iio' h)

@[simp] lemma mk_Iio_eq_continuum [no_bot_order α] (a : α) : #(Iio a) = 𝔠 :=
mk_Iio_eq_continuum' (no_bot a)

end cardinal
