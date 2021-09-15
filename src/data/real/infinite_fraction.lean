/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import set_theory.cardinal_ordinal
import data.stream
import data.setoid.basic
import tactic.wlog
import order.pilex
import order.conditionally_complete_lattice

def binary_fraction : Type := ℕ → bool

variables {x y z : binary_fraction}

open_locale cardinal
open cardinal function set bool

namespace binary_fraction

noncomputable instance : linear_order binary_fraction := pilex.linear_order nat.lt_wf

def tail_rel (x y : binary_fraction) :=
∃ k, (∀ i < k, x i = y i) ∧ x k = ff ∧ y k = tt ∧ (∀ i > k, x i = tt) ∧ (∀ i > k, y i = ff)

lemma tail_rel.lt (h : tail_rel x y) : x < y :=
h.imp $ λ K hK, ⟨hK.1, bool.lt_iff.2 ⟨hK.2.1, hK.2.2.1⟩⟩

lemma tail_rel.comp_bnot_symm (h : tail_rel x y) : tail_rel (bnot ∘ y) (bnot ∘ x) :=
begin
  rcases h with ⟨K, hlt, hxk, hyk, hgtx, hgty⟩,
  refine ⟨K, λ i hi, (congr_arg bnot (hlt i hi)).symm, by simp [hyk], by simp [hxk],
    λ i hi, by simp [hgty i hi], λ i hi, by simp [hgtx i hi]⟩
end

/-- The same fraction can not have a tail of `ff`s and a tail of `tt`s at the same time. -/
lemma tail_rel.strong_asymm (h : tail_rel x y) (z : binary_fraction) :
  ¬ tail_rel y z :=
begin
  rcases h with ⟨k, -, -, -, -, hk⟩, rintro ⟨l, -, -, -, hl, -⟩,
  specialize hk (max k l + 1) ((le_max_left k l).trans_lt $ nat.lt_succ_self _),
  specialize hl (max k l + 1) ((le_max_right k l).trans_lt $ nat.lt_succ_self _),
  exact ff_ne_tt (hk.symm.trans hl)
end

lemma tail_rel.right_le_of_left_lt (h₁ : tail_rel x y) (h₂ : x < z) : y ≤ z :=
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

lemma tail_rel.le_left_of_lt_right (h₁ : tail_rel y z) (h₂ : x < z) : x ≤ y :=
le_of_not_lt $ λ h, (h₁.right_le_of_left_lt h).not_lt h₂

lemma tail_rel.left_unique (h₁ : tail_rel x z) (h₂ : tail_rel y z) : x = y :=
le_antisymm (h₂.le_left_of_lt_right h₁.lt) (h₁.le_left_of_lt_right h₂.lt)

lemma tail_rel.right_unique (h₁ : tail_rel x y) (h₂ : tail_rel x z) : y = z :=
le_antisymm (h₁.right_le_of_left_lt h₂.lt) (h₂.right_le_of_left_lt h₁.lt)

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

structure nonempty_interval (α : Type*) [preorder α] :=
(left right : α) (hlt : left < right)

def nonempty_interval.Icc (I : nonempty_interval α) : set α := Icc I.left I.right

variable (choice : Π I : nonempty_interval α, (Ioo I.left I.right))
def next_interval (b : bool) (I : nonempty_interval α) : nonempty_interval α :=
cond b ⟨choice I, I.right, (choice I).2.2⟩ ⟨I.left, choice I, (choice I).2.1⟩

lemma next_interval_subset (b : bool) (I : nonempty_interval α) :
  (next_interval choice b I).Icc ⊆ I.Icc :=
begin
  cases b,
  exacts [Icc_subset_Icc_right (choice I).2.2.le, Icc_subset_Icc_left (choice I).2.1.le]
end

def nth_interval (x : binary_fraction) (I : nonempty_interval α) : ℕ → nonempty_interval α
| 0 := I
| (n + 1) := next_interval choice (x n) (nth_interval n)

lemma nth_interval_succ_subset (x : binary_fraction) (I : nonempty_interval α) (n : ℕ) :
    (x.nth_interval choice I (n + 1)).Icc ⊆ (x.nth_interval choice I n).Icc :=
next_interval_subset _ _ _

lemma nth_interval_antimono (x : binary_fraction) (I : nonempty_interval α) :
  ∀ ⦃m n⦄, m ≤ n → (x.nth_interval choice I n).Icc ⊆ (x.nth_interval choice I m).Icc :=
begin
  refine @monotone_nat_of_le_succ (order_dual (set α)) _ _ (λ n, _),
  apply nth_interval_succ_subset
end

lemma nth_interval_congr (n : ℕ) (h : ∀ k < n, x k = y k) (I : nonempty_interval α) :
  x.nth_interval choice I n = y.nth_interval choice I n :=
begin
  induction n with n ihn, { refl },
  rw [nth_interval, nth_interval, ihn, h n n.lt_succ_self],
  exact λ k hk, h k (hk.trans n.lt_succ_self)
end

end preorder

variables [conditionally_complete_lattice α]
  (choice : Π I : nonempty_interval α, (Ioo I.left I.right))

def decode (I : nonempty_interval α) (x : binary_fraction) : α :=
⨆ n, (x.nth_interval choice I n).left

lemma decode_mem_Inter_Icc (I : nonempty_interval α) (x : binary_fraction) :
  x.decode choice I ∈ ⋂ n, (x.nth_interval choice I n).Icc :=
csupr_mem_Inter_Icc_of_mono_decr_Icc_nat (x.nth_interval_succ_subset choice I)
  (λ n, (x.nth_interval choice I n).hlt.le)

lemma decode_mem_Icc (I : nonempty_interval α) (x : binary_fraction) (n : ℕ) :
  x.decode choice I ∈ (x.nth_interval choice I n).Icc :=
by convert mem_Inter.1 (x.decode_mem_Inter_Icc choice I) n

lemma decode_lt_of_lt_not_equiv (I : nonempty_interval α) (h₁ : x < y) (h₂ : ¬ x ≈ y) :
  x.decode choice I < y.decode choice I :=
begin
  rcases h₁ with ⟨N, lt_N, xy_N⟩,
  rw bool.lt_iff at xy_N,
  by_cases Hx : ∃ n > N, x n = ff,
  { rcases Hx with ⟨n, hNn, hxn⟩,
    calc x.decode choice I ≤ (x.nth_interval choice I (n + 1)).right :
      (x.decode_mem_Icc choice I _).2
    ... < (x.nth_interval choice I n).right :
      by { rw [nth_interval, hxn], exact (choice _).2.2 }
    ... ≤ (x.nth_interval choice I (N + 1)).right :
      (x.nth_interval_antimono _ _ hNn.lt $ right_mem_Icc.2 (nth_interval _ _ _ _).hlt.le).2
    ... = (y.nth_interval choice I (N + 1)).left :
      by { rw [nth_interval, nth_interval, xy_N.1, xy_N.2, nth_interval_congr _ _ lt_N], refl }
    ... ≤ y.decode choice I : (y.decode_mem_Icc choice I _).1 },
  { by_cases Hy : ∃ n > N, y n = tt,
    { rcases Hy with ⟨n, hNn, hyn⟩, from
    calc x.decode choice I ≤ (x.nth_interval choice I (N + 1)).right :
      (x.decode_mem_Icc choice I _).2
    ... = (y.nth_interval choice I (N + 1)).left :
      by { rw [nth_interval, nth_interval, xy_N.1, xy_N.2, nth_interval_congr _ _ lt_N], refl }
    ... ≤ (y.nth_interval choice I n).left :
      (y.nth_interval_antimono _ _ hNn.lt $ left_mem_Icc.2 (nth_interval _ _ _ _).hlt.le).1
    ... < (y.nth_interval choice I (n + 1)).left :
      by { rw [nth_interval, hyn], exact (choice _).2.1 }
    ... ≤ y.decode choice I : (y.decode_mem_Icc choice I _).1 },
    suffices : tail_rel x y, from (h₂ this.equiv).elim,
    push_neg at Hx Hy,
    exact ⟨N, lt_N, xy_N.1, xy_N.2, λ i hi, eq_tt_of_ne_ff (Hx i hi),
      λ i hi, eq_ff_of_ne_tt (Hy i hi)⟩ }
end

lemma strict_mono_decode_out (I : nonempty_interval α) :
  strict_mono (λ x : quotient binary_fraction.setoid, x.out.decode choice I) :=
λ x y h, decode_lt_of_lt_not_equiv _ _ h $ λ H, h.ne $ quotient.out_equiv_out.1 H

end binary_fraction

namespace cardinal

open binary_fraction

@[simp] lemma mk_binary_fraction : #binary_fraction = 2 ^ omega.{0} :=
by rw [binary_fraction, ← power_def, mk_nat, mk_bool]

@[simp] lemma mk_binary_fraction_quotient : #(quotient binary_fraction.setoid) = 2 ^ omega.{0} :=
begin
  rw ← mk_binary_fraction,
  refine mk_quotient_le.antisymm _,
  set f : binary_fraction → quotient binary_fraction.setoid :=
    λ x, quotient.mk (x ⋈ (λ _, ff)),
  have inj : injective f := λ x y h, eq_of_eqv_interleave (quotient.exact h),
  exact mk_le_of_injective inj
end

universe u

variables {α : Type u} [conditionally_complete_lattice α] [densely_ordered α]

lemma le_mk_Icc {a b : α} (h : a < b) :
  (2 : cardinal.{u}) ^ omega.{u} ≤ #(Icc a b) :=
begin
  set c : Π I : nonempty_interval α, (Ioo I.left I.right) :=
    λ I, classical.indefinite_description _ (nonempty_Ioo.2 I.hlt),
  set f : quotient binary_fraction.setoid → Icc a b :=
    λ x, ⟨x.out.decode c ⟨a, b, h⟩, x.out.decode_mem_Icc _ _ 0⟩,
  have hf : strict_mono f := strict_mono_decode_out c _,
  have := mk_le_of_injective (equiv.ulift.{0 u}.symm.injective.comp $
    hf.injective.comp equiv.ulift.{u 0}.injective),
  simpa [← lift_mk, ← lift_le.{u 0}] using this
end

lemma omega_lt_mk_Icc {a b : α} (h : a < b) : omega.{u} < #(Icc a b) :=
(cantor _).trans_le (le_mk_Icc h)

lemma le_mk_Ioo {a b : α} (h : a < b) :
  (2 : cardinal.{u}) ^ omega.{u} ≤ #(Ioo a b) :=
begin
  refine (le_mk_Icc h).trans_eq (cardinal.eq_of_add_eq_add_right _ one_lt_omega),
  rw add_one_eq (omega_lt_mk_Icc h).le,
  refine cardinal.eq_of_add_eq_add_right _ one_lt_omega,
  rw [add_one_eq (omega_lt_mk_Icc h).le, ← Ico_union_right h.le, union_singleton, mk_insert,
    ← Ioo_union_left h, union_singleton, mk_insert]; simp
end

lemma le_mk_Ico {a b : α} (h : a < b) :
  (2 : cardinal.{u}) ^ omega.{u} ≤ #(Ico a b) :=
(le_mk_Ioo h).trans (mk_le_mk_of_subset Ioo_subset_Ico_self)

lemma le_mk_Ioc {a b : α} (h : a < b) :
  (2 : cardinal.{u}) ^ omega.{u} ≤ #(Ioc a b) :=
(le_mk_Ioo h).trans (mk_le_mk_of_subset Ioo_subset_Ioc_self)

variable (α)

lemma le_mk_of_conditionally_complete_lattice [nontrivial α] :
  (2 : cardinal.{u}) ^ omega.{u} ≤ #α :=
let ⟨a, b, h⟩ := exists_lt_of_inf α in (le_mk_Icc h).trans $ mk_set_le _

end cardinal
