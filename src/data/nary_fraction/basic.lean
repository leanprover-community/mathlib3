/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.setoid.basic
import data.pi.lex
import data.fin.basic

/-- A binary fraction is a sequence of zeros and ones. We use a map `ℕ → bool` to represent it, with
`ff` encoding zero and `tt` encoding one. -/
@[derive linear_order]
def nary_fraction (N : ℕ) : Type := Πₗ n : ℕ, fin N

variables {N : ℕ} {x y z a b a' b' : nary_fraction N}

open function set bool

namespace nary_fraction

instance : inhabited (nary_fraction (N + 1)) := pi.inhabited _
instance : bounded_order (nary_fraction (N + 1)) := pi.lex.bounded_order
instance : nontrivial (nary_fraction (N + 2)) := pi.nontrivial

lemma pos (x : nary_fraction N) : 0 < N := (zero_le _).trans_lt (x 0).2

lemma one_le (x : nary_fraction N) : 1 ≤ N := nat.succ_le_iff.2 x.pos

lemma exists_eq_succ (x : nary_fraction N) : ∃ k, N = k + 1 :=
le_iff_exists_add'.1 x.one_le

lemma subsingleton_iff_le_one : subsingleton (nary_fraction N) ↔ N ≤ 1 :=
begin
  refine ⟨λ h, _, λ h, @pi.subsingleton _ _ (λ n, fin.subsingleton_iff_le_one.2 h)⟩,
  contrapose! h,
  rcases le_iff_exists_add'.1 (nat.succ_le_iff.2 h) with ⟨N, rfl⟩,
  exact not_subsingleton _
end

lemma nontrivial_iff_two_le : nontrivial (nary_fraction N) ↔ 2 ≤ N :=
by rw [← not_iff_not, not_nontrivial_iff_subsingleton, subsingleton_iff_le_one, not_le,
  nat.lt_succ_iff]

lemma two_le_of_ne (h : x ≠ y) : 2 ≤ N := nontrivial_iff_two_le.1 ⟨⟨x, y, h⟩⟩

def tail (x : nary_fraction N) : nary_fraction N := λ n, x (n + 1)

@[simp] lemma tail_apply (x : nary_fraction N) (n : ℕ) : x.tail n = x (n + 1) := rfl

def cons (i : fin N) (x : nary_fraction N) : nary_fraction N :=
λ n, nat.cases_on n i x

@[simp] lemma cons_apply_zero (i : fin N) (x : nary_fraction N) : cons i x 0 = i := rfl

@[simp] lemma cons_apply_succ (i : fin N) (x : nary_fraction N) (n : ℕ) :
  cons i x (n + 1) = x n :=
rfl

lemma cons_head_tail (x : nary_fraction N) : cons (x 0) (tail x) = x :=
funext $ by rintro (_|n); refl

@[simp] lemma tail_cons (i : fin N) (x : nary_fraction N) : tail (cons i x) = x := rfl

@[simps] def cons_equiv : (fin N × nary_fraction N) ≃ nary_fraction N :=
{ to_fun := λ x, cons x.1 x.2,
  inv_fun := λ x, (x 0, tail x),
  left_inv := λ ⟨i, x⟩, rfl,
  right_inv := cons_head_tail }

def tail_rel (x y : nary_fraction N) :=
∃ (k : ℕ), (∀ i < k, x i = y i) ∧ (x k + 1 : ℕ) = y k ∧
  (∀ i > k, (x i + 1 : ℕ) = N) ∧ (∀ i > k, (y i : ℕ) = 0)

lemma tail_rel_iff {x y : nary_fraction (N + 1)} :
  tail_rel x y ↔ ∃ (k : ℕ), (∀ i < k, x i = y i) ∧ (x k + 1 : ℕ) = y k ∧
    (∀ i > k, x i = fin.last N) ∧ (∀ i > k, y i = 0) :=
by simp only [tail_rel, fin.coe_eq_zero, fin.coe_eq_iff_eq_last, add_left_inj]

namespace tail_rel

protected lemma lt (h : tail_rel x y) : x < y :=
begin
  rcases h with ⟨k, h_eq, hxy, hx, hy⟩,
  refine ⟨k, h_eq, _⟩,
  simpa only [fin.lt_iff_coe_lt_coe, ← hxy] using nat.lt_succ_self _
end

protected lemma le (h : tail_rel x y) : x ≤ y := h.lt.le

lemma two_le (h : tail_rel x y) : 2 ≤ N := two_le_of_ne h.lt.ne

lemma one_lt (h : tail_rel x y) : 1 < N := nat.succ_le_iff.1 h.two_le

lemma exists_eq_add_two (h : tail_rel x y) : ∃ k, N = k + 2 :=
le_iff_exists_add'.1 h.two_le

/-- The same fraction can not have a tail of `ff`s and a tail of `tt`s at the same time. -/
lemma strong_asymm (h : tail_rel x y) (z : nary_fraction N) : ¬ tail_rel y z :=
begin
  have := h.one_lt,
  rcases h with ⟨k, -, -, -, hk⟩, rintro ⟨l, -, -, hl, -⟩,
  specialize hk (max k l + 1) ((le_max_left k l).trans_lt $ nat.lt_succ_self _),
  specialize hl (max k l + 1) ((le_max_right k l).trans_lt $ nat.lt_succ_self _),
  rw [hk, zero_add] at hl,
  exact this.ne hl
end

lemma right_le_of_left_lt (h₁ : tail_rel x y) (h₂ : x < z) : y ≤ z :=
begin
  rcases h₁ with ⟨K, hlt, hxy, hxgt, hygt⟩,
  rcases h₂ with ⟨N, hltN, hN⟩,
  rw [fin.lt_iff_coe_lt_coe, nat.lt_iff_add_one_le] at hN,
  rcases lt_trichotomy K N with (hKN|rfl|hNK),
  { rw [hxgt N hKN] at hN,
    exact absurd hN (z N).is_lt.not_le },
  { refine pi.lex.le_of_forall_le (λ i, _),
    rw [hxy] at hN,
    rcases lt_trichotomy i K with (hiK|rfl|hKi),
    exacts [hlt i hiK ▸ (hltN _ hiK).le, hN,
      fin.le_iff_coe_le_coe.2 $ (hygt _ hKi).symm ▸ zero_le _] },
  { exact le_of_lt ⟨N, λ j hj, hlt j (hj.trans hNK) ▸ hltN _ hj, hlt N hNK ▸ hN⟩ }
end

lemma le_left_of_lt_right (h₁ : tail_rel y z) (h₂ : x < z) : x ≤ y :=
le_of_not_lt $ λ h, (h₁.right_le_of_left_lt h).not_lt h₂

protected lemma left_unique (h₁ : tail_rel x z) (h₂ : tail_rel y z) : x = y :=
le_antisymm (h₂.le_left_of_lt_right h₁.lt) (h₁.le_left_of_lt_right h₂.lt)

protected lemma right_unique (h₁ : tail_rel x y) (h₂ : tail_rel x z) : y = z :=
le_antisymm (h₁.right_le_of_left_lt h₂.lt) (h₂.right_le_of_left_lt h₁.lt)

end tail_rel

lemma not_tail_rel_bot (x : nary_fraction (N + 1)) : ¬tail_rel ⊥ x :=
λ ⟨k, h₁, h₂, h₃, h₄⟩, (x k).is_lt.ne' $
  by simp_rw [← h₃ (k + 1) k.lt_succ_self, ← h₂, pi.bot_apply]

lemma not_tail_rel_top (x : nary_fraction (N + 1)) : ¬tail_rel x ⊤ :=
λ ⟨k, h₁, h₂, h₃, h₄⟩, absurd (h₄ (k + 1) k.lt_succ_self) $
  by { simp only [pi.top_apply] at *, simp only [← h₂, nat.succ_ne_zero, not_false_iff] }

instance : setoid (nary_fraction N) :=
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

lemma tail_rel.eqv (h : tail_rel x y) : x ≈ y := or.inr (or.inl h)
lemma tail_rel.eqv' (h : tail_rel x y) : y ≈ x := or.inr (or.inr h)

lemma eqv_def : x ≈ y ↔ x = y ∨ tail_rel x y ∨ tail_rel y x := iff.rfl

lemma lt_of_lt_of_eqv_not_eqv {a a' b b' : nary_fraction N} (hlt : a < b) (ha : a ≈ a')
  (hb : b ≈ b') (hne : ¬ a ≈ b) :
  a' < b' :=
begin
  rcases ⟨ha, hb⟩ with ⟨(rfl|ha|ha), (rfl|hb|hb)⟩,
  { exact hlt },
  { exact hlt.trans hb.lt },
  { exact (hb.le_left_of_lt_right hlt).lt_of_ne (λ hab', hne $ hab'.symm ▸ hb.eqv) },
  { exact (ha.right_le_of_left_lt hlt).lt_of_ne (λ ha'b, hne $ ha'b ▸ ha.eqv) },
  { exact (ha.right_le_of_left_lt hlt).trans_lt hb.lt },
  { refine (ha.right_le_of_left_lt ((hb.le_left_of_lt_right hlt).lt_of_ne $ _)).lt_of_ne _,
    { rintro rfl, obtain rfl : a' = b := ha.right_unique hb, exact hne hb.eqv },
    { rintro rfl, exact ha.strong_asymm _ hb } },
  { exact ha.lt.trans hlt },
  { exact ha.lt.trans (hlt.trans hb.lt) },
  { exact ha.lt.trans_le (hb.le_left_of_lt_right hlt) }
end

noncomputable instance : linear_order (quotient (@nary_fraction.setoid N)) :=
linear_order.lift quotient.out $ (λ _ _, quotient.out_inj.1)

lemma mkq_lt_mkq : ⟦x⟧ < ⟦y⟧ ↔ x < y ∧ ¬ x ≈ y :=
begin
  refine ⟨λ hlt, _, λ hlt, _⟩,
  { refine ⟨lt_of_lt_of_eqv_not_eqv hlt (quotient.mk_out _) (quotient.mk_out _) (λ h, _), _⟩,
    exacts [hlt.ne (quotient.out_equiv_out.1 h), λ h, hlt.ne (quotient.sound h)] },
  { exact lt_of_lt_of_eqv_not_eqv hlt.1 (setoid.symm $ quotient.mk_out _)
      (setoid.symm $ quotient.mk_out _) hlt.2 }
end

lemma mkq_lt_mkq' : ⟦x⟧ < ⟦y⟧ ↔ x < y ∧ ¬ tail_rel x y :=
mkq_lt_mkq.trans $ and_congr_right $ λ hlt, not_congr $
  ⟨λ h, (h.resolve_left hlt.ne).resolve_right (λ h, h.lt.not_lt hlt), λ h, h.eqv⟩

lemma mkq_le_mkq : ⟦x⟧ ≤ ⟦y⟧ ↔ x ≤ y ∨ x ≈ y :=
begin
  simp only [← not_lt, mkq_lt_mkq, not_and_distrib, not_not],
  exact or_congr iff.rfl ⟨setoid.symm, setoid.symm⟩
end

lemma mkq_le_mkq' : ⟦x⟧ ≤ ⟦y⟧ ↔ x ≤ y ∨ tail_rel y x :=
by simp only [← not_lt, mkq_lt_mkq', not_and_distrib, not_not]

lemma monotone_mkq : monotone (λ x : nary_fraction N, ⟦x⟧) :=
λ x y h, mkq_le_mkq.2 (or.inl h)

def interleave (x y : nary_fraction N) : nary_fraction N :=
λ n, nat.bit_cases_on n (λ b, cond b y x)

@[simp] lemma interleave_bit0 (x y : nary_fraction N) (n : ℕ) :
  interleave x y (bit0 n) = x n :=
nat.bit_cases_on_bit0 _ _

@[simp] lemma interleave_bit1 (x y : nary_fraction N) (n : ℕ) :
  interleave x y (bit1 n) = y n :=
nat.bit_cases_on_bit1 _ _

@[simp] lemma interleave_bit (x y : nary_fraction N) (b : bool) (n : ℕ) :
  interleave x y (nat.bit b n) = cond b (y n) (x n) :=
by { cases b, exacts [interleave_bit0 x y n, interleave_bit1 x y n] }

@[simp] lemma interleave_inj : interleave a b = interleave a' b' ↔ a = a' ∧ b = b' :=
by simp_rw [interleave, nat.bit_cases_on_inj, funext_iff, bool.forall_bool, cond]

lemma not_tail_rel_interleave_same : ¬tail_rel (interleave x z) (interleave y z) :=
begin
  intro h, have := h.one_lt,
  rcases h with ⟨k, -, -, hx, hy⟩,
  have hk : k < bit1 k, by simp [bit1, bit0, add_assoc],
  specialize hx _ hk, specialize hy _ hk,
  rw [interleave_bit1] at hx hy,
  rw [hy, zero_add] at hx,
  exact this.ne hx
end

lemma injective_interleave_zero :
  injective (λ x, ⟦interleave x (λ n, ⟨0, x.pos⟩)⟧ :
    nary_fraction N → quotient (@nary_fraction.setoid N)) :=
begin
  intros x y h,
  simp only [quotient.eq, eqv_def] at h,
  rcases h with h|h|h,
  exacts [(interleave_inj.1 h).1, absurd h not_tail_rel_interleave_same,
    absurd h not_tail_rel_interleave_same]
end

end nary_fraction
