/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Verification of the `ordnode α` datatype, with a type `ordset α` of verified
sets.
-/
import data.ordmap.ordnode algebra.ordered_ring data.nat.dist tactic.linarith

theorem cmp_le_flip {α} [has_le α] [@decidable_rel α (≤)] (x y : α) :
  @cmp_le (order_dual α) _ _ x y = cmp_le y x := rfl

theorem cmp_le_swap {α} [has_le α] [is_total α (≤)] [@decidable_rel α (≤)] (x y : α) :
  (cmp_le x y).swap = cmp_le y x :=
begin
  simp [cmp_le], split_ifs; try {refl},
  cases not_or h h_1 (total_of _ _ _)
end

variable {α : Type*}
namespace ordnode

theorem not_le_delta {s} (H : 1 ≤ s) : ¬ s ≤ delta * 0 :=
λ h, by rw mul_zero at h; exact not_lt_of_le h H

theorem delta_lt_false {a b : ℕ}
  (h₁ : delta * a < b) (h₂ : delta * b < a) : false :=
not_le_of_lt (lt_trans ((mul_lt_mul_left dec_trivial).2 h₁) h₂) $
by simpa [mul_assoc] using nat.mul_le_mul_right a (dec_trivial : 1 ≤ delta * delta)

theorem dual_dual : ∀ (t : ordnode α), dual (dual t) = t
| nil := rfl
| (node s l x r) := by rw [dual, dual, dual_dual, dual_dual]

theorem all_dual {P : α → Prop} : ∀ {t : ordnode α},
  all P (dual t) ↔ all P t
| nil := iff.rfl
| (node s l x r) :=
  ⟨λ ⟨hr, hx, hl⟩, ⟨all_dual.1 hl, hx, all_dual.1 hr⟩,
   λ ⟨hl, hx, hr⟩, ⟨all_dual.2 hr, hx, all_dual.2 hl⟩⟩

theorem all_singleton {P : α → Prop} {x : α} : all P (singleton x) ↔ P x :=
⟨λ h, h.2.1, λ h, ⟨⟨⟩, h, ⟨⟩⟩⟩

theorem all.imp {P Q : α → Prop} (H : ∀ a, P a → Q a) : ∀ {s}, all P s → all Q s
| nil h := ⟨⟩
| (node _ l x r) ⟨h₁, h₂, h₃⟩ := ⟨h₁.imp, H _ h₂, h₃.imp⟩

@[simp] theorem size_dual (t : ordnode α) : size (dual t) = size t :=
by cases t; refl

def node3_l (l : ordnode α) (x : α) (m : ordnode α) (y : α) (r : ordnode α) : ordnode α :=
node' (node' l x m) y r

def node3_r (l : ordnode α) (x : α) (m : ordnode α) (y : α) (r : ordnode α) : ordnode α :=
node' l x (node' m y r)

def node4_l : ordnode α → α → ordnode α → α → ordnode α → ordnode α
| l x (node _ ml y mr) z r := node' (node' l x ml) y (node' mr z r)
| l x nil z r := node3_l l x nil z r -- should not happen

def node4_r : ordnode α → α → ordnode α → α → ordnode α → ordnode α
| l x (node _ ml y mr) z r := node' (node' l x ml) y (node' mr z r)
| l x nil z r := node3_r l x nil z r -- should not happen

def rotate_l : ordnode α → α → ordnode α → ordnode α
| l x (node _ m y r) :=
  if size m < ratio * size r then node3_l l x m y r else node4_l l x m y r
| l x nil := node' l x nil -- should not happen

def rotate_r : ordnode α → α → ordnode α → ordnode α
| (node _ l x m) y r :=
  if size m < ratio * size l then node3_r l x m y r else node4_r l x m y r
| nil y r :=  node' nil y r -- should not happen

def balance' (l : ordnode α) (x : α) (r : ordnode α) : ordnode α :=
if size l + size r ≤ 1 then node' l x r else
if size r > delta * size l then rotate_l l x r else
if size l > delta * size r then rotate_r l x r else
node' l x r

theorem dual_node' (l : ordnode α) (x : α) (r : ordnode α) :
  dual (node' l x r) = node' (dual r) x (dual l) := by simp [node']

theorem dual_node3_l (l : ordnode α) (x : α) (m : ordnode α) (y : α) (r : ordnode α) :
  dual (node3_l l x m y r) = node3_r (dual r) y (dual m) x (dual l) :=
by simp [node3_l, node3_r, dual_node']

theorem dual_node3_r (l : ordnode α) (x : α) (m : ordnode α) (y : α) (r : ordnode α) :
  dual (node3_r l x m y r) = node3_l (dual r) y (dual m) x (dual l) :=
by simp [node3_l, node3_r, dual_node']

theorem dual_node4_l (l : ordnode α) (x : α) (m : ordnode α) (y : α) (r : ordnode α) :
  dual (node4_l l x m y r) = node4_r (dual r) y (dual m) x (dual l) :=
by cases m; simp [node4_l, node4_r, dual_node3_l, dual_node']

theorem dual_node4_r (l : ordnode α) (x : α) (m : ordnode α) (y : α) (r : ordnode α) :
  dual (node4_r l x m y r) = node4_l (dual r) y (dual m) x (dual l) :=
by cases m; simp [node4_l, node4_r, dual_node3_r, dual_node']

theorem dual_rotate_l (l : ordnode α) (x : α) (r : ordnode α) :
  dual (rotate_l l x r) = rotate_r (dual r) x (dual l) :=
by cases r; simp [rotate_l, rotate_r, dual_node'];
   split_ifs; simp [dual_node3_l, dual_node4_l]

theorem dual_rotate_r (l : ordnode α) (x : α) (r : ordnode α) :
  dual (rotate_r l x r) = rotate_l (dual r) x (dual l) :=
by rw [← dual_dual (rotate_l _ _ _), dual_rotate_l, dual_dual, dual_dual]

theorem dual_balance' (l : ordnode α) (x : α) (r : ordnode α) :
  dual (balance' l x r) = balance' (dual r) x (dual l) :=
begin
  simp [balance']; split_ifs; simp [dual_node', dual_rotate_l, dual_rotate_r],
  cases delta_lt_false h_1 h_2
end

theorem dual_balance_l (l : ordnode α) (x : α) (r : ordnode α) :
  dual (balance_l l x r) = balance_r (dual r) x (dual l) :=
begin
  unfold balance_l balance_r,
  cases r with rs rl rx rr,
  { cases l with ls ll lx lr, {refl},
    cases ll with lls lll llx llr; cases lr with lrs lrl lrx lrr;
      dsimp only [dual]; try {refl},
    split_ifs; repeat {simp [h]} },
  { cases l with ls ll lx lr, {refl},
    dsimp only [dual],
    split_ifs, swap, {simp},
    cases ll with lls lll llx llr; cases lr with lrs lrl lrx lrr; try {refl},
    dsimp only [dual],
    split_ifs; simp [h] },
end

theorem dual_balance_r (l : ordnode α) (x : α) (r : ordnode α) :
  dual (balance_r l x r) = balance_l (dual r) x (dual l) :=
by rw [← dual_dual (balance_l _ _ _), dual_balance_l, dual_dual, dual_dual]

theorem dual_erase_min : ∀ t : ordnode α, dual (erase_min t) = erase_max (dual t)
| nil := rfl
| (node _ nil x r) := rfl
| (node _ l@(node _ _ _ _) x r) :=
  by rw [erase_min, dual_balance_r, dual_erase_min, dual, dual, dual, erase_max]

theorem dual_erase_max (t : ordnode α) : dual (erase_max t) = erase_min (dual t) :=
by rw [← dual_dual (erase_min _), dual_erase_min, dual_dual]

theorem dual_insert [preorder α] [is_total α (≤)] [@decidable_rel α (≤)] (x : α) :
  ∀ t : ordnode α, dual (insert x t) = @insert (order_dual α) _ _ x (dual t)
| nil := rfl
| (node _ l y r) := begin
  rw [insert, dual, insert, cmp_le_flip, ← cmp_le_swap x y],
  cases cmp_le x y; simp [ordering.swap, insert, dual_balance_l, dual_balance_r, dual_insert]
end

theorem all_node' {P l x r} :
  @all α P (node' l x r) ↔ all P l ∧ P x ∧ all P r := iff.rfl

theorem all_node3_l {P l x m y r} :
  @all α P (node3_l l x m y r) ↔ all P l ∧ P x ∧ all P m ∧ P y ∧ all P r :=
by simp [node3_l, all_node', and_assoc]

theorem all_node3_r {P l x m y r} :
  @all α P (node3_r l x m y r) ↔ all P l ∧ P x ∧ all P m ∧ P y ∧ all P r := iff.rfl

theorem all_node4_l {P l x m y r} :
  @all α P (node4_l l x m y r) ↔ all P l ∧ P x ∧ all P m ∧ P y ∧ all P r :=
by cases m; simp [node4_l, all_node', all, all_node3_l, and_assoc]

theorem all_node4_r {P l x m y r} :
  @all α P (node4_r l x m y r) ↔ all P l ∧ P x ∧ all P m ∧ P y ∧ all P r :=
by cases m; simp [node4_r, all_node', all, all_node3_r, and_assoc]

theorem all_rotate_l {P l x r} :
  @all α P (rotate_l l x r) ↔ all P l ∧ P x ∧ all P r :=
by cases r; simp [rotate_l, all_node'];
   split_ifs; simp [all_node3_l, all_node4_l, all]

theorem all_rotate_r {P l x r} :
  @all α P (rotate_r l x r) ↔ all P l ∧ P x ∧ all P r :=
by rw [← all_dual, dual_rotate_r, all_rotate_l];
   simp [all_dual, and_comm, and.left_comm]

theorem all_balance' {P l x r} :
  @all α P (balance' l x r) ↔ all P l ∧ P x ∧ all P r :=
by rw balance'; split_ifs; simp [all_node', all_rotate_l, all_rotate_r]

def sized : ordnode α → Prop
| nil := true
| (node s l _ r) := s = size l + size r + 1 ∧ sized l ∧ sized r

theorem sized.node' {l x r} (hl : @sized α l) (hr : sized r) : sized (node' l x r) :=
⟨rfl, hl, hr⟩

theorem sized.eq_node' {s l x r} (h : @sized α (node s l x r)) : node s l x r = node' l x r :=
by rw h.1; refl

theorem sized.size_eq {s l x r} (H : sized (@node α s l x r)) :
  size (@node α s l x r) = size l + size r + 1 := H.1

@[elab_as_eliminator] theorem sized.induction {t} (hl : @sized α t)
  {C : ordnode α → Prop} (H0 : C nil)
  (H1 : ∀ l x r, C l → C r → C (node' l x r)) : C t :=
begin
  induction t, {exact H0},
  rw hl.eq_node',
  exact H1 _ _ _ (t_ih_l hl.2.1) (t_ih_r hl.2.2)
end

theorem sized.node3_l {l x m y r}
  (hl : @sized α l) (hm : sized m) (hr : sized r) : sized (node3_l l x m y r) :=
(hl.node' hm).node' hr

theorem sized.node3_r {l x m y r}
  (hl : @sized α l) (hm : sized m) (hr : sized r) : sized (node3_r l x m y r) :=
hl.node' (hm.node' hr)

theorem sized.node4_l {l x m y r}
  (hl : @sized α l) (hm : sized m) (hr : sized r) : sized (node4_l l x m y r) :=
by cases m; [exact (hl.node' hm).node' hr,
  exact (hl.node' hm.2.1).node' (hm.2.2.node' hr)]

theorem node3_l_size {l x m y r} :
  size (@node3_l α l x m y r) = size l + size m + size r + 2 :=
by dsimp [node3_l, node', size]; rw add_right_comm _ 1

theorem node3_r_size {l x m y r} :
  size (@node3_r α l x m y r) = size l + size m + size r + 2 :=
by dsimp [node3_r, node', size]; rw [← add_assoc, ← add_assoc]

theorem node4_l_size {l x m y r} (hm : sized m) :
  size (@node4_l α l x m y r) = size l + size m + size r + 2 :=
by cases m; simp [node4_l, node3_l, node']; [skip, simp [size, hm.1]];
   rw [← add_assoc, ← bit0]; simp

theorem sized.dual : ∀ {t : ordnode α} (h : sized t), sized (dual t)
| nil h := ⟨⟩
| (node s l x r) ⟨rfl, sl, sr⟩ := ⟨by simp [size_dual], sized.dual sr, sized.dual sl⟩

theorem sized.dual_iff {t : ordnode α} : sized (dual t) ↔ sized t :=
⟨λ h, by rw ← dual_dual t; exact h.dual, sized.dual⟩

theorem sized.rotate_l {l x r} (hl : @sized α l) (hr : sized r) : sized (rotate_l l x r) :=
begin
  cases r, {exact hl.node' hr},
  rw rotate_l, split_ifs,
  { exact hl.node3_l hr.2.1 hr.2.2 },
  { exact hl.node4_l hr.2.1 hr.2.2 }
end

theorem sized.rotate_r {l x r} (hl : @sized α l) (hr : sized r) : sized (rotate_r l x r) :=
sized.dual_iff.1 $ by rw dual_rotate_r; exact hr.dual.rotate_l hl.dual

theorem sized.rotate_l_size {l x r} (hm : sized r) :
  size (@rotate_l α l x r) = size l + size r + 1 :=
begin
  cases r; simp [rotate_l, node'],
  simp [size, hm.1], rw [← add_assoc, ← bit0], simp,
  split_ifs; simp [node3_l_size, node4_l_size hm.2.1]
end

theorem sized.rotate_r_size {l x r} (hl : sized l) :
  size (@rotate_r α l x r) = size l + size r + 1 :=
by rw [← size_dual, dual_rotate_r, hl.dual.rotate_l_size,
  size_dual, size_dual, add_comm (size l)]

theorem sized.balance' {l x r} (hl : @sized α l) (hr : sized r) : sized (balance' l x r) :=
begin
  unfold balance', split_ifs,
  { exact hl.node' hr },
  { exact hl.rotate_l hr },
  { exact hl.rotate_r hr },
  { exact hl.node' hr }
end

theorem sized.balance'_size {l x r} (hl : @sized α l) (hr : sized r) :
  size (@balance' α l x r) = size l + size r + 1 :=
begin
  unfold balance', split_ifs,
  { refl },
  { exact hr.rotate_l_size },
  { exact hl.rotate_r_size },
  { refl }
end

@[simp] theorem sized.size_eq_zero {t : ordnode α} (ht : sized t) : size t = 0 ↔ t = nil :=
by cases t; [simp, simp [ht.1]]

theorem sized.pos {s l x r} (h : sized (@node α s l x r)) : 0 < s :=
by rw h.1; apply nat.le_add_left

def balanced_sz (l r : ℕ) : Prop :=
l + r ≤ 1 ∨ (l ≤ delta * r ∧ r ≤ delta * l)

instance balanced_sz.dec : decidable_rel balanced_sz := λ l r, or.decidable

def balanced : ordnode α → Prop
| nil := true
| (node _ l _ r) := balanced_sz (size l) (size r) ∧ balanced l ∧ balanced r

theorem balanced_sz.symm {l r : ℕ} : balanced_sz l r → balanced_sz r l :=
or.imp (by rw add_comm; exact id) and.symm

theorem balanced_sz_zero {l : ℕ} : balanced_sz l 0 ↔ l ≤ 1 :=
by simp [balanced_sz]; apply or_iff_left_of_imp; rintro rfl; exact zero_le_one

theorem balanced_sz_up {l r₁ r₂ : ℕ} (h₁ : r₁ ≤ r₂)
  (h₂ : l + r₂ ≤ 1 ∨ r₂ ≤ delta * l)
  (H : balanced_sz l r₁) : balanced_sz l r₂ :=
begin
  refine or_iff_not_imp_left.2 (λ h, _),
  refine ⟨_, h₂.resolve_left h⟩,
  cases H,
  { cases r₂,
    { cases h (le_trans (nat.add_le_add_left (nat.zero_le _) _) H) },
    { exact le_trans (le_trans (nat.le_add_right _ _) H) (nat.le_add_left 1 _) } },
  { exact le_trans H.1 (nat.mul_le_mul_left _ h₁) }
end

theorem balanced_sz_down {l r₁ r₂ : ℕ} (h₁ : r₁ ≤ r₂)
  (h₂ : l + r₂ ≤ 1 ∨ l ≤ delta * r₁)
  (H : balanced_sz l r₂) : balanced_sz l r₁ :=
have l + r₂ ≤ 1 → balanced_sz l r₁, from
  λ H, or.inl (le_trans (nat.add_le_add_left h₁ _) H),
or.cases_on H this (λ H, or.cases_on h₂ this (λ h₂,
  or.inr ⟨h₂, le_trans h₁ H.2⟩))

theorem balanced.dual : ∀ {t : ordnode α}, balanced t → balanced (dual t)
| nil h := ⟨⟩
| (node s l x r) ⟨b, bl, br⟩ :=
  ⟨by rw [size_dual, size_dual]; exact b.symm, br.dual, bl.dual⟩

theorem balance_eq_balance' {l x r}
  (hl : balanced l) (hr : balanced r)
  (sl : sized l) (sr : sized r) :
  @balance α l x r = balance' l x r :=
begin
  cases l with ls ll lx lr,
  { cases r with rs rl rx rr,
    { refl },
    { rw sr.eq_node' at hr ⊢,
      cases rl with rls rll rlx rlr; cases rr with rrs rrl rrx rrr;
      dsimp [balance, balance', node'],
      { refl },
      { have : size rrl = 0 ∧ size rrr = 0,
        { have := balanced_sz_zero.1 hr.1.symm,
          rwa [size, sr.2.2.1, nat.succ_le_succ_iff,
            nat.le_zero_iff, add_eq_zero_iff] at this },
        cases sr.2.2.2.1.size_eq_zero.1 this.1,
        cases sr.2.2.2.2.size_eq_zero.1 this.2,
        have : rrs = 1 := sr.2.2.1, subst rrs,
        rw [if_neg, if_pos, rotate_l, if_pos], {refl},
        all_goals {exact dec_trivial} },
      { have : size rll = 0 ∧ size rlr = 0,
        { have := balanced_sz_zero.1 hr.1,
          rwa [size, sr.2.1.1, nat.succ_le_succ_iff,
            nat.le_zero_iff, add_eq_zero_iff] at this },
        cases sr.2.1.2.1.size_eq_zero.1 this.1,
        cases sr.2.1.2.2.size_eq_zero.1 this.2,
        have : rls = 1 := sr.2.1.1, subst rls,
        rw [if_neg, if_pos, rotate_l, if_neg], {refl},
        all_goals {exact dec_trivial} },
      { symmetry, rw [zero_add, if_neg, if_pos, rotate_l],
        { split_ifs,
          { simp [node3_l, node'] },
          { simp [node4_l, node', sr.2.1.1] } },
        { exact dec_trivial },
        { exact not_le_of_gt (nat.succ_lt_succ
            (add_pos sr.2.1.pos sr.2.2.pos)) } } } },
  { cases r with rs rl rx rr,
    { rw sl.eq_node' at hl ⊢,
      cases ll with lls lll llx llr; cases lr with lrs lrl lrx lrr;
      dsimp [balance, balance', node'],
      { refl },
      { have : size lrl = 0 ∧ size lrr = 0,
        { have := balanced_sz_zero.1 hl.1.symm,
          rwa [size, sl.2.2.1, nat.succ_le_succ_iff,
            nat.le_zero_iff, add_eq_zero_iff] at this },
        cases sl.2.2.2.1.size_eq_zero.1 this.1,
        cases sl.2.2.2.2.size_eq_zero.1 this.2,
        have : lrs = 1 := sl.2.2.1, subst lrs,
        rw [if_neg, if_neg, if_pos, rotate_r, if_neg], {refl},
        all_goals {exact dec_trivial} },
      { have : size lll = 0 ∧ size llr = 0,
        { have := balanced_sz_zero.1 hl.1,
          rwa [size, sl.2.1.1, nat.succ_le_succ_iff,
            nat.le_zero_iff, add_eq_zero_iff] at this },
        cases sl.2.1.2.1.size_eq_zero.1 this.1,
        cases sl.2.1.2.2.size_eq_zero.1 this.2,
        have : lls = 1 := sl.2.1.1, subst lls,
        rw [if_neg, if_neg, if_pos, rotate_r, if_pos], {refl},
        all_goals {exact dec_trivial} },
      { symmetry, rw [if_neg, if_neg, if_pos, rotate_r],
        { split_ifs,
          { simp [node3_r, node'] },
          { simp [node4_r, node', sl.2.2.1] } },
        { exact dec_trivial },
        { exact dec_trivial },
        { exact not_le_of_gt (nat.succ_lt_succ
            (add_pos sl.2.1.pos sl.2.2.pos)) } } },
    { simp [balance, balance'],
      symmetry, rw [if_neg],
      { split_ifs,
        { have rd : delta ≤ size rl + size rr,
          { have := lt_of_le_of_lt (nat.mul_le_mul_left _ sl.pos) h,
            rwa [sr.1, nat.lt_succ_iff] at this },
          cases rl with rls rll rlx rlr,
          { rw [size, zero_add] at rd,
            exact absurd (le_trans rd (balanced_sz_zero.1 hr.1.symm)) dec_trivial },
          cases rr with rrs rrl rrx rrr,
          { exact absurd (le_trans rd (balanced_sz_zero.1 hr.1)) dec_trivial },
          dsimp [rotate_l], split_ifs,
          { simp [node3_l, node', sr.1] },
          { simp [node4_l, node', sr.1, sr.2.1.1] } },
        { have ld : delta ≤ size ll + size lr,
          { have := lt_of_le_of_lt (nat.mul_le_mul_left _ sr.pos) h_1,
            rwa [sl.1, nat.lt_succ_iff] at this },
          cases ll with lls lll llx llr,
          { rw [size, zero_add] at ld,
            exact absurd (le_trans ld (balanced_sz_zero.1 hl.1.symm)) dec_trivial },
          cases lr with lrs lrl lrx lrr,
          { exact absurd (le_trans ld (balanced_sz_zero.1 hl.1)) dec_trivial },
          dsimp [rotate_r], split_ifs,
          { simp [node3_r, node', sl.1] },
          { simp [node4_r, node', sl.1, sl.2.2.1] } },
        { simp [node'] } },
      { exact not_le_of_gt (add_le_add sl.pos sr.pos : 2 ≤ ls + rs) } } }
end

theorem balance_l_eq_balance {l x r}
  (sl : sized l) (sr : sized r)
  (H1 : l = nil → size r ≤ 1)
  (H2 : 1 ≤ size l → 1 ≤ size r → size r ≤ delta * size l) :
  @balance_l α l x r = balance l x r :=
begin
  cases r with rs rl rx rr,
  { refl },
  { cases l with ls ll lx lr,
    { have : size rl = 0 ∧ size rr = 0,
      { have := H1 rfl,
        rwa [size, sr.1, nat.succ_le_succ_iff,
          nat.le_zero_iff, add_eq_zero_iff] at this },
      cases sr.2.1.size_eq_zero.1 this.1,
      cases sr.2.2.size_eq_zero.1 this.2,
      rw sr.eq_node', refl },
    { replace H2 : ¬ rs > delta * ls := not_lt_of_le (H2 sl.pos sr.pos),
      simp [balance_l, balance, H2]; split_ifs; simp } }
end

theorem balance_l_eq_balance' {l x r}
  (hl : balanced l) (hr : balanced r)
  (sl : sized l) (sr : sized r)
  (H : (∃ l', size l = l' + 1 ∧ balanced_sz l' (size r)) ∨
       (∃ r', size r ≤ r' ∧ r' ≤ size r + 1 ∧ balanced_sz (size l) r')) :
  @balance_l α l x r = balance' l x r :=
begin
  rw [← balance_eq_balance' hl hr sl sr, balance_l_eq_balance sl sr],
  { rintro rfl,
    rcases H with ⟨_, ⟨⟩, _⟩ | ⟨r', e₁, e₂, H⟩,
    exact le_trans e₁ (balanced_sz_zero.1 H.symm) },
  { intros l1 r1,
    rcases H with ⟨l', e, H | ⟨H₁, H₂⟩⟩ | ⟨r', e₁, e₂, H | ⟨H₁, H₂⟩⟩,
    { exact le_trans (le_trans (nat.le_add_left _ _) H)
        (mul_pos dec_trivial l1 : (0:ℕ)<_) },
    { rw e, exact le_trans H₂ (nat.mul_le_mul_left _ (nat.le_succ _)) },
    { unfold delta, linarith },
    { exact le_trans e₁ H₂ } }
end

theorem balance_sz_dual {l r}
  (H : (∃ l', @size α l ≤ l' ∧ l' ≤ size l + 1 ∧ balanced_sz l' (@size α r)) ∨
    ∃ r', size r = r' + 1 ∧ balanced_sz (size l) r') :
  (∃ l', size (dual r) = l' + 1 ∧ balanced_sz l' (size (dual l))) ∨
    ∃ r', size (dual l) ≤ r' ∧ r' ≤ size (dual l) + 1 ∧ balanced_sz (size (dual r)) r' :=
begin
  rw [size_dual, size_dual],
  exact H.symm.imp
    (Exists.imp $ λ _, and.imp_right balanced_sz.symm)
    (Exists.imp $ λ _, and.imp_right $ and.imp_right balanced_sz.symm)
end

theorem balance_l_size {l x r}
  (hl : balanced l) (hr : balanced r)
  (sl : sized l) (sr : sized r)
  (H : (∃ l', size l = l' + 1 ∧ balanced_sz l' (size r)) ∨
       (∃ r', size r ≤ r' ∧ r' ≤ size r + 1 ∧ balanced_sz (size l) r')) :
  size (@balance_l α l x r) = size l + size r + 1 :=
by rw [balance_l_eq_balance' hl hr sl sr H, sl.balance'_size sr]

theorem all_balance_l {P l x r}
  (hl : balanced l) (hr : balanced r)
  (sl : sized l) (sr : sized r)
  (H : (∃ l', size l = l' + 1 ∧ balanced_sz l' (size r)) ∨
       (∃ r', size r ≤ r' ∧ r' ≤ size r + 1 ∧ balanced_sz (size l) r')) :
  all P (@balance_l α l x r) ↔ all P l ∧ P x ∧ all P r :=
by rw [balance_l_eq_balance' hl hr sl sr H, all_balance']

theorem balance_r_eq_balance' {l x r}
  (hl : balanced l) (hr : balanced r)
  (sl : sized l) (sr : sized r)
  (H : (∃ l', size l ≤ l' ∧ l' ≤ size l + 1 ∧ balanced_sz l' (size r)) ∨
       (∃ r', size r = r' + 1 ∧ balanced_sz (size l) r')) :
  @balance_r α l x r = balance' l x r :=
by rw [← dual_dual (balance_r l x r), dual_balance_r,
  balance_l_eq_balance' hr.dual hl.dual sr.dual sl.dual (balance_sz_dual H),
  ← dual_balance', dual_dual]

theorem balance_r_size {l x r}
  (hl : balanced l) (hr : balanced r)
  (sl : sized l) (sr : sized r)
  (H : (∃ l', size l ≤ l' ∧ l' ≤ size l + 1 ∧ balanced_sz l' (size r)) ∨
       (∃ r', size r = r' + 1 ∧ balanced_sz (size l) r')) :
  size (@balance_r α l x r) = size l + size r + 1 :=
by rw [balance_r_eq_balance' hl hr sl sr H, sl.balance'_size sr]

theorem all_balance_r {P l x r}
  (hl : balanced l) (hr : balanced r)
  (sl : sized l) (sr : sized r)
  (H : (∃ l', size l ≤ l' ∧ l' ≤ size l + 1 ∧ balanced_sz l' (size r)) ∨
       (∃ r', size r = r' + 1 ∧ balanced_sz (size l) r')) :
  all P (@balance_r α l x r) ↔ all P l ∧ P x ∧ all P r :=
by rw [balance_r_eq_balance' hl hr sl sr H, all_balance']

def bounded [preorder α] : ordnode α → with_bot α → with_top α → Prop
| nil (some a) (some b) := a < b
| nil _ _ := true
| (node _ l x r) o₁ o₂ := bounded l o₁ ↑x ∧ bounded r ↑x o₂

structure valid' [preorder α] (o₁ : with_bot α) (t : ordnode α) (o₂ : with_top α) : Prop :=
(ord : t.bounded o₁ o₂)
(sz : t.sized)
(bal : t.balanced)

def valid [preorder α] (t : ordnode α) : Prop := valid' ⊥ t ⊤

section
variable [preorder α]

theorem bounded.dual : ∀ {t : ordnode α} {o₁ o₂} (h : bounded t o₁ o₂),
  @bounded (order_dual α) _ (dual t) o₂ o₁
| nil o₁ o₂ h := by cases o₁; cases o₂; try {trivial}; exact h
| (node s l x r) _ _ ⟨ol, or⟩ := ⟨or.dual, ol.dual⟩

theorem bounded.dual_iff {t : ordnode α} {o₁ o₂} : bounded t o₁ o₂ ↔
  @bounded (order_dual α) _ (dual t) o₂ o₁ :=
⟨bounded.dual, λ h, by have := bounded.dual h;
  rwa [dual_dual, order_dual.preorder.dual_dual] at this⟩

theorem bounded.weak_left : ∀ {t : ordnode α} {o₁ o₂}, bounded t o₁ o₂ → bounded t ⊥ o₂
| nil o₁ o₂ h := by cases o₂; try {trivial}; exact h
| (node s l x r) _ _ ⟨ol, or⟩ := ⟨ol.weak_left, or⟩

theorem bounded.weak_right : ∀ {t : ordnode α} {o₁ o₂}, bounded t o₁ o₂ → bounded t o₁ ⊤
| nil o₁ o₂ h := by cases o₁; try {trivial}; exact h
| (node s l x r) _ _ ⟨ol, or⟩ := ⟨ol, or.weak_right⟩

theorem bounded.weak {t : ordnode α} {o₁ o₂} (h : bounded t o₁ o₂) : bounded t ⊥ ⊤ :=
h.weak_left.weak_right

theorem bounded.mono_left {x y : α} (xy : x ≤ y) : ∀ {t : ordnode α} {o}, bounded t ↑y o → bounded t ↑x o
| nil none h := ⟨⟩
| nil (some z) h := lt_of_le_of_lt xy h
| (node s l z r) o ⟨ol, or⟩ := ⟨ol.mono_left, or⟩

theorem bounded.mono_right {x y : α} (xy : x ≤ y) : ∀ {t : ordnode α} {o}, bounded t o ↑x → bounded t o ↑y
| nil none h := ⟨⟩
| nil (some z) h := lt_of_lt_of_le h xy
| (node s l z r) o ⟨ol, or⟩ := ⟨ol, or.mono_right⟩

theorem bounded.to_lt : ∀ {t : ordnode α} {x y : α}, bounded t x y → x < y
| nil x y h := h
| (node _ l y r) x z ⟨h₁, h₂⟩ := lt_trans h₁.to_lt h₂.to_lt

theorem bounded.to_nil {t : ordnode α} : ∀ {o₁ o₂}, bounded t o₁ o₂ → bounded nil o₁ o₂
| none _ h := ⟨⟩
| (some _) none h := ⟨⟩
| (some x) (some y) h := h.to_lt

theorem bounded.trans_left {t₁ t₂ : ordnode α} {x : α} : ∀ {o₁ o₂}, bounded t₁ o₁ ↑x → bounded t₂ ↑x o₂ → bounded t₂ o₁ o₂
| none o₂ h₁ h₂ := h₂.weak_left
| (some y) o₂ h₁ h₂ := h₂.mono_left (le_of_lt h₁.to_lt)

theorem bounded.trans_right {t₁ t₂ : ordnode α} {x : α} : ∀ {o₁ o₂}, bounded t₁ o₁ ↑x → bounded t₂ ↑x o₂ → bounded t₁ o₁ o₂
| o₁ none h₁ h₂ := h₁.weak_right
| o₁ (some y) h₁ h₂ := h₁.mono_right (le_of_lt h₂.to_lt)

theorem valid'.mono_left {x y : α} (xy : x ≤ y) {t : ordnode α} {o} (h : valid' ↑y t o) : valid' ↑x t o :=
⟨h.1.mono_left xy, h.2, h.3⟩

theorem valid'.mono_right {x y : α} (xy : x ≤ y) {t : ordnode α} {o} (h : valid' o t ↑x) : valid' o t ↑y :=
⟨h.1.mono_right xy, h.2, h.3⟩

theorem valid'.trans_left {t₁ t₂ : ordnode α} {x : α} {o₁ o₂}
  (h : bounded t₁ o₁ ↑x) (H : valid' ↑x t₂ o₂) : valid' o₁ t₂ o₂ :=
⟨h.trans_left H.1, H.2, H.3⟩

theorem valid'.trans_right {t₁ t₂ : ordnode α} {x : α} {o₁ o₂}
  (H : valid' o₁ t₁ ↑x) (h : bounded t₂ ↑x o₂) : valid' o₁ t₁ o₂ :=
⟨H.1.trans_right h, H.2, H.3⟩

theorem valid'.valid {t o₁ o₂} (h : @valid' α _ o₁ t o₂) : valid t := ⟨h.1.weak, h.2, h.3⟩

theorem valid'_nil {o₁ o₂} (h : bounded nil o₁ o₂) : valid' o₁ (@nil α) o₂ := ⟨h, ⟨⟩, ⟨⟩⟩

theorem valid_nil : valid (@nil α) := valid'_nil ⟨⟩

theorem valid'.node {s l x r o₁ o₂}
  (hl : valid' o₁ l ↑x) (hr : valid' ↑x r o₂)
  (H : balanced_sz (size l) (size r)) (hs : s = size l + size r + 1) :
  valid' o₁ (@node α s l x r) o₂ :=
⟨⟨hl.1, hr.1⟩, ⟨hs, hl.2, hr.2⟩, ⟨H, hl.3, hr.3⟩⟩

theorem valid'.dual : ∀ {t : ordnode α} {o₁ o₂} (h : valid' o₁ t o₂),
  @valid' (order_dual α) _ o₂ (dual t) o₁
| nil o₁ o₂ h := valid'_nil h.1.dual
| (node s l x r) o₁ o₂ ⟨⟨ol, or⟩, ⟨rfl, sl, sr⟩, ⟨b, bl, br⟩⟩ :=
  let ⟨ol', sl', bl'⟩ := valid'.dual ⟨ol, sl, bl⟩,
      ⟨or', sr', br'⟩ := valid'.dual ⟨or, sr, br⟩ in
  ⟨⟨or', ol'⟩,
   ⟨by simp [size_dual], sr', sl'⟩,
   ⟨by rw [size_dual, size_dual]; exact b.symm, br', bl'⟩⟩

theorem valid'.dual_iff {t : ordnode α} {o₁ o₂} : valid' o₁ t o₂ ↔
  @valid' (order_dual α) _ o₂ (dual t) o₁ :=
⟨valid'.dual, λ h, by have := valid'.dual h;
  rwa [dual_dual, order_dual.preorder.dual_dual] at this⟩

theorem valid.dual {t : ordnode α} : valid t →
  @valid (order_dual α) _ (dual t) := valid'.dual

theorem valid.dual_iff {t : ordnode α} : valid t ↔
  @valid (order_dual α) _ (dual t) := valid'.dual_iff

theorem valid'.left {s l x r o₁ o₂} (H : valid' o₁ (@node α s l x r) o₂) : valid' o₁ l x :=
⟨H.1.1, H.2.2.1, H.3.2.1⟩

theorem valid'.right {s l x r o₁ o₂} (H : valid' o₁ (@node α s l x r) o₂) : valid' ↑x r o₂ :=
⟨H.1.2, H.2.2.2, H.3.2.2⟩

theorem valid.left {s l x r} (H : valid (@node α s l x r)) : valid l := H.left.valid

theorem valid.right {s l x r} (H : valid (@node α s l x r)) : valid r := H.right.valid

theorem valid.size_eq {s l x r} (H : valid (@node α s l x r)) :
  size (@node α s l x r) = size l + size r + 1 := H.2.1

theorem valid'.node' {l x r o₁ o₂} (hl : valid' o₁ l ↑x) (hr : valid' ↑x r o₂)
  (H : balanced_sz (size l) (size r)) : valid' o₁ (@node' α l x r) o₂ :=
hl.node hr H rfl

theorem valid'_singleton {x : α} {o₁ o₂}
  (h₁ : bounded nil o₁ ↑x) (h₂ : bounded nil ↑x o₂) : valid' o₁ (singleton x) o₂ :=
(valid'_nil h₁).node (valid'_nil h₂) (or.inl zero_le_one) rfl

theorem valid_singleton {x : α} : valid (singleton x) := valid'_singleton ⟨⟩ ⟨⟩

theorem valid'.node3_l {l x m y r o₁ o₂}
  (hl : valid' o₁ l ↑x) (hm : valid' ↑x m ↑y) (hr : valid' ↑y r o₂)
  (H1 : balanced_sz (size l) (size m))
  (H2 : balanced_sz (size l + size m + 1) (size r)) :
  valid' o₁ (@node3_l α l x m y r) o₂ :=
(hl.node' hm H1).node' hr H2

theorem valid'.node3_r {l x m y r o₁ o₂}
  (hl : valid' o₁ l ↑x) (hm : valid' ↑x m ↑y) (hr : valid' ↑y r o₂)
  (H1 : balanced_sz (size l) (size m + size r + 1))
  (H2 : balanced_sz (size m) (size r)) :
  valid' o₁ (@node3_r α l x m y r) o₂ :=
hl.node' (hm.node' hr H2) H1

theorem valid'.node4_l {l x m y r o₁ o₂}
  (hl : valid' o₁ l ↑x) (hm : valid' ↑x m ↑y) (hr : valid' ↑y r o₂)
  (Hm : size m > 0)
  (H : (size l = 0 ∧ size m = 1 ∧ size r = 0) ∨
    (size l > 0 ∧ ratio * size r ≤ size m ∧
      delta * size l ≤ size m + size r ∧
      size m + size r ≤ delta * size l + 2 ∧
      size m ≤ delta * size r)) :
  valid' o₁ (@node4_l α l x m y r) o₂ :=
begin
  cases m with s ml z mr, {cases Hm},
  suffices : balanced_sz (size l) (size ml) ∧
    balanced_sz (size mr) (size r) ∧
    balanced_sz (size l + size ml + 1) (size mr + size r + 1),
  from (valid'.node' (hl.node' hm.left this.1) (hm.right.node' hr this.2.1) this.2.2),
  rcases H with ⟨l0, m1, r0⟩ | ⟨l0, mr₁, lr₁, lr₂, mr₂⟩,
  { rw [hm.2.size_eq, nat.succ_inj', add_eq_zero_iff] at m1,
    rw [l0, m1.1, m1.2, r0], exact dec_trivial },
  { cases nat.eq_zero_or_pos (size r) with r0 r0,
    { rw r0 at mr₂, cases not_le_of_lt Hm mr₂ },
    rw [hm.2.size_eq] at lr₁ lr₂ mr₁ mr₂,
    by_cases mm : size ml + size mr ≤ 1,
    { have r1 := le_antisymm ((mul_le_mul_left dec_trivial).1
        (le_trans mr₁ (nat.succ_le_succ mm) : _ ≤ ratio * 1)) r0,
      rw [r1, add_assoc] at lr₁,
      have l1 := le_antisymm ((mul_le_mul_left dec_trivial).1
        (le_trans lr₁ (add_le_add_right mm 2) : _ ≤ delta * 1)) l0,
      rw [l1, r1],
      cases size ml; cases size mr,
      { exact dec_trivial },
      { rw zero_add at mm, rcases mm with _|⟨_,⟨⟩⟩,
        exact dec_trivial },
      { rcases mm with _|⟨_,⟨⟩⟩, exact dec_trivial },
      { rw nat.succ_add at mm, rcases mm with _|⟨_,⟨⟩⟩ } },
    rcases hm.3.1.resolve_left mm with ⟨mm₁, mm₂⟩,
    cases nat.eq_zero_or_pos (size ml) with ml0 ml0,
    { rw [ml0, mul_zero, nat.le_zero_iff] at mm₂,
      rw [ml0, mm₂] at mm, cases mm dec_trivial },
    cases nat.eq_zero_or_pos (size mr) with mr0 mr0,
    { rw [mr0, mul_zero, nat.le_zero_iff] at mm₁,
      rw [mr0, mm₁] at mm, cases mm dec_trivial },
    have : 2 * size l ≤ size ml + size mr + 1,
    { have := nat.mul_le_mul_left _ lr₁,
      rw [mul_left_comm, mul_add] at this,
      have := le_trans this (add_le_add_left mr₁ _),
      rw [← nat.succ_mul] at this,
      exact (mul_le_mul_left dec_trivial).1 this },
    refine ⟨or.inr ⟨_, _⟩, or.inr ⟨_, _⟩, or.inr ⟨_, _⟩⟩,
    { refine (mul_le_mul_left dec_trivial).1 (le_trans this _),
      rw [two_mul, nat.succ_le_iff],
      refine add_lt_add_of_lt_of_le _ mm₂,
      simpa using (mul_lt_mul_right ml0).2 (dec_trivial:1<3) },
    { refine (add_le_add_iff_right _).1 (le_trans _ lr₂),
      rw [add_assoc, add_assoc],
      exact add_le_add_left (add_le_add mr0 (nat.le_add_right _ _)) _ },
    { exact le_trans (le_trans (nat.le_add_left _ _) (nat.le_add_right _ _)) mr₂ },
    { refine (mul_le_mul_left dec_trivial).1 (le_trans mr₁ _),
      rw [← mul_assoc, mul_comm],
      refine add_le_add (add_le_add_right _ _) mr0,
      rw mul_comm at mm₁,
      exact le_trans mm₁ (nat.mul_le_mul_left _ (dec_trivial : 3 ≤ 4)) },
    { unfold delta ratio at mr₂ mr₁ lr₁ mm₁ ⊢, linarith },
    { unfold delta ratio at lr₂ ⊢, linarith } }
end

theorem valid'.rotate_l {l x r o₁ o₂} (hl : valid' o₁ l ↑x) (hr : valid' ↑x r o₂)
  (H1 : ¬ size l + size r ≤ 1)
  (H2 : delta * size l < size r)
  (H3 : size r ≤ delta * (size l + 1)) :
  valid' o₁ (@rotate_l α l x r) o₂ :=
begin
  cases r with rs rl rx rr, {cases H2},
  rw [hr.2.size_eq, nat.lt_succ_iff] at H2,
  rw [hr.2.size_eq] at H3,
  replace H3 : size rl + size rr ≤ delta * size l + 2 :=
    nat.succ_le_succ_iff.1 H3,
  have hlp : size l > 0 → ¬ size rl + size rr ≤ 1 := λ l0 hb, absurd
    (le_trans (le_trans (nat.mul_le_mul_left _ l0) H2) hb) dec_trivial,
  rw rotate_l, split_ifs,
  { have rr0 : size rr > 0 := (mul_lt_mul_left dec_trivial).1
      (lt_of_le_of_lt (nat.zero_le _) h : ratio * 0 < _),
    suffices : balanced_sz (size l) (size rl) ∧ balanced_sz (size l + size rl + 1) (size rr),
    { exact hl.node3_l hr.left hr.right this.1 this.2 },
    cases nat.eq_zero_or_pos (size l) with l0 l0,
    { rw l0 at H3 ⊢,
      have := hr.3.1,
      cases nat.eq_zero_or_pos (size rl) with rl0 rl0,
      { rw rl0 at this ⊢,
        rw le_antisymm (balanced_sz_zero.1 this.symm) rr0,
        exact dec_trivial },
      have rr1 : size rr = 1,
      { refine le_antisymm _ rr0,
        refine nat.le_of_add_le_add_left (le_trans _ $
          nat.add_le_add_right rl0 _), exact H3 },
      rw [rr1, show size rl = 1, from le_antisymm _ rl0],
      { exact dec_trivial },
      exact nat.le_of_add_le_add_right (le_trans H3 $
        nat.add_le_add_left rr0 _) },
    rcases hr.3.1.resolve_left (hlp l0) with ⟨hb₁, hb₂⟩,
    cases nat.eq_zero_or_pos (size rl) with rl0 rl0,
    { rw rl0 at hb₂, cases not_le_of_gt rr0 hb₂ },
    cases eq_or_lt_of_le (show 1 ≤ size rr, from rr0) with rr1 rr1,
    { rw [← rr1] at h H2 ⊢,
      have : size rl = 1 := le_antisymm (nat.lt_succ_iff.1 h) rl0,
      rw this at H2,
      exact absurd (le_trans (nat.mul_le_mul_left _ l0) H2) dec_trivial },
    refine ⟨or.inr ⟨_, _⟩, or.inr ⟨_, _⟩⟩,
    { refine (mul_le_mul_left dec_trivial).1 (le_trans H2 $
        le_trans (add_le_add_left hb₂ _) _),
      rw [← mul_assoc, add_comm, ← nat.succ_mul],
      exact nat.mul_le_mul_right _ dec_trivial },
    { exact nat.le_of_add_le_add_right (le_trans H3 $
        nat.add_le_add_left rr1 _) },
    { refine le_trans (nat.add_lt_add_left h _) (_ : _ ≤ ratio.succ * size rr),
      rw [nat.succ_mul, add_comm, add_le_add_iff_left],
      refine (mul_le_mul_left dec_trivial).1
        (le_trans H2 (_ : _ ≤ ratio.succ * size rr)),
      rw [nat.succ_mul, add_le_add_iff_right],
      exact le_of_lt h },
    { exact le_trans hb₂ (nat.mul_le_mul_left _ $
        le_trans (nat.le_add_left _ _) (nat.le_add_right _ _)) } },
  { cases nat.eq_zero_or_pos (size rl) with rl0 rl0,
    { rw [rl0, not_lt, nat.le_zero_iff, nat.mul_eq_zero] at h,
      replace h := h.resolve_left dec_trivial,
      rw [rl0, h, nat.le_zero_iff, nat.mul_eq_zero] at H2,
      rw [hr.2.size_eq, rl0, h, H2.resolve_left dec_trivial] at H1,
      cases H1 dec_trivial },
    refine hl.node4_l hr.left hr.right rl0 _,
    cases nat.eq_zero_or_pos (size l) with l0 l0,
    { rw l0 at H3,
      cases nat.eq_zero_or_pos (size rr) with rr0 rr0,
      { have := hr.3.1,
        rw rr0 at this,
        exact or.inl ⟨l0, le_antisymm (balanced_sz_zero.1 this) rl0, rr0⟩ },
      exact absurd
        (le_trans (add_le_add
          (le_trans (nat.mul_le_mul_left _ rr0) (le_of_not_lt h)) rr0) H3)
        dec_trivial },
    exact or.inr ⟨l0, not_lt.1 h, H2, H3, (hr.3.1.resolve_left (hlp l0)).1⟩ }
end

theorem valid'.rotate_r {l x r o₁ o₂} (hl : valid' o₁ l ↑x) (hr : valid' ↑x r o₂)
  (H1 : ¬ size l + size r ≤ 1)
  (H2 : delta * size r < size l)
  (H3 : size l ≤ delta * (size r + 1)) :
  valid' o₁ (@rotate_r α l x r) o₂ :=
begin
  refine valid'.dual_iff.2 _,
  rw dual_rotate_r,
  refine hr.dual.rotate_l hl.dual _ _ _,
  { rwa [size_dual, size_dual, add_comm] },
  { rwa [size_dual, size_dual] },
  { rwa [size_dual, size_dual] }
end

theorem valid'.balance'_aux {l l' r r'}
  (H1 : balanced_sz l' r')
  (H2 : nat.dist (@size α l) l' ≤ 1 ∧ size r = r' ∨
        nat.dist (size r) r' ≤ 1 ∧ size l = l') :
  @size α r ≤ delta * (size l + 1) :=
begin
  rcases H2 with ⟨hl, rfl⟩ | ⟨hr, rfl⟩;
  rcases H1 with h | ⟨h₁, h₂⟩,
  { exact le_trans (nat.le_add_left _ _) (le_trans h (nat.le_add_left _ _)) },
  { exact le_trans h₂ (nat.mul_le_mul_left _ $
      le_trans (nat.dist_tri_right _ _) (nat.add_le_add_left hl _)) },
  { exact le_trans (nat.dist_tri_left' _ _)
      (le_trans (add_le_add hr (le_trans (nat.le_add_left _ _) h)) dec_trivial) },
  { rw nat.mul_succ,
    exact le_trans (nat.dist_tri_right' _ _)
      (add_le_add h₂ (le_trans hr dec_trivial)) },
end

theorem valid'.balance' {l x r o₁ o₂} (hl : valid' o₁ l ↑x) (hr : valid' ↑x r o₂)
  (H : ∃ l' r', balanced_sz l' r' ∧
    (nat.dist (size l) l' ≤ 1 ∧ size r = r' ∨
     nat.dist (size r) r' ≤ 1 ∧ size l = l')) :
  valid' o₁ (@balance' α l x r) o₂ :=
begin
  rw balance', split_ifs,
  { exact hl.node' hr (or.inl h) },
  { rcases H with ⟨l', r', H1, H2⟩,
    have := valid'.balance'_aux H1 H2,
    exact hl.rotate_l hr h h_1 this },
  { rcases H with ⟨l', r', H1, H2⟩,
    have := valid'.balance'_aux H1.symm H2.symm,
    exact hl.rotate_r hr h h_2 this },
  { exact hl.node' hr (or.inr ⟨not_lt.1 h_2, not_lt.1 h_1⟩) }
end

theorem valid'.balance_l {l x r o₁ o₂} (hl : valid' o₁ l ↑x) (hr : valid' ↑x r o₂)
  (H : (∃ l', size l = l' + 1 ∧ balanced_sz l' (size r)) ∨
       (∃ r', size r ≤ r' ∧ r' ≤ size r + 1 ∧ balanced_sz (size l) r')) :
  valid' o₁ (@balance_l α l x r) o₂ :=
begin
  rw balance_l_eq_balance' hl.3 hr.3 hl.2 hr.2 H,
  refine hl.balance' hr _,
  rcases H with ⟨l', e, H⟩ | ⟨r', e₁, e₂, H⟩,
  { refine ⟨_, _, H, or.inl ⟨_, rfl⟩⟩,
    rw [← add_zero l', e, nat.dist_add_add_left], refl },
  { refine ⟨_, _, H, or.inr ⟨_, rfl⟩⟩,
    rwa [nat.dist_eq_sub_of_le e₁, nat.sub_le_left_iff_le_add] },
end

theorem valid'.balance_r {l x r o₁ o₂} (hl : valid' o₁ l ↑x) (hr : valid' ↑x r o₂)
  (H : (∃ l', size l ≤ l' ∧ l' ≤ size l + 1 ∧ balanced_sz l' (size r)) ∨
       (∃ r', size r = r' + 1 ∧ balanced_sz (size l) r')) :
  valid' o₁ (@balance_r α l x r) o₂ :=
by rw [valid'.dual_iff, dual_balance_r]; exact
hr.dual.balance_l hl.dual (balance_sz_dual H)

theorem erase_min.valid_aux : ∀ {t o₁ o₂}, @valid' α _ o₁ t o₂ →
  valid' o₁ (erase_min t) o₂ ∧
  (size (erase_min t) ≤ size t ∧ size t ≤ size (erase_min t) + 1) ∧
  ∀ P, all P t → all P (erase_min t)
| nil _ _ h := ⟨valid'_nil h.1, dec_trivial, λ _, id⟩
| (node _ nil x r) o₁ o₂ h := ⟨h.right.trans_left h.1.1, by simp [h.2.size_eq, erase_min], λ _ h, h.2.2⟩
| (node _ l@(node _ ll lx lr) x r) _ _ h :=
  let ⟨v, ⟨s₁, s₂⟩, al⟩ := erase_min.valid_aux h.left in
  begin
    suffices H,
    rw [erase_min],
    { refine ⟨v.balance_r h.right H, _, _⟩,
      { rw [balance_r_size v.3 h.3.2.2 v.2 h.2.2.2 H, h.2.size_eq],
        refine ⟨nat.succ_le_succ (nat.add_le_add_right s₁ _), nat.succ_le_succ _⟩,
        rw add_right_comm, exact nat.add_le_add_right s₂ _ },
      { rintro P ⟨h₁, h₂, h₃⟩,
        exact (all_balance_r v.3 h.3.2.2 v.2 h.2.2.2 H).2 ⟨al _ h₁, h₂, h₃⟩ } },
    { exact or.inl ⟨_, s₁, s₂, h.3.1⟩ }
  end

theorem erase_min.valid {t} (h : @valid α _ t) : valid (erase_min t) :=
(erase_min.valid_aux h).1

theorem erase_max.valid {t} (h : @valid α _ t) : valid (erase_max t) :=
by rw [valid.dual_iff, dual_erase_max]; exact erase_min.valid h.dual

theorem split_min_eq : ∀ s l (x : α) r,
  split_min' l x r = (find_min' l x, erase_min (node s l x r))
| _ nil x r := rfl
| _ (node ls ll lx lr) x r :=
  by rw [split_min', split_min_eq, split_min', find_min', erase_min]

theorem split_max_eq : ∀ s l (x : α) r,
  split_max' l x r = (erase_max (node s l x r), find_max' x r)
| _ l x nil := rfl
| _ l x (node ls ll lx lr) :=
  by rw [split_max', split_max_eq, split_max', find_max', erase_max]

theorem insert.valid_aux' {l r r₂} (h : balanced_sz l r) (h₁ : r ≤ r₂) (h₂ : r₂ ≤ r + 1) :
  (∃ l', l ≤ l' ∧ l' ≤ l + 1 ∧ balanced_sz l' r₂) ∨
  (∃ r', r₂ = r' + 1 ∧ balanced_sz l r') :=
begin
  cases eq_or_lt_of_le h₂ with h₂ h₂,
  { exact or.inr ⟨_, h₂, h⟩ },
  { rw le_antisymm (nat.lt_succ_iff.1 h₂) h₁,
    exact or.inl ⟨_, le_refl _, nat.le_succ _, h⟩ }
end

theorem insert.valid_aux [is_total α (≤)] [@decidable_rel α (≤)] (x : α) : ∀ {t o₁ o₂},
  valid' o₁ t o₂ → bounded nil o₁ ↑x → bounded nil ↑x o₂ →
  valid' o₁ (insert x t) o₂ ∧
  (size t ≤ size (insert x t) ∧ size (insert x t) ≤ size t + 1) ∧
  ∀ P, all P t → P x → all P (insert x t)
| nil o₁ o₂ _ ol or := ⟨valid'_singleton ol or, dec_trivial, λ _ _, all_singleton.2⟩
| (node sz l y r) o₁ o₂ h ol or := begin
    rw [insert, cmp_le],
    split_ifs; rw [insert],
    { rcases h with ⟨⟨lx, xr⟩, hs, hb⟩,
      refine ⟨⟨⟨lx.mono_right h_2, xr.mono_left h_1⟩, hs, hb⟩, by simp, _⟩,
      rintro P ⟨h₁, _, h₂⟩ h₃, exact ⟨h₁, h₃, h₂⟩ },
    { rcases insert.valid_aux h.left ol (lt_of_le_not_le h_1 h_2) with ⟨vl, ⟨s₁, s₂⟩, al⟩,
      suffices H,
      refine ⟨vl.balance_l h.right H, _, _⟩,
      { rw [balance_l_size vl.3 h.3.2.2 vl.2 h.2.2.2 H, h.2.size_eq],
        refine ⟨nat.succ_le_succ (nat.add_le_add_right s₁ _), nat.succ_le_succ _⟩,
        rw add_right_comm, exact nat.add_le_add_right s₂ _ },
      { rintro P ⟨h₁, h₂, h₃⟩ h',
        refine (all_balance_l vl.3 h.3.2.2 vl.2 h.2.2.2 H).2 ⟨al _ h₁ h', h₂, h₃⟩ },
      { have := balance_sz_dual (insert.valid_aux' h.3.1.symm s₁ s₂),
        rwa [size_dual, size_dual] at this } },
    { have : y < x := lt_of_le_not_le ((total_of (≤) _ _).resolve_left h_1) h_1,
      rcases insert.valid_aux h.right this or with ⟨vr, ⟨s₁, s₂⟩, al⟩,
      suffices H,
      refine ⟨h.left.balance_r vr H, _, _⟩,
      { rw [balance_r_size h.3.2.1 vr.3 h.2.2.1 vr.2 H, h.2.size_eq],
        refine ⟨nat.succ_le_succ (nat.add_le_add_left s₁ _), nat.succ_le_succ _⟩,
        rw add_assoc, exact nat.add_le_add_left s₂ _ },
      { rintro P ⟨h₁, h₂, h₃⟩ h',
        refine (all_balance_r h.3.2.1 vr.3 h.2.2.1 vr.2 H).2 ⟨h₁, h₂, al _ h₃ h'⟩ },
      { exact insert.valid_aux' h.3.1 s₁ s₂ } },
  end

theorem insert.valid [is_total α (≤)] [@decidable_rel α (≤)]
  (x : α) {t} (h : valid t) : valid (insert x t) :=
(insert.valid_aux _ h ⟨⟩ ⟨⟩).1

-- TODO(Mario): simplify proof using forall₂
theorem insert'.valid_aux [is_total α (≤)] [@decidable_rel α (≤)] (x : α) : ∀ {t o₁ o₂},
  valid' o₁ t o₂ → bounded nil o₁ ↑x → bounded nil ↑x o₂ →
  valid' o₁ (insert' x t) o₂ ∧
  size (insert' x t) = size (insert x t) ∧
  ∀ P, all P t → P x → all P (insert' x t)
| nil o₁ o₂ _ ol or := ⟨valid'_singleton ol or, dec_trivial, λ _ _, all_singleton.2⟩
| (node sz l y r) o₁ o₂ h ol or := begin
    rw [insert, insert', cmp_le],
    split_ifs; rw [insert, insert'],
    { exact ⟨h, rfl, λ _ h _, h⟩ },
    { have := lt_of_le_not_le h_1 h_2,
      rcases insert'.valid_aux h.left ol this with ⟨vl, s, al⟩,
      suffices H,
      refine ⟨vl.balance_l h.right H, _, _⟩,
      { have := (insert.valid_aux x h.left ol this).1,
        rw [balance_l_size vl.3 h.3.2.2 vl.2 h.2.2.2 H, s,
            balance_l_size this.3 h.3.2.2 this.2 h.2.2.2 (s ▸ H)] },
      { rintro P ⟨h₁, h₂, h₃⟩ h',
        refine (all_balance_l vl.3 h.3.2.2 vl.2 h.2.2.2 H).2 ⟨al _ h₁ h', h₂, h₃⟩ },
      { cases (insert.valid_aux _ h.left ol this).2.1 with s₁ s₂,
        rw ← s at s₁ s₂,
        have := balance_sz_dual (insert.valid_aux' h.3.1.symm s₁ s₂),
        rwa [size_dual, size_dual] at this } },
    { have : y < x := lt_of_le_not_le ((total_of (≤) _ _).resolve_left h_1) h_1,
      rcases insert'.valid_aux h.right this or with ⟨vr, s, al⟩,
      suffices H,
      refine ⟨h.left.balance_r vr H, _, _⟩,
      { have := (insert.valid_aux x h.right this or).1,
        rw [balance_r_size h.3.2.1 vr.3 h.2.2.1 vr.2 H, s,
            balance_r_size h.3.2.1 this.3 h.2.2.1 this.2 (s ▸ H)] },
      { rintro P ⟨h₁, h₂, h₃⟩ h',
        refine (all_balance_r h.3.2.1 vr.3 h.2.2.1 vr.2 H).2 ⟨h₁, h₂, al _ h₃ h'⟩ },
      { cases (insert.valid_aux _ h.right this or).2.1 with s₁ s₂,
        rw ← s at s₁ s₂,
        exact insert.valid_aux' h.3.1 s₁ s₂ } }
  end

theorem insert'.valid [is_total α (≤)] [@decidable_rel α (≤)]
  (x : α) {t} (h : valid t) : valid (insert' x t) :=
(insert'.valid_aux _ h ⟨⟩ ⟨⟩).1

end

end ordnode

def ordset (α : Type*) [preorder α] := {t : ordnode α // t.valid}

namespace ordset
open ordnode
variable [preorder α]

def nil : ordset α := ⟨nil, ⟨⟩, ⟨⟩, ⟨⟩⟩

def size (s : ordset α) : ℕ := s.1.size

def singleton (x : α) : ordset α := ⟨singleton x, valid_singleton⟩

instance : has_emptyc (ordset α) := ⟨nil⟩

def empty (s : ordset α) : Prop := s = ∅

theorem empty_iff {s : ordset α} : s = ∅ ↔ s.1.empty :=
⟨λ h, by cases h; exact rfl,
 λ h, by cases s; cases s_val; [exact rfl, cases h]⟩

instance : decidable_pred (@empty α _) :=
λ s, decidable_of_iff' _ empty_iff

def insert [is_total α (≤)] [@decidable_rel α (≤)] (x : α) (s : ordset α) : ordset α :=
⟨insert x s.1, insert.valid _ s.2⟩

def insert' [is_total α (≤)] [@decidable_rel α (≤)] (x : α) (s : ordset α) : ordset α :=
⟨insert' x s.1, insert'.valid _ s.2⟩

end ordset
