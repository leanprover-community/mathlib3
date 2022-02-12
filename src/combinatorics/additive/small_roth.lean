/-
Copyright (c) 2022 Mario Carneiro, Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yaël Dillies, Bhavik Mehta
-/
import combinatorics.additive.salem_spencer

/-!
# Calculation of small Roth numbers

This file implements an algorithm to calculate small Roth numbers.

The algorithm we implement is the BASIC2 algorithm from the reference.

## References

[W. Gasarch, J. Glenn, C. Kruskal, *Finding Large 3-free sets I: The Small `n` Case]
(https://www.cs.umd.edu/~gasarch/papers/3apI.pdf)

## Tags

Roth, arithmetic progression, average, three-free, algorithm
-/

open list nat

variables {α β : Type*}

/-!
### Explicit values

Some lemmas and calculations of the Roth number for (very) small naturals.

Sequence [A003002](http://oeis.org/A003002) in the OEIS.
-/

lemma transitive_gt [preorder α] : transitive (@gt α _) := @gt_trans _ _

namespace list

variables {R : α → α → Prop} {l l₁ l₂ : list α} {a b : α}

lemma chain.sublist [is_trans α R] (hl : l₂.chain R a) (h : l₁ <+ l₂) : l₁.chain R a :=
begin
  have hR : transitive R := λ a b c, trans,
  rw chain_iff_pairwise hR at ⊢ hl,
  exact pairwise_of_sublist (h.cons_cons a) hl,
end

lemma chain.rel [is_trans α R] (hl : l.chain R a) (hb : b ∈ l) : R a b :=
begin
  have hR : transitive R := λ a b c, trans,
  rw chain_iff_pairwise hR at hl,
  exact rel_of_pairwise_cons hl hb,
end

lemma chain'.sublist [is_trans α R] (hl : l₂.chain' R) (h : l₁ <+ l₂) : l₁.chain' R :=
begin
  have hR : transitive R := λ a b c, trans,
  rw chain'_iff_pairwise hR at ⊢ hl,
  exact pairwise_of_sublist h hl,
end

lemma pairwise.forall_of_forall_of_flip (h₁ : ∀ x ∈ l, R x x) (h₂ : l.pairwise R)
  (h₃ : l.pairwise (flip R)) :
  ∀ (x ∈ l) (y ∈ l), R x y :=
begin
  induction l with a l ih,
  { exact λ x hx, hx.elim },
  rw pairwise_cons at h₂ h₃,
  rintro x (rfl | hx) y (rfl | hy),
  { exact h₁ _ (l.mem_cons_self _) },
  { exact h₂.1 _ hy },
  { exact h₃.1 _ hx },
  { exact ih (λ x hx, h₁ _ $ mem_cons_of_mem _ hx) h₂.2 h₃.2 _ hx _ hy }
end

end list

example {a m d : ℕ} (s : finset ℕ)
  (h₁ : roth_number_nat a ≤ d)
  (hs₁ : ∀ (x : ℕ), x ∈ s → x < a + m)
  (hs₃ : add_salem_spencer (s : set ℕ)) :
  (finset.filter (not ∘ (< m)) s).card ≤ d :=
begin
  refine le_trans _ h₁,
  have : finset.filter (not ∘ (< m)) s ⊆ finset.Ico m (a + m),
  { rintro x hx,
    rw finset.mem_filter at hx,
    exact finset.mem_Ico.2 ⟨not_lt.1 hx.2, hs₁ _ hx.1⟩ },
  rw [←add_tsub_cancel_right a m, ←add_roth_number_Ico],
  exact (hs₃.mono $ finset.filter_subset _ _).le_add_roth_number this,
end

section explicit_values
variables {l l₁ l₂ : list ℕ} {a b d m n : ℕ}

/-- `three_free a l` returns whether adding `a` to `l` keeps it three-free. -/
def three_free : ℕ → list ℕ → bool
| a []       := tt
| a (b :: l) := l.all (λ c, a + c ≠ b + b) && three_free a l

@[simp] lemma three_free_nil : three_free n [] := by exact rfl

lemma three_free.of_cons (hl : three_free a (b :: l)) : three_free a l := bool.band_elim_right hl

lemma three_free_iff_pairwise : three_free a l ↔ l.pairwise (λ b c, a + c ≠ b + b) :=
by induction l; simp [three_free, *, all_iff_forall]

lemma three_free.sublist (hl : three_free a l₂) (h : l₁ <+ l₂) : three_free a l₁ :=
begin
  rw three_free_iff_pairwise at hl ⊢,
  apply pairwise_of_sublist h hl,
end

lemma three_free_spec (hl : chain (>) a l) (h₁ : add_salem_spencer {n | n ∈ l}) :
  three_free a l ↔ add_salem_spencer {n | n ∈ a :: l} :=
begin
  rw three_free_iff_pairwise,
  have : {n : ℕ | n ∈ a :: l} = insert a {n : ℕ | n ∈ l},
  { ext, simp only [set.mem_insert_iff, mem_cons_iff, set.mem_set_of_eq] },
  rw [this, add_salem_spencer_insert],
  refine ⟨λ H, ⟨h₁, λ b c hb hc e, _, λ b c hb hc e, _⟩, λ H, _⟩,
  { cases H.forall_of_forall_of_flip _ _ _ hc _ hb e,
    { exact λ b hb, (add_lt_add_right (hl.rel hb) _).ne' },
    refine (pairwise_of_pairwise_cons ((chain_iff_pairwise transitive_gt).1 hl)).imp_of_mem _,
    exact λ b c hb hc h, (add_lt_add (hl.rel hc) h).ne' },
  { cases (add_lt_add (hl.rel hb) (hl.rel hc)).ne e },
  { exact pairwise.imp_mem.2 (pairwise_of_forall $ λ c b hc hb e,
    (H.2.1 hb hc e).not_gt $ hl.rel hb) }
end

def roth_aux (a m d : ℕ) (l : list ℕ) : Prop :=
add_salem_spencer {n | n ∈ l} → list.chain (>) m l →
  ∀ s : finset ℕ, (∀ x ∈ s, x < a + m) → s.filter (< m) = list.to_finset l →
    add_salem_spencer (s : set ℕ) → s.card ≤ d + l.length

def roth_aux₁ (a m d : ℕ) (l : list ℕ) : Prop :=
roth_number_nat a ≤ d ∨ roth_aux a (m + 1) d l

def roth_aux₂ (a m d : ℕ) (l : list ℕ) : Prop :=
¬ three_free m l ∨ ∃ d', d = d' + 1 ∧ roth_aux a (m + 1) d' (m :: l)

lemma roth_aux_zero (m d : ℕ) (l : list ℕ) : roth_aux 0 m d l :=
begin
  intros h hl s hs₀ hs₁ _,
  rw zero_add at hs₀,
  rw finset.filter_true_of_mem hs₀ at hs₁,
  rw [hs₁, card_to_finset, erase_dup_eq_self.2],
  { exact le_add_self },
  { exact (pairwise_of_pairwise_cons $ (chain_iff_pairwise transitive_gt).1 hl).nodup }
end

lemma roth_aux_succ (h₁ : roth_aux₁ a m d l) (h₂ : roth_aux₂ a m d l) : roth_aux (a + 1) m d l :=
begin
  intros hl₁ hl₂ s hs₁ hs₂ hs₃,
  have hl₃ := (pairwise_of_pairwise_cons $ (chain_iff_pairwise transitive_gt).1 hl₂).nodup,
  rw [←finset.filter_card_add_filter_neg_card_eq_card (< m), hs₂, add_comm, card_to_finset,
    erase_dup_eq_self.2 hl₃, add_le_add_iff_right],
  sorry
end

lemma roth_aux₁_left (h : roth_number_nat a ≤ d) : roth_aux₁ a m d l := or.inl h
lemma roth_aux₁_right (h : roth_aux a (m + 1) d l) : roth_aux₁ a m d l := or.inr h

lemma roth_aux₂_left (h : three_free m l = ff) : roth_aux₂ a m d l := or.inl $ bool_iff_false.2 h

lemma roth_aux₂_right (h : roth_aux a (m + 1) d (m :: l)) : roth_aux₂ a m (d + 1) l :=
or.inr ⟨_, rfl, h⟩

lemma roth_aux_out (h : roth_aux n 0 d []) : roth_number_nat n ≤ d :=
begin
  rw roth_aux at h,
  simp only [add_zero, to_finset_nil, set.set_of_false, add_salem_spencer_empty, not_mem_nil,
    finset.filter_false, eq_self_iff_true, length, forall_true_left, chain.nil, not_lt_zero'] at h,
  obtain ⟨s, hs₀, hs₁, hs₂⟩ := add_roth_number_spec (finset.range n),
  convert h s _ hs₂,
  { exact hs₁.symm },
  { exact λ x hx, finset.mem_range.1 (hs₀ hx) }
end

example : roth_number_nat 3 ≤ 2 → roth_number_nat 4 ≤ 3 → roth_number_nat 8 ≤ 4 :=
begin
  intros h₃ h₄,
  apply roth_aux_out,
  apply roth_aux_succ,
  { apply roth_aux₁_right,
    apply roth_aux_succ,
    { apply roth_aux₁_right,
      apply roth_aux_succ,
      { apply roth_aux₁_right,
        apply roth_aux_succ,
        { apply roth_aux₁_left,
          apply roth_number_nat_le },
        apply roth_aux₂_right,
        apply roth_aux_succ,
        { apply roth_aux₁_left,
          apply roth_number_nat_le },
        apply roth_aux₂_right,
        apply roth_aux_succ,
        { apply roth_aux₁_left,
          apply roth_number_nat_le },
        apply roth_aux₂_left,
        dec_trivial },
    apply roth_aux₂_right,
    apply roth_aux_succ,
    { apply roth_aux₁_left h₄ },
    { apply roth_aux₂_right,
      apply roth_aux_succ,
      { apply roth_aux₁_left,
        apply h₃ },
      apply roth_aux₂_left,
      dec_trivial } },
    apply roth_aux₂_right,
    apply roth_aux_succ,
    { apply roth_aux₁_right,
      apply roth_aux_succ,
      { apply roth_aux₁_right,
        apply roth_aux_succ,
        { apply roth_aux₁_left,
          apply roth_number_nat_le },
        apply roth_aux₂_right,
        apply roth_aux_succ,
        { apply roth_aux₁_left,
          apply roth_number_nat_le },
        apply roth_aux₂_right,
        apply roth_aux_succ,
        { apply roth_aux₁_left,
          apply roth_number_nat_le },
        apply roth_aux₂_left,
        dec_trivial },
      apply roth_aux₂_right,
      apply roth_aux_succ,
      { apply roth_aux₁_left,
        apply h₃ },
      apply roth_aux₂_right,
      apply roth_aux_succ,
      { apply roth_aux₁_right,
        apply roth_aux_succ,
        { apply roth_aux₁_left,
          apply roth_number_nat_le },
        apply roth_aux₂_right,
        apply roth_aux_succ,
        { apply roth_aux₁_right,
          apply roth_aux_zero },
        apply roth_aux₂_left,
        dec_trivial },
      apply roth_aux₂_left,
      dec_trivial },
    apply roth_aux₂_right,
    apply roth_aux_succ,
    { apply roth_aux₁_right,
      apply roth_aux_succ,
      { apply roth_aux₁_left,
        apply h₃ },
      apply roth_aux₂_right,
      apply roth_aux_succ,
      { apply roth_aux₁_right,
        apply roth_aux_succ,
        { apply roth_aux₁_left,
          apply roth_number_nat_le },
        apply roth_aux₂_left,
        dec_trivial },
      apply roth_aux₂_right,
      apply roth_aux_succ,
      { apply roth_aux₁_right,
        apply roth_aux_succ,
        { apply roth_aux₁_right,
          apply roth_aux_zero },
        apply roth_aux₂_left,
        dec_trivial },
      apply roth_aux₂_left,
      dec_trivial },
    apply roth_aux₂_left,
    dec_trivial },
  apply roth_aux₂_right,
  apply roth_aux_succ,
  { apply roth_aux₁_right,
    apply roth_aux_succ,
    { apply roth_aux₁_right,
      apply roth_aux_succ,
      { apply roth_aux₁_left,
        apply h₄ },
      apply roth_aux₂_right,
      apply roth_aux_succ,
      { apply roth_aux₁_left h₃ },
      apply roth_aux₂_right,
      apply roth_aux_succ,
      { apply roth_aux₁_right,
        apply roth_aux_succ,
        { apply roth_aux₁_left,
          apply roth_number_nat_le },
        apply roth_aux₂_left,
        dec_trivial },
      apply roth_aux₂_left,
      dec_trivial },
    apply roth_aux₂_right,
    apply roth_aux_succ,
    { apply roth_aux₁_right,
      apply roth_aux_succ,
      { apply roth_aux₁_left,
        apply h₃ },
      apply roth_aux₂_left,
      dec_trivial },
    apply roth_aux₂_right,
    apply roth_aux_succ,
    { apply roth_aux₁_right,
      apply roth_aux_succ,
      { apply roth_aux₁_right,
        apply roth_aux_succ,
        { apply roth_aux₁_left,
          apply roth_number_nat_le },
        apply roth_aux₂_left,
        dec_trivial },
      apply roth_aux₂_right,
      apply roth_aux_succ,
      { apply roth_aux₁_right,
        apply roth_aux_succ,
        { apply roth_aux₁_right,
          apply roth_aux_zero },
        apply roth_aux₂_left,
        dec_trivial },
      apply roth_aux₂_left,
      dec_trivial },
    apply roth_aux₂_left,
    dec_trivial },
  apply roth_aux₂_right,
  apply roth_aux_succ,
  { apply roth_aux₁_right,
    apply roth_aux_succ,
    { apply roth_aux₁_right,
      apply roth_aux_succ,
      { apply roth_aux₁_left,
        apply h₃ },
      apply roth_aux₂_right,
      apply roth_aux_succ,
      { apply roth_aux₁_right,
        apply roth_aux_succ,
        { apply roth_aux₁_left,
          apply roth_number_nat_le },
        apply roth_aux₂_right,
        apply roth_aux_succ,
        { apply roth_aux₁_right,
          apply roth_aux_zero },
        apply roth_aux₂_left,
        dec_trivial },
      apply roth_aux₂_right,
      apply roth_aux_succ,
      { apply roth_aux₁_right,
        apply roth_aux_succ,
        { apply roth_aux₁_right,
          apply roth_aux_zero },
        apply roth_aux₂_left,
        dec_trivial },
      apply roth_aux₂_left,
      dec_trivial },
    apply roth_aux₂_right,
    apply roth_aux_succ,
    { apply roth_aux₁_right,
      apply roth_aux_succ,
      { apply roth_aux₁_right,
        apply roth_aux_succ,
        { apply roth_aux₁_left,
          apply roth_number_nat_le },
        apply roth_aux₂_left,
        dec_trivial },
      apply roth_aux₂_left,
      dec_trivial },
    apply roth_aux₂_right,
    apply roth_aux_succ,
    { apply roth_aux₁_right,
      apply roth_aux_succ,
      { apply roth_aux₁_right,
        apply roth_aux_succ,
        { apply roth_aux₁_right,
          apply roth_aux_zero },
        apply roth_aux₂_left,
        dec_trivial },
      apply roth_aux₂_left,
      dec_trivial },
    apply roth_aux₂_left,
    dec_trivial },
  apply roth_aux₂_left,
  dec_trivial
end

meta def tactic.roth_auto_step : tactic unit :=
do t ← tactic.target,
   match t with
   | `(roth_aux 0 _ _ _) := `[refine roth_aux_zero _ _ _]
   | `(roth_aux _ _ _ _) := tactic.refine ``(roth_aux_succ _ _)
   | _ := tactic.fail "no"
   end

meta def tactic.interactive.roth_start : tactic unit :=
`[refine roth_aux_out _] >> tactic.roth_auto_step

meta def tactic.interactive.roth_left : tactic unit :=
do t ← tactic.target,
  match t with
  | `(roth_aux₁ _ _ _ _) := `[refine roth_aux₁_left _]
  | `(roth_aux₂ _ _ _ _) :=
      `[exact roth_aux₂_left dec_trivial] <|> tactic.trace "Try this: roth_right"
  | _ := tactic.fail "goal isn't a roth proof"
  end

meta def tactic.interactive.roth_right : tactic unit :=
do t ← tactic.target,
  match t with
  | `(roth_aux₁ _ _ _ _) := `[refine roth_aux₁_right _] >> tactic.roth_auto_step
  | `(roth_aux₂ _ _ _ _) := `[refine roth_aux₂_right _] >> tactic.roth_auto_step
  | _ := tactic.fail "goal isn't a roth proof"
  end

example : roth_number_nat 3 ≤ 2 → roth_number_nat 4 ≤ 3 → roth_number_nat 8 ≤ 4 →
  roth_number_nat 10 ≤ 5 :=
begin
  intros h₃ h₄ h₈,
  roth_start,
  { roth_right,
    { roth_left,
      sorry },
    roth_right,
    { roth_left,
      sorry },
    roth_right,
    { roth_right,
      { roth_right,
        { roth_left,
          sorry },
        roth_right,
        { roth_left,
          sorry },
        roth_right,
        { roth_right,
          { roth_left,
            sorry },
          roth_left },
        roth_left },
      roth_right,
      { roth_right,
        { roth_left,
          sorry },
        { roth_left } },
      roth_right,
      { roth_right,
        { roth_right,
          { roth_left,
            sorry },
          roth_left },
        roth_left },
      roth_left },
    roth_left },
  roth_right,
  { roth_left,
    sorry },
  roth_right,
  { roth_right,
    { roth_right,
      { roth_right,
        { roth_left,
          sorry },
        roth_right,
        { roth_left,
          sorry },
        roth_right,
        { roth_right,
          { roth_left,
            sorry },
          roth_right,
          { roth_right },
          roth_left },
        roth_left },
      roth_right,
      { roth_right,
        { roth_left,
          sorry },
        roth_right,
        { roth_right,
          { roth_left,
            sorry },
          roth_left },
        roth_left },
      roth_right,
      { roth_right,
        { roth_right,
          { roth_left,
            sorry },
          roth_left },
        roth_left },
      roth_left },
    roth_right,
    { roth_right,
      { roth_right,
        { roth_left,
          sorry },
        roth_left },
      roth_left },
    roth_right,
    { roth_right,
      { roth_right,
        { roth_right,
          { roth_left,
            sorry },
          roth_left },
        roth_left },
      roth_left },
    roth_left },
  roth_left,
end

#exit

/-! ### Second attempt -/

/-- `old_roth_aux sz n d l` returns whether -/
def old_roth_aux : list ℕ → ℕ → ℕ → list ℕ → bool
| []        n d l := ff
| (a :: sz) n d l :=
  ((d < a) && old_roth_aux sz (n + 1) d l) ||
  (three_free n l && match d with
    | 0        := tt
    | (d' + 1) := old_roth_aux sz (n + 1) d' (n :: l)
    end)

def roth : ℕ → ℕ × list ℕ
| 0 := (0, [])
| (n + 1) := let (a, l) := roth n in (if old_roth_aux (a :: l) 0 a [] then a + 1 else a, a :: l)

-- lemma roth_succ :
--   roth n.succ = (if old_roth_aux ((roth n).1 :: (roth n).2) 0 (roth n).1 [] then (roth n).1 + 1
--     else (roth n).1, (roth n).1 :: (roth n).2) :=
-- begin
--   sorry
-- end

-- lemma old_roth_aux_spec (a n m d : ℕ) (l : list ℕ)
--   (h₁ : add_salem_spencer {n | n ∈ l}) (h₂ : list.chain' (>) l)
--   (hm : a + m = n + 1) (hd : roth_number_nat n = d + l.length) :
--   ¬ old_roth_aux ((list.range a).map roth_number_nat) m d l ↔
--   (∀ t : finset ℕ, (∀ x ∈ t, x ≤ n) → {n | n ∈ l} ⊆ t →
--     add_salem_spencer (t : set ℕ) → t.card ≤ roth_number_nat n) :=
-- begin

-- end

example (n : ℕ) : roth n = (roth_number_nat n, (list.range n).reverse.map roth_number_nat) :=
begin
  suffices h : ∀ n, (roth n).1 = roth_number_nat n,
  {
    induction n with n ih,
    { refl },
    refine prod.ext (h _) _,
    rw [roth_succ, range_succ, reverse_append, reverse_singleton, singleton_append, map_cons,
      h n],
    convert rfl,
    refl,
    rw roth,
    change (roth n).1 :: (roth n).2 = _,
  },
end

/-! ### First attempt -/

/-- A simpler `decidable` instance for Salem-Spencer sets of naturals. We use it to prove small
values of the Roth number by `rfl`/`dec_trivial`. -/
def add_salem_spencer.decidable_nat {a : finset ℕ} : decidable (add_salem_spencer (a : set ℕ)) :=
decidable_of_iff (∀ (a ∈ a) (b ∈ a), a < b → b + (b - a) ∉ a) begin
  rw add_salem_spencer_iff_eq_right,
  refine ⟨λ hs a b c ha hb hc habc, _, λ hs a ha b hb hab h, _⟩,
  { by_contra h,
    obtain hac | hac := lt_or_gt_of_ne h,
    { refine hs _ ha _ hc hac _,
      rwa [←add_tsub_assoc_of_le hac.le, ←habc, add_tsub_cancel_left] },
    { have hbc : b < c := lt_of_not_ge' (λ h, (add_lt_add_of_lt_of_le hac h).ne' habc),
      refine hs _ hb _ hc hbc _,
      rwa [←add_tsub_assoc_of_le hbc.le, ←habc, add_tsub_cancel_right] } },
  { refine hab.ne (hs ha h hb _),
    rw [←add_tsub_assoc_of_le hab.le, add_tsub_cancel_of_le (le_add_left hab.le)] }
end

local attribute [instance] add_salem_spencer.decidable_nat

lemma roth_number_nat_succ_le {m n : ℕ} (hn : roth_number_nat n ≤ m)
  (h : ∀ a ∈ (powerset_len m (range n)).filter (λ (a : finset ℕ), add_salem_spencer (a : set ℕ)),
          ∃ z ∈ a, n ≤ z + z ∧ z + z - n ∈ a) :
  roth_number_nat (n + 1) ≤ m :=
begin
  apply nat.le_of_lt_succ,
  change roth_number_nat (n + 1) < m.succ,
  apply add_roth_number_lt_of_forall_not_add_salem_spencer,
  simp only [range_succ, powerset_len_succ_insert not_mem_range_self, mem_union, mem_image,
    or_imp_distrib, forall_and_distrib, and_imp, coe_insert, forall_exists_index,
    forall_apply_eq_imp_iff₂],
  refine ⟨_, λ a hs hsN, _⟩,
  { simp only [mem_powerset_len, and_imp],
    rw ←not_lt at hn,
    exact λ x hx₁ hx₂ h, hn (h.le_roth_number_nat _ (λ x hx, mem_range.1 (hx₁ hx)) hx₂) },
  simp only [and_imp, exists_prop, mem_filter, exists_and_distrib_left] at h,
  obtain ⟨a, hNa, ha, haN⟩ := h a hs (hsN.mono $ set.subset_insert _ _),
  rw [mem_powerset_len] at hs,
  replace hs := hs.1 haN,
  rw hsN (set.mem_insert_of_mem _ haN) (set.mem_insert _ _) (set.mem_insert_of_mem _ ha) _ at hs,
  exact not_mem_range_self hs,
  { rw [tsub_add_cancel_of_le hNa] }
end

/-- In conjunction with `dec_trivial`, this allows quick computation of small Roth numbers. -/
lemma roth_number_nat_succ_eq {m n : ℕ} (hn : roth_number_nat n = m)
  (h : ∀ a ∈ (powerset_len m (range n)).filter (λ (a : finset ℕ), add_salem_spencer (a : set ℕ)),
          ∃ z ∈ a, n ≤ z + z ∧ z + z - n ∈ a) :
  roth_number_nat (n + 1) = m :=
(roth_number_nat_succ_le hn.le h).antisymm $ hn.ge.trans $ roth_number_nat.mono n.le_succ

@[simp] lemma roth_number_nat_zero : roth_number_nat 0 = 0 := rfl
@[simp] lemma roth_number_nat_one : roth_number_nat 1 = 1 := rfl
@[simp] lemma roth_number_nat_two : roth_number_nat 2 = 2 := rfl
@[simp] lemma roth_number_nat_three : roth_number_nat 3 = 2 := rfl
@[simp] lemma roth_number_nat_four : roth_number_nat 4 = 3 := rfl
@[simp] lemma roth_number_nat_five : roth_number_nat 5 = 4 := rfl
@[simp] lemma roth_number_nat_six : roth_number_nat 6 = 4 := rfl
@[simp] lemma roth_number_nat_seven : roth_number_nat 7 = 4 := rfl
@[simp] lemma roth_number_nat_eight : roth_number_nat 8 = 4 := rfl
@[simp] lemma roth_number_nat_nine : roth_number_nat 9 = 5 := rfl
@[simp] lemma roth_number_nat_ten : roth_number_nat 10 = 5 := dec_trivial
@[simp] lemma roth_number_nat_eleven : roth_number_nat 11 = 6 :=
begin
  apply le_antisymm,
  { simpa using roth_number_nat_add_le 3 8 },
  apply add_salem_spencer.le_roth_number_nat {0, 1, 3, 7, 8, 10},
  { dec_trivial },
  { simp },
  { simp }
end

@[simp] lemma roth_number_twelve : roth_number_nat 12 = 6 :=
roth_number_nat_succ_eq roth_number_nat_eleven $ by dec_trivial

@[simp] lemma roth_number_nat_thirteen : roth_number_nat 13 = 7 :=
begin
  apply le_antisymm,
  { simpa using roth_number_nat_add_le 10 3 },
  apply add_salem_spencer.le_roth_number_nat {0, 1, 3, 4, 9, 10, 12},
  { dec_trivial },
  { simp },
  { simp }
end

@[simp] lemma roth_number_nat_fourteen : roth_number_nat 14 = 8 :=
begin
  apply le_antisymm,
  { simpa using roth_number_nat_add_le 11 3 },
  apply add_salem_spencer.le_roth_number_nat {0, 1, 3, 4, 9, 10, 12, 13}, -- unique example
  { dec_trivial },
  { simp },
  { simp }
end

end explicit_values
