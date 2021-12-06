/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.additive.salem_spencer

/-!
# Salem-Spencer sets and Roth numbers

This file defines Salem-Spencer sets, the Roth number of a set and calculates small Roth numbers.

A Salem-Spencer set is a set without arithmetic progressions of length `3`. Equivalently, the
average of any two distinct elements is not in the set.

The Roth number of a finset is the size of its biggest Salem-Spencer subset. This is a more general
definition than the one often found in mathematical litterature, where the `n`-th Roth number is
the size of the biggest Salem-Spencer subset of `{0, ..., n - 1}`.

## Main declarations

* `mul_salem_spencer`: Predicate for a set to be multiplicative Salem-Spencer.
* `add_salem_spencer`: Predicate for a set to be Salem-Spencer.
* `roth_number`: The Roth number of a finset.
* `roth_number_nat`: The Roth number of a natural. This corresponds to
  `roth_number (finset.range n)`.

## TODO

Can we calculate small Roth numbers quicker. The current algorithm to decide `roth_number_nat n ≤ m`
is `O (n.choose m * m^2)`.

## Tags

Salem-Spencer, Roth, arithmetic progression, average
-/

open list nat

variables {α β : Type*}

/-!
### Explicit values

Some lemmas and calculations of the Roth number for (very) small naturals.

Sequence [A003002](http://oeis.org/A003002) in the OEIS.
-/.

namespace bool
variables {l : list α} {p : α → bool}

lemma coe_all : (l.all p : Prop) ↔ ∀ a ∈ l, p a :=
begin
  induction l with a l ih,
  { exact iff_of_true rfl (λ a ha, ha.elim) },
  { rw [all_cons, band_coe_iff, ih],
    simp only [forall_eq_or_imp, mem_cons_iff, iff_self] }
end

lemma coe_any : (l.any p : Prop) ↔ ∃ a ∈ l, p a :=
begin
  induction l with a l ih,
  { refine iff_of_false (λ h, ff_ne_tt h) _,
    rintro ⟨a, ha, _⟩,
    exact ha.elim },
  rw [any_cons, bor_coe_iff, ih],
  split,
  { rintro (hp | ⟨b, hb, hp⟩),
    { exact ⟨a, mem_cons_self _ _, hp⟩ },
    { exact ⟨b, mem_cons_of_mem _ hb, hp⟩ } },
  { rintro ⟨b, (rfl | hb), hp⟩,
    { exact or.inl hp },
    { exact or.inr ⟨b, hb, hp⟩ } }
end

@[simp] lemma coe_tt : tt := by exact rfl
@[simp] lemma coe_ff : ¬ ff := ff_ne_tt

end bool

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
  rintro x (rfl | hx) y (rfl | hy),
  { exact h₁ _ (l.mem_cons_self _) },
  { exact rel_of_pairwise_cons h₂ hy },
  { convert rel_of_pairwise_cons h₃ hx },
  { exact ih (λ x hx, h₁ _ $ mem_cons_of_mem _ hx) (pairwise_of_pairwise_cons h₂)
    (pairwise_of_pairwise_cons h₃) _ hx _ hy }
end

end list

section explicit_values
variables {l l₁ l₂ : list ℕ} {a b n : ℕ}

/-- `three_free a l` returns whether adding `a` to `l` keeps it three-free. -/
def three_free : ℕ → list ℕ → bool
| a []       := tt
| a (b :: l) := l.all (λ c, a + c ≠ b + b) && three_free a l

/-- `roth_aux sz n d l` returns whether -/
def roth_aux : list ℕ → ℕ → ℕ → list ℕ → bool
| []        n d l := ff
| (s :: sz) n d l :=
  ((d < s) && roth_aux sz (n + 1) d l) ||
  (three_free n l && match d with
    | 0        := tt
    | (d' + 1) := roth_aux sz (n + 1) d' (n :: l)
    end)

def roth : ℕ → ℕ × list ℕ
| 0 := (0, [])
| (n + 1) := let (a, l) := roth n in (if roth_aux (a :: l) 0 a [] then a + 1 else a, a :: l)

@[simp] lemma three_free_nil : three_free n [] := by exact rfl

lemma three_free.of_cons (hl : three_free a (b :: l)) : three_free a l := bool.band_elim_right hl

lemma three_free.sublist (hl : three_free a l₂) (h : l₁ <+ l₂) : three_free a l₁ :=
begin
  induction h with l₁ l₂ b h ih l₁ l₂ b h ih,
  { exact rfl },
  { exact ih (three_free.of_cons hl) },
  { rw [three_free, band_coe_iff, bool.coe_all] at ⊢ hl,
    exact ⟨λ c hc, hl.1 _ (h.subset hc), ih hl.2⟩ }
end

lemma three_free_spec (hl : chain (>) a l) (h₁ : add_salem_spencer {n | n ∈ l}) :
  three_free a l ↔ add_salem_spencer {n | n ∈ a :: l} :=
begin
  induction l with d l ih,
  { simp only [set.set_of_eq_eq_singleton, iff_true, add_salem_spencer_singleton, mem_singleton,
      three_free_nil] },
  have : {n : ℕ | n ∈ a :: d :: l} = insert d {n : ℕ | n ∈ a :: l},
  { ext,
    simp only [set.mem_insert_iff, mem_cons_iff, set.mem_set_of_eq],
    exact or.left_comm },
  rw [this, three_free, bool.band_comm, band_coe_iff, bool.coe_all,
    ih (hl.sublist $ sublist_cons _ _) (h₁.mono $ l.subset_cons _), add_salem_spencer_insert],
  simp_rw bool.coe_to_bool,
  refine and_congr_right (λ hl', ⟨λ hs, ⟨_, _⟩, _⟩),
  { rintro b c (rfl | hb) (rfl | hc),
    { exact add_right_cancel },
    { rintro h,
      cases hl with _ _ _ _ hdb hl,
      have hcd : c < d := hl.rel hc,
      exact ((add_lt_add hcd $ hcd.trans hdb).ne' h).elim },
    { exact λ h, ((add_lt_add (rel_of_chain_cons hl : c > d) $
        hl.rel $ mem_cons_of_mem _ hb).ne h).elim },
    { exact h₁ (mem_cons_self _ _) (mem_cons_of_mem _ hb) (mem_cons_of_mem _ hc) } },
  { rintro b c (rfl | hb) (rfl | hc),
    { exact λ _, rfl },
    { exact λ h, (hs _ hc h).elim },
    { exact λ h, (hs _ hb $ (add_comm _ _).trans h).elim },
    { exact h₁ (mem_cons_of_mem _ hb) (mem_cons_of_mem _ hc) (mem_cons_self _ _) } },
  { rintro ⟨_, hs⟩ b hb h,
    have hab : a = b := hs (mem_cons_self _ _) (or.inr hb) h,
    rw hab at hl h,
    have hbd : b > d := rel_of_chain_cons hl,
    exact (add_lt_add hbd hbd).ne' h }
end

lemma roth_succ :
  roth n.succ = (if roth_aux ((roth n).1 :: (roth n).2) 0 (roth n).1 [] then (roth n).1 + 1
    else (roth n).1, (roth n).1 :: (roth n).2) :=
begin
  sorry
end

lemma roth_aux_spec (s n m d : ℕ) (l : list ℕ)
  (h₁ : add_salem_spencer {n | n ∈ l}) (h₂ : list.chain' (>) l)
  (hm : s + m = n + 1) (hd : roth_number_nat n = d + l.length) :
  ¬ roth_aux ((list.range s).map roth_number_nat) m d l ↔
  (∀ t : finset ℕ, (∀ x ∈ t, x ≤ n) → {n | n ∈ l} ⊆ t →
    add_salem_spencer (t : set ℕ) → t.card ≤ roth_number_nat n) :=
begin

end

example (n : ℕ) : roth n = (roth_number_nat n, (list.range n).reverse.map roth_number_nat) :=
begin
  suffices h : ∀ n, (roth n).1 = roth_number_nat n,
  {
    induction n with n ih,
    { refl },
    refine prod.ext (h _) _,
    rw [roth_succ, range_succ, reverse_append, reverse_singleton, singleton_append, map_cons, h n],
    convert rfl,
    refl,
    rw roth,
    change (roth n).1 :: (roth n).2 = _,
  },
end

#exit

/-- A simpler `decidable` instance for Salem-Spencer sets of naturals. We use it to prove small
values of the Roth number by `rfl`/`dec_trivial`. -/
def add_salem_spencer.decidable_nat {s : finset ℕ} : decidable (add_salem_spencer (s : set ℕ)) :=
decidable_of_iff (∀ (a ∈ s) (b ∈ s), a < b → b + (b - a) ∉ s) begin
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
  (h : ∀ s ∈ (powerset_len m (range n)).filter (λ (s : finset ℕ), add_salem_spencer (s : set ℕ)),
          ∃ z ∈ s, n ≤ z + z ∧ z + z - n ∈ s) :
  roth_number_nat (n + 1) ≤ m :=
begin
  apply nat.le_of_lt_succ,
  change roth_number_nat (n + 1) < m.succ,
  apply add_roth_number_lt_of_forall_not_add_salem_spencer,
  simp only [range_succ, powerset_len_succ_insert not_mem_range_self, mem_union, mem_image,
    or_imp_distrib, forall_and_distrib, and_imp, coe_insert, forall_exists_index,
    forall_apply_eq_imp_iff₂],
  refine ⟨_, λ s hs hsN, _⟩,
  { simp only [mem_powerset_len, and_imp],
    rw ←not_lt at hn,
    exact λ x hx₁ hx₂ h, hn (h.le_roth_number_nat _ (λ x hx, mem_range.1 (hx₁ hx)) hx₂) },
  simp only [and_imp, exists_prop, mem_filter, exists_and_distrib_left] at h,
  obtain ⟨a, hNa, ha, haN⟩ := h s hs (hsN.mono $ set.subset_insert _ _),
  rw [mem_powerset_len] at hs,
  replace hs := hs.1 haN,
  rw hsN (set.mem_insert_of_mem _ haN) (set.mem_insert _ _) (set.mem_insert_of_mem _ ha) _ at hs,
  exact not_mem_range_self hs,
  { rw [tsub_add_cancel_of_le hNa] }
end

/-- In conjunction with `dec_trivial`, this allows quick computation of small Roth numbers. -/
lemma roth_number_nat_succ_eq {m n : ℕ} (hn : roth_number_nat n = m)
  (h : ∀ s ∈ (powerset_len m (range n)).filter (λ (s : finset ℕ), add_salem_spencer (s : set ℕ)),
          ∃ z ∈ s, n ≤ z + z ∧ z + z - n ∈ s) :
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
