/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.perm.sign group_theory.order_of_element

namespace equiv.perm
open equiv function finset
variables {α : Type*} {β : Type*} [decidable_eq α]

def is_cycle (f : perm β) := ∃ x, f x ≠ x ∧ ∀ y, f y ≠ y → ∃ i : ℤ, (f ^ i) x = y

lemma is_cycle_swap {x y : α} (hxy : x ≠ y) : is_cycle (swap x y) :=
⟨y, by rwa swap_apply_right,
  λ a (ha : ite (a = x) y (ite (a = y) x a) ≠ a),
    if hya : y = a then ⟨0, hya⟩
    else ⟨1, by rw [gpow_one, swap_apply_def]; split_ifs at *; cc⟩⟩

lemma is_cycle_inv {f : perm β} (hf : is_cycle f) : is_cycle (f⁻¹) :=
let ⟨x, hx⟩ := hf in
⟨x, by simp [eq_inv_iff_eq, inv_eq_iff_eq, *] at *; cc,
  λ y hy, let ⟨i, hi⟩ := hx.2 y (by simp [eq_inv_iff_eq, inv_eq_iff_eq, *] at *; cc) in
    ⟨-i, by rwa [gpow_neg, inv_gpow, inv_inv]⟩⟩

lemma exists_gpow_eq_of_is_cycle {f : perm β} (hf : is_cycle f) {x y : β}
  (hx : f x ≠ x) (hy : f y ≠ y) : ∃ i : ℤ, (f ^ i) x = y :=
let ⟨g, hg⟩ := hf in
let ⟨a, ha⟩ := hg.2 x hx in
let ⟨b, hb⟩ := hg.2 y hy in
⟨b - a, by rw [← ha, ← mul_apply, ← gpow_add, sub_add_cancel, hb]⟩

lemma is_cycle_swap_mul_aux₁ : ∀ (n : ℕ) {b x : α} {f : perm α}
  (hb : (swap x (f x) * f) b ≠ b) (h : (f ^ n) (f x) = b),
  ∃ i : ℤ, ((swap x (f x) * f) ^ i) (f x) = b
| 0         := λ b x f hb h, ⟨0, h⟩
| (n+1 : ℕ) := λ b x f hb h,
  if hfbx : f x = b then ⟨0, hfbx⟩
  else
    have f b ≠ b ∧ b ≠ x, from ne_and_ne_of_swap_mul_apply_ne_self hb,
    have hb' : (swap x (f x) * f) (f⁻¹ b) ≠ f⁻¹ b,
      by rw [mul_apply, apply_inv_self, swap_apply_of_ne_of_ne this.2 (ne.symm hfbx),
          ne.def, ← injective.eq_iff f.bijective.1, apply_inv_self];
        exact this.1,
    let ⟨i, hi⟩ := is_cycle_swap_mul_aux₁ n hb'
      (f.bijective.1 $
        by rw [apply_inv_self];
        rwa [pow_succ, mul_apply] at h) in
    ⟨i + 1, by rw [add_comm, gpow_add, mul_apply, hi, gpow_one, mul_apply, apply_inv_self,
        swap_apply_of_ne_of_ne (ne_and_ne_of_swap_mul_apply_ne_self hb).2 (ne.symm hfbx)]⟩

lemma is_cycle_swap_mul_aux₂ : ∀ (n : ℤ) {b x : α} {f : perm α}
  (hb : (swap x (f x) * f) b ≠ b) (h : (f ^ n) (f x) = b),
  ∃ i : ℤ, ((swap x (f x) * f) ^ i) (f x) = b
| (n : ℕ) := λ b x f, is_cycle_swap_mul_aux₁ n
| -[1+ n] := λ b x f hb h,
  if hfbx : f⁻¹ x = b then ⟨-1, by rwa [gpow_neg, gpow_one, mul_inv_rev, mul_apply, swap_inv, swap_apply_right]⟩
  else if hfbx' : f x = b then ⟨0, hfbx'⟩
  else
  have f b ≠ b ∧ b ≠ x := ne_and_ne_of_swap_mul_apply_ne_self hb,
  have hb : (swap x (f⁻¹ x) * f⁻¹) (f⁻¹ b) ≠ f⁻¹ b,
    by rw [mul_apply, swap_apply_def];
      split_ifs;
      simp [inv_eq_iff_eq, eq_inv_iff_eq] at *; cc,
  let ⟨i, hi⟩ := is_cycle_swap_mul_aux₁ n hb
    (show (f⁻¹ ^ n) (f⁻¹ x) = f⁻¹ b, by
      rw [← gpow_coe_nat, ← h, ← mul_apply, ← mul_apply, ← mul_apply, gpow_neg_succ, ← inv_pow, pow_succ', mul_assoc,
        mul_assoc, inv_mul_self, mul_one, gpow_coe_nat, ← pow_succ', ← pow_succ]) in
  have h : (swap x (f⁻¹ x) * f⁻¹) (f x) = f⁻¹ x, by rw [mul_apply, inv_apply_self, swap_apply_left],
  ⟨-i, by rw [← add_sub_cancel i 1, neg_sub, sub_eq_add_neg, gpow_add, gpow_one, gpow_neg, ← inv_gpow,
      mul_inv_rev, swap_inv, mul_swap_eq_swap_mul, inv_apply_self, swap_comm _ x, gpow_add, gpow_one,
      mul_apply, mul_apply (_ ^ i), h, hi, mul_apply, apply_inv_self, swap_apply_of_ne_of_ne this.2 (ne.symm hfbx')]⟩

lemma eq_swap_of_is_cycle_of_apply_apply_eq_self {f : perm α} (hf : is_cycle f) {x : α}
  (hfx : f x ≠ x) (hffx : f (f x) = x) : f = swap x (f x) :=
equiv.ext _ _ $ λ y,
let ⟨z, hz⟩ := hf in
let ⟨i, hi⟩ := hz.2 x hfx in
if hyx : y = x then by simp [hyx]
else if hfyx : y = f x then by simp [hfyx, hffx]
else begin
  rw [swap_apply_of_ne_of_ne hyx hfyx],
  refine by_contradiction (λ hy, _),
  cases hz.2 y hy with j hj,
  rw [← sub_add_cancel j i, gpow_add, mul_apply, hi] at hj,
  cases gpow_apply_eq_of_apply_apply_eq_self hffx (j - i) with hji hji,
  { rw [← hj, hji] at hyx, cc },
  { rw [← hj, hji] at hfyx, cc }
end

lemma is_cycle_swap_mul {f : perm α} (hf : is_cycle f) {x : α}
  (hx : f x ≠ x) (hffx : f (f x) ≠ x) : is_cycle (swap x (f x) * f) :=
⟨f x, by simp only [swap_apply_def, mul_apply];
        split_ifs; simp [injective.eq_iff f.bijective.1] at *; cc,
  λ y hy,
  let ⟨i, hi⟩ := exists_gpow_eq_of_is_cycle hf hx (ne_and_ne_of_swap_mul_apply_ne_self hy).1 in
  have hi : (f ^ (i - 1)) (f x) = y, from
    calc (f ^ (i - 1)) (f x) = (f ^ (i - 1) * f ^ (1 : ℤ)) x : by rw [gpow_one, mul_apply]
    ... =  y : by rwa [← gpow_add, sub_add_cancel],
  is_cycle_swap_mul_aux₂ (i - 1) hy hi⟩

@[simp] lemma support_swap [fintype α] {x y : α} (hxy : x ≠ y) : (swap x y).support = {x, y} :=
finset.ext.2 $ λ a, by simp [swap_apply_def]; split_ifs; cc

lemma card_support_swap [fintype α] {x y : α} (hxy : x ≠ y) : (swap x y).support.card = 2 :=
show (swap x y).support.card = finset.card ⟨x::y::0, by simp [hxy]⟩,
from congr_arg card $ by rw [support_swap hxy]; simp [*, finset.ext]; cc

lemma sign_cycle [fintype α] : ∀ {f : perm α} (hf : is_cycle f),
  sign f = -(-1 ^ f.support.card)
| f := λ hf,
let ⟨x, hx⟩ := hf in
calc sign f = sign (swap x (f x) * (swap x (f x) * f)) :
  by rw [← mul_assoc, mul_def, mul_def, swap_swap, trans_refl]
... = -(-1 ^ f.support.card) :
  if h1 : f (f x) = x
  then
    have h : swap x (f x) * f = 1,
      by conv in (f) {rw eq_swap_of_is_cycle_of_apply_apply_eq_self hf hx.1 h1 };
        simp [mul_def, one_def],
    by rw [sign_mul, sign_swap hx.1.symm, h, sign_one, eq_swap_of_is_cycle_of_apply_apply_eq_self hf hx.1 h1,
        card_support_swap hx.1.symm]; refl
  else
    have h : card (support (swap x (f x) * f)) + 1 = card (support f),
      by rw [← insert_erase (mem_support.2 hx.1), support_swap_mul_eq h1,
        card_insert_of_not_mem (not_mem_erase _ _)],
    have wf : card (support (swap x (f x) * f)) < card (support f),
      from card_support_swap_mul hx.1,
    by rw [sign_mul, sign_swap hx.1.symm, sign_cycle (is_cycle_swap_mul hf hx.1 h1), ← h];
      simp [pow_add]
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ f, f.support.card)⟩]}

def same_cycle (f : perm β) (x y : β) := ∃ i : ℤ, (f ^ i) x = y

@[refl] lemma same_cycle.refl (f : perm β) (x : β) : same_cycle f x x := ⟨0, rfl⟩

@[symm] lemma same_cycle.symm (f : perm β) {x y : β} : same_cycle f x y → same_cycle f y x :=
λ ⟨i, hi⟩, ⟨-i, by rw [gpow_neg, ← hi, inv_apply_self]⟩

@[trans] lemma same_cycle.trans (f : perm β) {x y z : β} :
  same_cycle f x y → same_cycle f y z → same_cycle f x z :=
λ ⟨i, hi⟩ ⟨j, hj⟩, ⟨j + i, by rw [gpow_add, mul_apply, hi, hj]⟩

lemma apply_eq_self_iff_of_same_cycle {f : perm β} {x y : β} :
  same_cycle f x y → (f x = x ↔ f y = y) :=
λ ⟨i, hi⟩, by rw [← hi, ← mul_apply, ← gpow_one_add, add_comm, gpow_add_one, mul_apply,
    (f ^ i).bijective.1.eq_iff]

lemma same_cycle_of_is_cycle {f : perm β} (hf : is_cycle f) {x y : β}
  (hx : f x ≠ x) (hy : f y ≠ y) : same_cycle f x y :=
exists_gpow_eq_of_is_cycle hf hx hy

instance [fintype α] (f : perm α) : decidable_rel (same_cycle f) :=
λ x y, decidable_of_iff (∃ n ∈ list.range (order_of f), (f ^ n) x = y)
⟨λ ⟨n, _, hn⟩, ⟨n, hn⟩, λ ⟨i, hi⟩, ⟨(i % order_of f).nat_abs, list.mem_range.2
  (int.coe_nat_lt.1 $
    by rw int.nat_abs_of_nonneg (int.mod_nonneg _
      (int.coe_nat_ne_zero_iff_pos.2 (order_of_pos _)));
        exact calc _ < _ : int.mod_lt _ (int.coe_nat_ne_zero_iff_pos.2 (order_of_pos _))
          ... = _ : by simp),
  by rw [← gpow_coe_nat, int.nat_abs_of_nonneg (int.mod_nonneg _
      (int.coe_nat_ne_zero_iff_pos.2 (order_of_pos _))), ← gpow_eq_mod_order_of, hi]⟩⟩

lemma same_cycle_apply {f : perm β} {x y : β} : same_cycle f x (f y) ↔ same_cycle f x y :=
⟨λ ⟨i, hi⟩, ⟨-1 + i, by rw [gpow_add, mul_apply, hi, gpow_neg_one, inv_apply_self]⟩,
 λ ⟨i, hi⟩, ⟨1 + i, by rw [gpow_add, mul_apply, hi, gpow_one]⟩⟩

lemma same_cycle_cycle {f : perm β} {x : β} (hx : f x ≠ x) : is_cycle f ↔
  (∀ {y}, same_cycle f x y ↔ f y ≠ y) :=
⟨λ hf y, ⟨λ ⟨i, hi⟩ hy, hx $
    by rw [← gpow_apply_eq_self_of_apply_eq_self hy i, (f ^ i).bijective.1.eq_iff] at hi;
    rw [hi, hy],
  exists_gpow_eq_of_is_cycle hf hx⟩,
  λ h, ⟨x, hx, λ y hy, h.2 hy⟩⟩

lemma same_cycle_inv (f : perm β) {x y : β} : same_cycle f⁻¹ x y ↔ same_cycle f x y :=
⟨λ ⟨i, hi⟩, ⟨-i, by rw [gpow_neg, ← inv_gpow, hi]⟩,
 λ ⟨i, hi⟩, ⟨-i, by rw [gpow_neg, ← inv_gpow, inv_inv, hi]⟩ ⟩

lemma same_cycle_inv_apply {f : perm β} {x y : β} : same_cycle f x (f⁻¹ y) ↔ same_cycle f x y :=
by rw [← same_cycle_inv, same_cycle_apply, same_cycle_inv]

def cycle_of [fintype α] (f : perm α) (x : α) : perm α :=
of_subtype (@subtype_perm _ f (same_cycle f x) (λ _, same_cycle_apply.symm))

lemma cycle_of_apply [fintype α] (f : perm α) (x y : α) :
  cycle_of f x y = if same_cycle f x y then f y else y := rfl

lemma cycle_of_inv [fintype α] (f : perm α) (x : α) :
  (cycle_of f x)⁻¹ = cycle_of f⁻¹ x :=
equiv.ext _ _ $ λ y, begin
  rw [inv_eq_iff_eq, cycle_of_apply, cycle_of_apply];
  split_ifs; simp [*, same_cycle_inv, same_cycle_inv_apply] at *
end

@[simp] lemma cycle_of_pow_apply_self [fintype α] (f : perm α) (x : α) :
  ∀ n : ℕ, (cycle_of f x ^ n) x = (f ^ n) x
| 0     := rfl
| (n+1) := by rw [pow_succ, mul_apply, cycle_of_apply,
    cycle_of_pow_apply_self, if_pos, pow_succ, mul_apply];
  exact ⟨n, rfl⟩

@[simp] lemma cycle_of_gpow_apply_self [fintype α] (f : perm α) (x : α) :
  ∀ n : ℤ, (cycle_of f x ^ n) x = (f ^ n) x
| (n : ℕ) := cycle_of_pow_apply_self f x n
| -[1+ n] := by rw [gpow_neg_succ, ← inv_pow, cycle_of_inv,
  gpow_neg_succ, ← inv_pow, cycle_of_pow_apply_self]

lemma cycle_of_apply_of_same_cycle [fintype α] {f : perm α} {x y : α} (h : same_cycle f x y) :
  cycle_of f x y = f y := dif_pos h

lemma cycle_of_apply_of_not_same_cycle [fintype α] {f : perm α} {x y : α} (h : ¬same_cycle f x y) :
  cycle_of f x y = y := dif_neg h

@[simp] lemma cycle_of_apply_self [fintype α] (f : perm α) (x : α) :
  cycle_of f x x = f x := cycle_of_apply_of_same_cycle (same_cycle.refl _ _)

lemma cycle_of_cycle [fintype α] {f : perm α} (hf : is_cycle f) {x : α} (hx : f x ≠ x) :
  cycle_of f x = f :=
equiv.ext _ _ $ λ y,
  if h : same_cycle f x y then by rw [cycle_of_apply_of_same_cycle h]
  else by rw [cycle_of_apply_of_not_same_cycle h, not_not.1 (mt ((same_cycle_cycle hx).1 hf).2 h)]

lemma cycle_of_one [fintype α] (x : α) : cycle_of 1 x = 1 :=
by rw [cycle_of, subtype_perm_one (same_cycle 1 x), of_subtype_one]

lemma is_cycle_cycle_of [fintype α] (f : perm α) {x : α} (hx : f x ≠ x) : is_cycle (cycle_of f x) :=
have cycle_of f x x ≠ x, by rwa [cycle_of_apply_of_same_cycle (same_cycle.refl _ _)],
(same_cycle_cycle this).2 $ λ y,
⟨λ h, mt (apply_eq_self_iff_of_same_cycle h).2 this,
  λ h, if hxy : same_cycle f x y then
  let ⟨i, hi⟩ := hxy in
  ⟨i, by rw [cycle_of_gpow_apply_self, hi]⟩
  else by rw [cycle_of_apply_of_not_same_cycle hxy] at h; exact (h rfl).elim⟩

def cycle_factors_aux [fintype α] : Π (l : list α) (f : perm α), (∀ {x}, f x ≠ x → x ∈ l) →
  {l : list (perm α) // l.prod = f ∧ (∀ g ∈ l, is_cycle g) ∧ l.pairwise disjoint}
| []     f h := ⟨[], by simp [*, imp_false, list.pairwise.nil] at *; ext; simp *⟩
| (x::l) f h :=
if hx : f x = x then cycle_factors_aux l f (λ y hy, list.mem_of_ne_of_mem (λ h, hy (by rwa h)) (h hy))
else let ⟨m, hm₁, hm₂, hm₃⟩ := cycle_factors_aux l ((cycle_of f x)⁻¹ * f)
  (λ y hy, list.mem_of_ne_of_mem
    (λ h : y = x, by rw [h, mul_apply, ne.def, inv_eq_iff_eq, cycle_of_apply_self] at hy; exact hy rfl)
    (h (λ h : f y = y,
      by rw [mul_apply, h, ne.def, inv_eq_iff_eq, cycle_of_apply] at hy; split_ifs at hy; cc))) in
    ⟨(cycle_of f x) :: m, by rw [list.prod_cons, hm₁]; simp,
      λ g hg, ((list.mem_cons_iff _ _ _).1 hg).elim (λ hg, hg.symm ▸ is_cycle_cycle_of _ hx)
        (hm₂ g),
      list.pairwise_cons.2 ⟨λ g hg y,
        or_iff_not_imp_left.2 (λ hfy,
          have hxy : same_cycle f x y := not_not.1 (mt cycle_of_apply_of_not_same_cycle hfy),
          have hgm : g :: m.erase g ~ m := list.cons_perm_iff_perm_erase.2 ⟨hg, list.perm.refl _⟩,
          have ∀ h ∈ m.erase g, disjoint g h,
            from (list.pairwise_cons.1 ((list.perm_pairwise (λ a b (h : disjoint a b), h.symm) hgm).2 hm₃)).1,
          classical.by_cases id $ λ hgy : g y ≠ y,
            (disjoint_prod_right _ this y).resolve_right $
            have hsc : same_cycle f⁻¹ x (f y), by rwa [same_cycle_inv, same_cycle_apply],
            by rw [disjoint_prod_perm hm₃ hgm.symm, list.prod_cons, ← eq_inv_mul_iff_mul_eq] at hm₁;
              rwa [hm₁, mul_apply, mul_apply, cycle_of_inv, cycle_of_apply_of_same_cycle hsc,
                inv_apply_self, inv_eq_iff_eq, eq_comm]),
        hm₃⟩⟩

def cycle_factors [fintype α] [decidable_linear_order α] (f : perm α) :
  {l : list (perm α) // l.prod = f ∧ (∀ g ∈ l, is_cycle g) ∧ l.pairwise disjoint} :=
cycle_factors_aux (univ.sort (≤)) f (λ _ _, (mem_sort _).2 (mem_univ _))

end equiv.perm
