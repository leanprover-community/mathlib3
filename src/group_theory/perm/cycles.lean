/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.perm.sign
import group_theory.order_of_element

namespace equiv.perm
open equiv function finset
variables {α : Type*} {β : Type*} [decidable_eq α]

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
    (f ^ i).injective.eq_iff]

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
    by rw [← gpow_apply_eq_self_of_apply_eq_self hy i, (f ^ i).injective.eq_iff] at hi;
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
equiv.ext $ λ y, begin
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
| -[1+ n] := by rw [gpow_neg_succ_of_nat, ← inv_pow, cycle_of_inv,
  gpow_neg_succ_of_nat, ← inv_pow, cycle_of_pow_apply_self]

lemma cycle_of_apply_of_same_cycle [fintype α] {f : perm α} {x y : α} (h : same_cycle f x y) :
  cycle_of f x y = f y := dif_pos h

lemma cycle_of_apply_of_not_same_cycle [fintype α] {f : perm α} {x y : α} (h : ¬same_cycle f x y) :
  cycle_of f x y = y := dif_neg h

@[simp] lemma cycle_of_apply_self [fintype α] (f : perm α) (x : α) :
  cycle_of f x x = f x := cycle_of_apply_of_same_cycle (same_cycle.refl _ _)

lemma cycle_of_cycle [fintype α] {f : perm α} (hf : is_cycle f) {x : α} (hx : f x ≠ x) :
  cycle_of f x = f :=
equiv.ext $ λ y,
  if h : same_cycle f x y then by rw [cycle_of_apply_of_same_cycle h]
  else by rw [cycle_of_apply_of_not_same_cycle h, not_not.1 (mt ((same_cycle_cycle hx).1 hf).2 h)]

lemma cycle_of_one [fintype α] (x : α) : cycle_of 1 x = 1 :=
by rw [cycle_of, subtype_perm_one (same_cycle 1 x), of_subtype.map_one]

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
            from (list.pairwise_cons.1 ((hgm.pairwise_iff (λ a b (h : disjoint a b), h.symm)).2 hm₃)).1,
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
