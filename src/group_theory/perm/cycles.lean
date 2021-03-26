/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.perm.sign
/-!
# Cyclic permutations

## Main definitions

In the following, `f : equiv.perm β`.

* `equiv.perm.is_cycle`: `f.is_cycle` when two nonfixed points of `β`
  are related by repeated application of `f`.
* `equiv.perm.same_cycle`: `f.same_cycle x y` when `x` and `y` are in the same cycle of `f`.

The following two definitions require that `β` is a `fintype`:

* `equiv.perm.cycle_of`: `f.cycle_of x` is the cycle of `f` that `x` belongs to.
* `equiv.perm.cycle_factors`: `f.cycle_factors` is a list of disjoint cyclic permutations that
  multiply to `f`.

-/
namespace equiv.perm
open equiv function finset

variables {α : Type*} {β : Type*} [decidable_eq α]

section sign_cycle

/-!
### `is_cycle`
-/

variables [fintype α]

/-- A permutation is a cycle when any two nonfixed points of the permutation are related by repeated
  application of the permutation. -/
def is_cycle (f : perm β) : Prop := ∃ x, f x ≠ x ∧ ∀ y, f y ≠ y → ∃ i : ℤ, (f ^ i) x = y

lemma is_cycle.swap {α : Type*} [decidable_eq α] {x y : α} (hxy : x ≠ y) : is_cycle (swap x y) :=
⟨y, by rwa swap_apply_right,
  λ a (ha : ite (a = x) y (ite (a = y) x a) ≠ a),
    if hya : y = a then ⟨0, hya⟩
    else ⟨1, by { rw [gpow_one, swap_apply_def], split_ifs at *; cc }⟩⟩

lemma is_cycle.inv {f : perm β} (hf : is_cycle f) : is_cycle (f⁻¹) :=
let ⟨x, hx⟩ := hf in
⟨x, by { simp only [inv_eq_iff_eq, *, forall_prop_of_true, ne.def] at *, cc },
  λ y hy, let ⟨i, hi⟩ := hx.2 y (by { simp only [inv_eq_iff_eq, *, forall_prop_of_true,
      ne.def] at *, cc }) in
    ⟨-i, by rwa [gpow_neg, inv_gpow, inv_inv]⟩⟩

lemma is_cycle.exists_gpow_eq {f : perm β} (hf : is_cycle f) {x y : β}
  (hx : f x ≠ x) (hy : f y ≠ y) : ∃ i : ℤ, (f ^ i) x = y :=
let ⟨g, hg⟩ := hf in
let ⟨a, ha⟩ := hg.2 x hx in
let ⟨b, hb⟩ := hg.2 y hy in
⟨b - a, by rw [← ha, ← mul_apply, ← gpow_add, sub_add_cancel, hb]⟩

lemma is_cycle.exists_pow_eq [fintype β] {f : perm β} (hf : is_cycle f) {x y : β}
  (hx : f x ≠ x) (hy : f y ≠ y) : ∃ i : ℕ, (f ^ i) x = y :=
let ⟨n, hn⟩ := hf.exists_gpow_eq hx hy in
by classical; exact ⟨(n % order_of f).to_nat, by {
  have := n.mod_nonneg (int.coe_nat_ne_zero.mpr (ne_of_gt (order_of_pos f))),
  rwa [← gpow_coe_nat, int.to_nat_of_nonneg this, ← gpow_eq_mod_order_of] }⟩

lemma gpow_apply_comm {α : Type*} (σ : perm α) (m n : ℤ) {x : α} :
  (σ ^ m) ((σ ^ n) x) = (σ ^ n) ((σ ^ m) x) :=
by rw [←mul_apply, ←mul_apply, gpow_mul_comm]

lemma order_of_is_cycle {σ : perm α} (hσ : is_cycle σ) : order_of σ = σ.support.card :=
begin
  obtain ⟨x, hx, hσ⟩ := hσ,
  rw [order_eq_card_gpowers, ←fintype.card_coe],
  apply fintype.card_congr,
  refine equiv.of_bijective (λ τ, ⟨τ x, _⟩) ⟨_, _⟩,
  { obtain ⟨τ, n, rfl⟩ := τ,
    rw [finset.mem_coe, mem_support],
    exact λ h, hx ((σ ^ n).injective (by rwa [←mul_apply, mul_gpow_self, ←mul_self_gpow])) },
  { rintros ⟨a, m, rfl⟩ ⟨b, n, rfl⟩ h,
    ext y,
    by_cases hy : σ y = y,
    { simp_rw [subtype.coe_mk, gpow_apply_eq_self_of_apply_eq_self hy] },
    { obtain ⟨i, rfl⟩ := hσ y hy,
      rw [subtype.coe_mk, subtype.coe_mk, gpow_apply_comm σ m i, gpow_apply_comm σ n i],
      exact congr_arg _ (subtype.ext_iff.mp h) } },
  { rintros ⟨y, hy⟩,
    rw [finset.mem_coe, mem_support] at hy,
    obtain ⟨n, rfl⟩ := hσ y hy,
    exact ⟨⟨σ ^ n, n, rfl⟩, rfl⟩ },
end

lemma is_cycle_swap_mul_aux₁ {α : Type*} [decidable_eq α] : ∀ (n : ℕ) {b x : α} {f : perm α}
  (hb : (swap x (f x) * f) b ≠ b) (h : (f ^ n) (f x) = b),
  ∃ i : ℤ, ((swap x (f x) * f) ^ i) (f x) = b
| 0         := λ b x f hb h, ⟨0, h⟩
| (n+1 : ℕ) := λ b x f hb h,
  if hfbx : f x = b then ⟨0, hfbx⟩
  else
    have f b ≠ b ∧ b ≠ x, from ne_and_ne_of_swap_mul_apply_ne_self hb,
    have hb' : (swap x (f x) * f) (f⁻¹ b) ≠ f⁻¹ b,
      by { rw [mul_apply, apply_inv_self, swap_apply_of_ne_of_ne this.2 (ne.symm hfbx),
          ne.def, ← f.injective.eq_iff, apply_inv_self],
        exact this.1 },
    let ⟨i, hi⟩ := is_cycle_swap_mul_aux₁ n hb'
      (f.injective $ by { rw [apply_inv_self], rwa [pow_succ, mul_apply] at h }) in
    ⟨i + 1, by rw [add_comm, gpow_add, mul_apply, hi, gpow_one, mul_apply, apply_inv_self,
        swap_apply_of_ne_of_ne (ne_and_ne_of_swap_mul_apply_ne_self hb).2 (ne.symm hfbx)]⟩

lemma is_cycle_swap_mul_aux₂ {α : Type*} [decidable_eq α] :
  ∀ (n : ℤ) {b x : α} {f : perm α} (hb : (swap x (f x) * f) b ≠ b) (h : (f ^ n) (f x) = b),
  ∃ i : ℤ, ((swap x (f x) * f) ^ i) (f x) = b
| (n : ℕ) := λ b x f, is_cycle_swap_mul_aux₁ n
| -[1+ n] := λ b x f hb h,
  if hfbx : f⁻¹ x = b then
    ⟨-1, by rwa [gpow_neg, gpow_one, mul_inv_rev, mul_apply, swap_inv, swap_apply_right]⟩
  else if hfbx' : f x = b then ⟨0, hfbx'⟩
  else
  have f b ≠ b ∧ b ≠ x := ne_and_ne_of_swap_mul_apply_ne_self hb,
  have hb : (swap x (f⁻¹ x) * f⁻¹) (f⁻¹ b) ≠ f⁻¹ b,
    by { rw [mul_apply, swap_apply_def],
      split_ifs;
      simp only [inv_eq_iff_eq, perm.mul_apply, gpow_neg_succ_of_nat, ne.def,
        perm.apply_inv_self] at *;
      cc },
  let ⟨i, hi⟩ := is_cycle_swap_mul_aux₁ n hb
    (show (f⁻¹ ^ n) (f⁻¹ x) = f⁻¹ b, by
      rw [← gpow_coe_nat, ← h, ← mul_apply, ← mul_apply, ← mul_apply, gpow_neg_succ_of_nat,
        ← inv_pow, pow_succ', mul_assoc, mul_assoc, inv_mul_self, mul_one, gpow_coe_nat,
        ← pow_succ', ← pow_succ]) in
  have h : (swap x (f⁻¹ x) * f⁻¹) (f x) = f⁻¹ x, by rw [mul_apply, inv_apply_self, swap_apply_left],
  ⟨-i, by rw [← add_sub_cancel i 1, neg_sub, sub_eq_add_neg, gpow_add, gpow_one, gpow_neg,
      ← inv_gpow, mul_inv_rev, swap_inv, mul_swap_eq_swap_mul, inv_apply_self, swap_comm _ x,
      gpow_add, gpow_one, mul_apply, mul_apply (_ ^ i), h, hi, mul_apply, apply_inv_self,
      swap_apply_of_ne_of_ne this.2 (ne.symm hfbx')]⟩

lemma is_cycle.eq_swap_of_apply_apply_eq_self {α : Type*} [decidable_eq α]
  {f : perm α} (hf : is_cycle f) {x : α}
  (hfx : f x ≠ x) (hffx : f (f x) = x) : f = swap x (f x) :=
equiv.ext $ λ y,
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

lemma is_cycle.swap_mul {α : Type*} [decidable_eq α] {f : perm α} (hf : is_cycle f) {x : α}
  (hx : f x ≠ x) (hffx : f (f x) ≠ x) : is_cycle (swap x (f x) * f) :=
⟨f x, by { simp only [swap_apply_def, mul_apply],
        split_ifs; simp [f.injective.eq_iff] at *; cc },
  λ y hy,
  let ⟨i, hi⟩ := hf.exists_gpow_eq hx (ne_and_ne_of_swap_mul_apply_ne_self hy).1 in
  have hi : (f ^ (i - 1)) (f x) = y, from
    calc (f ^ (i - 1)) (f x) = (f ^ (i - 1) * f ^ (1 : ℤ)) x : by rw [gpow_one, mul_apply]
    ... = y : by rwa [← gpow_add, sub_add_cancel],
  is_cycle_swap_mul_aux₂ (i - 1) hy hi⟩

lemma is_cycle.sign : ∀ {f : perm α} (hf : is_cycle f),
  sign f = -(-1) ^ f.support.card
| f := λ hf,
let ⟨x, hx⟩ := hf in
calc sign f = sign (swap x (f x) * (swap x (f x) * f)) :
  by rw [← mul_assoc, mul_def, mul_def, swap_swap, trans_refl]
... = -(-1) ^ f.support.card :
  if h1 : f (f x) = x
  then
    have h : swap x (f x) * f = 1,
      begin
        rw hf.eq_swap_of_apply_apply_eq_self hx.1 h1,
        simp only [perm.mul_def, perm.one_def, swap_apply_left, swap_swap]
      end,
    by { rw [sign_mul, sign_swap hx.1.symm, h, sign_one, hf.eq_swap_of_apply_apply_eq_self hx.1 h1,
      card_support_swap hx.1.symm], refl }
  else
    have h : card (support (swap x (f x) * f)) + 1 = card (support f),
      by rw [← insert_erase (mem_support.2 hx.1), support_swap_mul_eq h1,
        card_insert_of_not_mem (not_mem_erase _ _)],
    have wf : card (support (swap x (f x) * f)) < card (support f),
      from card_support_swap_mul hx.1,
    by { rw [sign_mul, sign_swap hx.1.symm, (hf.swap_mul hx.1 h1).sign, ← h],
      simp only [pow_add, mul_one, units.neg_neg, one_mul, units.mul_neg, eq_self_iff_true,
        pow_one, units.neg_mul_neg] }
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ f, f.support.card)⟩]}

end sign_cycle

/-!
### `same_cycle`
-/

/-- The equivalence relation indicating that two points are in the same cycle of a permutation. -/
def same_cycle (f : perm β) (x y : β) : Prop := ∃ i : ℤ, (f ^ i) x = y

@[refl] lemma same_cycle.refl (f : perm β) (x : β) : same_cycle f x x := ⟨0, rfl⟩

@[symm] lemma same_cycle.symm (f : perm β) {x y : β} : same_cycle f x y → same_cycle f y x :=
λ ⟨i, hi⟩, ⟨-i, by rw [gpow_neg, ← hi, inv_apply_self]⟩

@[trans] lemma same_cycle.trans (f : perm β) {x y z : β} :
  same_cycle f x y → same_cycle f y z → same_cycle f x z :=
λ ⟨i, hi⟩ ⟨j, hj⟩, ⟨j + i, by rw [gpow_add, mul_apply, hi, hj]⟩

lemma same_cycle.apply_eq_self_iff {f : perm β} {x y : β} :
  same_cycle f x y → (f x = x ↔ f y = y) :=
λ ⟨i, hi⟩, by rw [← hi, ← mul_apply, ← gpow_one_add, add_comm, gpow_add_one, mul_apply,
    (f ^ i).injective.eq_iff]

lemma is_cycle.same_cycle {f : perm β} (hf : is_cycle f) {x y : β}
  (hx : f x ≠ x) (hy : f y ≠ y) : same_cycle f x y :=
hf.exists_gpow_eq hx hy

noncomputable instance [fintype α] (f : perm α) : decidable_rel (same_cycle f) :=
λ x y, decidable_of_iff (∃ n ∈ list.range (order_of f), (f ^ n) x = y)
⟨λ ⟨n, _, hn⟩, ⟨n, hn⟩, λ ⟨i, hi⟩, ⟨(i % order_of f).nat_abs, list.mem_range.2
  (int.coe_nat_lt.1 $
    by { rw int.nat_abs_of_nonneg (int.mod_nonneg _
        (int.coe_nat_ne_zero_iff_pos.2 (order_of_pos _))),
      calc _ < _ : int.mod_lt _ (int.coe_nat_ne_zero_iff_pos.2 (order_of_pos _))
          ... = _ : by simp,
          exact fintype_perm, }),
  by { rw [← gpow_coe_nat, int.nat_abs_of_nonneg (int.mod_nonneg _
      (int.coe_nat_ne_zero_iff_pos.2 (order_of_pos _))), ← gpow_eq_mod_order_of, hi],
    exact fintype_perm }⟩⟩

lemma same_cycle_apply {f : perm β} {x y : β} : same_cycle f x (f y) ↔ same_cycle f x y :=
⟨λ ⟨i, hi⟩, ⟨-1 + i, by rw [gpow_add, mul_apply, hi, gpow_neg_one, inv_apply_self]⟩,
 λ ⟨i, hi⟩, ⟨1 + i, by rw [gpow_add, mul_apply, hi, gpow_one]⟩⟩

lemma same_cycle_cycle {f : perm β} {x : β} (hx : f x ≠ x) : is_cycle f ↔
  (∀ {y}, same_cycle f x y ↔ f y ≠ y) :=
⟨λ hf y, ⟨λ ⟨i, hi⟩ hy, hx $
    by { rw [← gpow_apply_eq_self_of_apply_eq_self hy i, (f ^ i).injective.eq_iff] at hi,
      rw [hi, hy] },
  hf.exists_gpow_eq hx⟩,
  λ h, ⟨x, hx, λ y hy, h.2 hy⟩⟩

lemma same_cycle_inv (f : perm β) {x y : β} : same_cycle f⁻¹ x y ↔ same_cycle f x y :=
⟨λ ⟨i, hi⟩, ⟨-i, by rw [gpow_neg, ← inv_gpow, hi]⟩,
 λ ⟨i, hi⟩, ⟨-i, by rw [gpow_neg, ← inv_gpow, inv_inv, hi]⟩ ⟩

lemma same_cycle_inv_apply {f : perm β} {x y : β} : same_cycle f x (f⁻¹ y) ↔ same_cycle f x y :=
by rw [← same_cycle_inv, same_cycle_apply, same_cycle_inv]

/-!
### `cycle_of`
-/

/-- `f.cycle_of x` is the cycle of the permutation `f` to which `x` belongs. -/
noncomputable def cycle_of [fintype α] (f : perm α) (x : α) : perm α :=
of_subtype (@subtype_perm _ f (same_cycle f x) (λ _, same_cycle_apply.symm))

lemma cycle_of_apply [fintype α] (f : perm α) (x y : α) :
  cycle_of f x y = if same_cycle f x y then f y else y := rfl

lemma cycle_of_inv [fintype α] (f : perm α) (x : α) :
  (cycle_of f x)⁻¹ = cycle_of f⁻¹ x :=
equiv.ext $ λ y, begin
  rw [inv_eq_iff_eq, cycle_of_apply, cycle_of_apply],
  split_ifs; simp [*, same_cycle_inv, same_cycle_inv_apply] at *
end

@[simp] lemma cycle_of_pow_apply_self [fintype α] (f : perm α) (x : α) :
  ∀ n : ℕ, (cycle_of f x ^ n) x = (f ^ n) x
| 0     := rfl
| (n+1) := by { rw [pow_succ, mul_apply, cycle_of_apply,
    cycle_of_pow_apply_self, if_pos, pow_succ, mul_apply],
  exact ⟨n, rfl⟩ }

@[simp] lemma cycle_of_gpow_apply_self [fintype α] (f : perm α) (x : α) :
  ∀ n : ℤ, (cycle_of f x ^ n) x = (f ^ n) x
| (n : ℕ) := cycle_of_pow_apply_self f x n
| -[1+ n] := by rw [gpow_neg_succ_of_nat, ← inv_pow, cycle_of_inv,
  gpow_neg_succ_of_nat, ← inv_pow, cycle_of_pow_apply_self]

lemma same_cycle.cycle_of_apply [fintype α] {f : perm α} {x y : α} (h : same_cycle f x y) :
  cycle_of f x y = f y := dif_pos h

lemma cycle_of_apply_of_not_same_cycle [fintype α] {f : perm α} {x y : α} (h : ¬same_cycle f x y) :
  cycle_of f x y = y := dif_neg h

@[simp] lemma cycle_of_apply_self [fintype α] (f : perm α) (x : α) :
  cycle_of f x x = f x := (same_cycle.refl _ _).cycle_of_apply

lemma is_cycle.cycle_of_eq [fintype α] {f : perm α} (hf : is_cycle f) {x : α} (hx : f x ≠ x) :
  cycle_of f x = f :=
equiv.ext $ λ y,
  if h : same_cycle f x y then by rw [h.cycle_of_apply]
  else by rw [cycle_of_apply_of_not_same_cycle h, not_not.1 (mt ((same_cycle_cycle hx).1 hf).2 h)]

lemma cycle_of_one [fintype α] (x : α) : cycle_of 1 x = 1 :=
by rw [cycle_of, subtype_perm_one (same_cycle 1 x), of_subtype.map_one]

lemma is_cycle_cycle_of [fintype α] (f : perm α) {x : α} (hx : f x ≠ x) : is_cycle (cycle_of f x) :=
have cycle_of f x x ≠ x, by rwa [(same_cycle.refl _ _).cycle_of_apply],
(same_cycle_cycle this).2 $ λ y,
⟨λ h, mt h.apply_eq_self_iff.2 this,
  λ h, if hxy : same_cycle f x y then
  let ⟨i, hi⟩ := hxy in
  ⟨i, by rw [cycle_of_gpow_apply_self, hi]⟩
  else by { rw [cycle_of_apply_of_not_same_cycle hxy] at h, exact (h rfl).elim }⟩

/-!
### `cycle_factors`
-/

/-- Given a list `l : list α` and a permutation `f : perm α` whose nonfixed points are all in `l`,
  recursively factors `f` into cycles. -/
noncomputable def cycle_factors_aux [fintype α] : Π (l : list α) (f : perm α),
  (∀ {x}, f x ≠ x → x ∈ l) →
  {l : list (perm α) // l.prod = f ∧ (∀ g ∈ l, is_cycle g) ∧ l.pairwise disjoint}
| []     f h := ⟨[], by { simp only [imp_false, list.pairwise.nil, list.not_mem_nil, forall_const,
    and_true, forall_prop_of_false, not_not, not_false_iff, list.prod_nil] at *,
  ext, simp * }⟩
| (x::l) f h :=
if hx : f x = x then
  cycle_factors_aux l f (λ y hy, list.mem_of_ne_of_mem (λ h, hy (by rwa h)) (h hy))
else let ⟨m, hm₁, hm₂, hm₃⟩ := cycle_factors_aux l ((cycle_of f x)⁻¹ * f)
  (λ y hy, list.mem_of_ne_of_mem
    (λ h : y = x,
      by { rw [h, mul_apply, ne.def, inv_eq_iff_eq, cycle_of_apply_self] at hy, exact hy rfl })
    (h (λ h : f y = y, by { rw [mul_apply, h, ne.def, inv_eq_iff_eq, cycle_of_apply] at hy,
        split_ifs at hy; cc }))) in
    ⟨(cycle_of f x) :: m, by { rw [list.prod_cons, hm₁], simp },
      λ g hg, ((list.mem_cons_iff _ _ _).1 hg).elim (λ hg, hg.symm ▸ is_cycle_cycle_of _ hx)
        (hm₂ g),
      list.pairwise_cons.2 ⟨λ g hg y,
        or_iff_not_imp_left.2 (λ hfy,
          have hxy : same_cycle f x y := not_not.1 (mt cycle_of_apply_of_not_same_cycle hfy),
          have hgm : g :: m.erase g ~ m := list.cons_perm_iff_perm_erase.2 ⟨hg, list.perm.refl _⟩,
          have ∀ h ∈ m.erase g, disjoint g h, from
            (list.pairwise_cons.1 ((hgm.pairwise_iff (λ a b (h : disjoint a b), h.symm)).2 hm₃)).1,
          classical.by_cases id $ λ hgy : g y ≠ y,
            (disjoint_prod_right _ this y).resolve_right $
            have hsc : same_cycle f⁻¹ x (f y), by rwa [same_cycle_inv, same_cycle_apply],
            by { rw [disjoint_prod_perm hm₃ hgm.symm, list.prod_cons,
                ← eq_inv_mul_iff_mul_eq] at hm₁,
              rwa [hm₁, mul_apply, mul_apply, cycle_of_inv, hsc.cycle_of_apply,
                inv_apply_self, inv_eq_iff_eq, eq_comm] }),
        hm₃⟩⟩

/-- Factors a permutation `f` into a list of disjoint cyclic permutations that multiply to `f`. -/
noncomputable def cycle_factors [fintype α] [linear_order α] (f : perm α) :
  {l : list (perm α) // l.prod = f ∧ (∀ g ∈ l, is_cycle g) ∧ l.pairwise disjoint} :=
cycle_factors_aux (univ.sort (≤)) f (λ _ _, (mem_sort _).2 (mem_univ _))

section fixed_points

/-!
### Fixed points
-/

lemma one_lt_nonfixed_point_card_of_ne_one [fintype α] {σ : perm α} (h : σ ≠ 1) :
  1 < (filter (λ x, σ x ≠ x) univ).card :=
begin
  rw one_lt_card_iff,
  contrapose! h,
  ext x,
  dsimp,
  have := h (σ x) x,
  contrapose! this,
  simpa,
end

lemma fixed_point_card_lt_of_ne_one [fintype α] {σ : perm α} (h : σ ≠ 1) :
  (filter (λ x, σ x = x) univ).card < fintype.card α - 1 :=
begin
  rw [nat.lt_sub_left_iff_add_lt, ← nat.lt_sub_right_iff_add_lt, ← finset.card_compl,
    finset.compl_filter],
  exact one_lt_nonfixed_point_card_of_ne_one h
end

end fixed_points

end equiv.perm
