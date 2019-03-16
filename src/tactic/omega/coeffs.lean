/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

A tactic for discharging Presburger arithmetic goals using the Omega test.
-/

import tactic.ring
import tactic.omega.list 
import tactic.omega.logic 
import tactic.omega.int 

@[reducible] def coeffs : Type := list int

namespace coeffs

@[omega] def val_between (v : nat → int) (as : coeffs) (l : nat) : nat → int 
| 0     := 0 
| (o+1) := (val_between o) + (as.get (l+o) * v (l+o))

@[omega] lemma val_between_nil {v l} : 
  ∀ m, val_between v [] l m = 0 
| 0 := by simp_omega
| (m+1) := by simp_omega [val_between_nil m]

def val (v as) : int := val_between v as 0 as.length

@[omega] lemma val_nil {v} : val v [] = 0 := rfl

lemma val_between_eq_of_le {as : coeffs} {v l} : 
  ∀ m, as.length ≤ l + m → 
  val_between v as l m = val_between v as l (as.length - l) 
| 0 h1 := 
  begin rw (nat.sub_eq_zero_iff_le.elim_right _), apply h1 end
| (m+1) h1 := 
  begin
    rw le_iff_eq_or_lt at h1, cases h1,
    { rw [h1, add_comm l, nat.add_sub_cancel] },
    { simp only [val_between], 
      have h2 :  list.length as ≤ l + m, 
      { rw ← nat.lt_succ_iff, apply h1 },
      rw [list.get_eq_zero_of_le _ h2, zero_mul, add_zero],
      apply val_between_eq_of_le _ h2 } 
  end

lemma val_eq_of_le {as : coeffs} {v k} : 
  as.length ≤ k → val v as = val_between v as 0 k :=
begin
  intro h1, simp only [val], 
  rw [val_between_eq_of_le k _], refl, 
  rw zero_add, exact h1
end

lemma val_between_eq_val_between {v w : nat → int} {as bs : coeffs} {l} :
  ∀ {m}, (∀ x, l ≤ x → x < l + m → v x = w x) → 
    (∀ x, l ≤ x → x < l + m → as.get x = bs.get x) → 
    val_between v as l m = val_between w bs l m 
| 0 h1 h2 := rfl
| (m+1) h1 h2 :=
  begin
    simp only [val_between], 
    have h3 : l + m < l + (m + 1), 
    { rw ← add_assoc, apply lt_add_one },
    apply fun_mono_2,
    apply val_between_eq_val_between; intros x h4 h5,
    { apply h1 _ h4 (lt_trans h5 h3) },
    { apply h2 _ h4 (lt_trans h5 h3) },
    rw [h1 _ _ h3, h2 _ _ h3];
    apply nat.le_add_right
  end

def val_between_set {v a l n} :
  ∀ {m}, l ≤ n → n < l + m → val_between v ([]{n ↦ a}) l m = a * v n 
| 0 h1 h2 := 
  begin exfalso, apply lt_irrefl l (lt_of_le_of_lt h1 h2) end
| (m+1) h1 h2 :=
  begin
    rw [← add_assoc, nat.lt_succ_iff, le_iff_eq_or_lt] at h2, 
    cases h2; simp_omega, 
    { rw h2, simp,
      have h3 : val_between v ([]{l + m↦a}) l m = 0, 
      { apply @eq.trans _ _ (val_between v [] l m),
        { apply val_between_eq_val_between, 
          { intros, refl }, 
          { intros x h4 h5, rw [list.get_nil, 
            list.get_set_eq_of_ne, list.get_nil], 
            apply ne_of_lt h5 } }, 
        apply val_between_nil },
      rw [h3, list.get_set, zero_add] }, 
    { rw [@val_between_set m h1 h2, list.get_set_eq_of_ne],
      simp_omega, apply ne_of_gt, apply h2 }
  end

@[omega] def val_set {v m a} : 
  val v ([]{m ↦ a}) = a * v m := 
begin
  apply val_between_set, apply zero_le,
  simp_omega [list.length_set],
  apply lt_of_lt_of_le (lt_add_one _),
  apply le_max_right 
end

lemma val_between_neg {as v l} : 
  ∀ {o}, val_between v (list.neg as) l o = -(val_between v as l o)
| 0 := rfl
| (o+1) := 
  begin
    simp only [val_between], 
    rw [neg_add, neg_mul_eq_neg_mul],
    apply fun_mono_2, apply val_between_neg,
    apply fun_mono_2 _ rfl, 
    apply list.get_neg
  end

@[omega] lemma val_neg {as v} :
   val v (list.neg as) = -(val v as) := begin
  simp only [val, list.length_neg],
  apply val_between_neg
end

lemma val_between_add {is js v l} : 
  ∀ m, val_between v (list.add is js) l m = 
  (val_between v is l m) + (val_between v js l m) 
| 0     := rfl
| (m+1) := begin simp_omega [val_between_add m], ring end

@[omega] lemma val_add {v} {is js : coeffs} : 
  val v (list.add is js) = (val v is) + (val v js) :=
begin
  simp only [val],
  rw val_between_add, apply fun_mono_2;
  apply val_between_eq_of_le;
  rw [zero_add, list.length_add],
  apply le_max_left, apply le_max_right
end

lemma val_between_sub {is js v l} : 
  ∀ m, val_between v (list.sub is js) l m = 
  (val_between v is l m) - (val_between v js l m) 
| 0 := rfl
| (m+1) := begin simp_omega [val_between_sub m], ring end

@[omega] lemma val_sub {v} {is js : coeffs} : 
  val v (list.sub is js) = (val v is) - (val v js) :=
begin
  simp only [val],
   rw val_between_sub, apply fun_mono_2;
  apply val_between_eq_of_le;
  rw [zero_add, list.length_sub],
  apply le_max_left, apply le_max_right
end

def val_except (n v as) := 
val_between v as 0 n + val_between v as (n+1) (as.length - (n+1))

lemma val_except_eq_val_except 
  {k : nat} {is js : coeffs} {v w : nat → int} :
  (∀ x ≠ k, v x = w x) → (∀ x ≠ k, is.get x = js.get x) → 
  val_except k v is = val_except k w js :=
begin
  intros h1 h2, simp only [val_except],
  apply fun_mono_2, 
  { apply val_between_eq_val_between; intros x h3 h4;
    [ {apply h1}, {apply h2} ]; apply ne_of_lt;
    rw zero_add at h4; apply h4 },
  { repeat { rw ← val_between_eq_of_le 
      ((max is.length js.length) - (k+1)) }, 
    { apply val_between_eq_val_between; intros x h3 h4;
      [ {apply h1}, {apply h2} ]; apply ne.symm;
        apply ne_of_lt; rw nat.lt_iff_add_one_le; exact h3 },
    repeat { rw add_comm, apply le_trans _ (nat.le_sub_add _ _), 
      { apply le_max_right <|> apply le_max_left } } }
end

lemma val_except_update_set {n v as i j} :
  val_except n (v⟨n ↦ i⟩) (as{n ↦ j}) = val_except n v as :=
by rw val_except_eq_val_except update_eq_of_ne list.get_set_eq_of_ne

lemma val_between_add_val_between {v as l m} :
  ∀ {n}, val_between v as l m + val_between v as (l+m) n = 
  val_between v as l (m+n) 
| 0 := by simp_omega
| (n+1) :=
  begin
    rw ← add_assoc, simp_omega, rw add_assoc, 
    rw ← @val_between_add_val_between n, ring
  end

def val_except_add_eq (n) {v as} :
  (val_except n v as) + ((as.get n) * (v n)) = val v as :=
begin
  simp only [val_except, val],
  by_cases h1 : n + 1 ≤ as.length,
  { have h4 := @val_between_add_val_between v as 0 (n+1) (as.length - (n+1)),
    have h5 : n + 1 + (as.length - (n + 1)) = as.length,
    { rw [add_comm, nat.sub_add_cancel h1] },
    rw h5 at h4, apply eq.trans _ h4,
     simp only [val_between, zero_add], ring },
  { rw not_lt at h1,
    have h2 : (list.length as - (n + 1)) = 0,
    { apply nat.sub_eq_zero_of_le 
      (le_trans h1 (nat.le_add_right _ _)) },
    rw h2, simp only [val_between, add_zero],  
    have h3 := @val_eq_of_le as v (n+1) _, 
    simp only [val] at h3, rw h3, 
    simp only [val_between, zero_add],
    apply le_trans h1, apply nat.le_add_right }
end

@[omega] lemma val_between_map_mul {v i as l} :
  ∀ {m}, val_between v (list.map ((*) i) as) l m = i * val_between v as l m 
| 0     := by simp_omega
| (m+1) :=
  begin
    simp_omega [@val_between_map_mul m, mul_add],
    apply fun_mono_2 rfl, 
    by_cases h1 : l + m < as.length,
    { rw [list.get_map h1, mul_assoc] },
    { rw not_lt at h1,
      rw [list.get_eq_zero_of_le, 
          list.get_eq_zero_of_le];
      try {simp_omega}; apply h1 }
  end

lemma forall_val_dvd_of_forall_mem_dvd {i} {as : coeffs} :
  (∀ x ∈ as, i ∣ x) → (∀ n, i ∣ as.get n) | h1 n := 
begin apply list.forall_val_of_forall_mem (dvd_zero _) h1 end

lemma dvd_val_between {i v as l} :
  ∀ {m}, (∀ x ∈ as, i ∣ x) → (i ∣ val_between v as l m)
| 0 h1 := dvd_zero _
| (m+1) h1 :=
  begin
    simp_omega, apply dvd_add,
    apply dvd_val_between h1,
    apply dvd_mul_of_dvd_left,
    by_cases h2 : as.get (l+m) = 0,
    { rw h2, apply dvd_zero },
    { apply h1, apply list.mem_get_of_ne_zero h2 }
  end

lemma dvd_val {i v as} :
  (∀ x ∈ as, i ∣ x) → (i ∣ val v as) := by apply dvd_val_between

@[omega] lemma val_between_map_div {v i as l} (h1 : ∀ x ∈ as, i ∣ x) :
  ∀ {m}, val_between v (list.map (λ x, x / i) as) l m = (val_between v as l m) / i 
| 0     := by simp_omega [int.zero_div]
| (m+1) :=
  begin
    simp_omega [@val_between_map_div m],
    rw [int.add_div (dvd_val_between h1)], 
    apply fun_mono_2 rfl,

    apply calc list.get (l + m) (list.map (λ (x : ℤ), x / i) as) * v (l + m) 
        = ((as.get (l + m)) / i) * v (l + m) : 
          begin
            apply fun_mono_2 _ rfl, 
            rw list.get_map', apply int.zero_div 
          end
    ... =  list.get (l + m) as * v (l + m) / i :
          begin
            repeat {rw mul_comm _ (v (l+m))}, 
            rw int.mul_div_assoc, 
            apply forall_val_dvd_of_forall_mem_dvd h1
          end,
    apply dvd_mul_of_dvd_left,
    apply forall_val_dvd_of_forall_mem_dvd h1,
  end

@[omega] lemma val_map_div {v i as} :
  (∀ x ∈ as, i ∣ x) → 
  val v (list.map (λ x, x / i) as) = (val v as) / i := 
begin 
  intro h1, simp only [val, list.length_map], 
  apply val_between_map_div h1 
end

lemma val_between_eq_zero {v as l} : 
  ∀ {m}, (∀ x : int, x ∈ as → x = 0) → val_between v as l m = 0 
| 0 h1 := rfl
| (m+1) h1 :=
  begin
    have h2 := list.forall_val_of_forall_mem _ h1, 
    simp_omega [h2 (l+m)], apply @val_between_eq_zero m h1, refl,
  end

lemma val_eq_zero {v is} : 
  (∀ x : int, x ∈ is → x = 0) → val v is = 0 :=
by apply val_between_eq_zero

end coeffs