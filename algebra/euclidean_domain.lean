/- 
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin

Euclidean domains and Euclidean algorithm (extended to come)
A lot is based on pre-existing code in mathlib for natural number gcds
-/
import tactic.ring

universe u

class euclidean_domain (α : Type u) extends integral_domain α :=
( quotient : α → α → α )
( remainder : α → α → α )
( witness : ∀ a b, (quotient a b) * b + (remainder a b) = a ) -- This could be changed to the same order as int.mod_add_div. We normally write qb+r rather than r + qb though.
(valuation : α → ℕ)
(val_mod : ∀ a b, b = 0 ∨  valuation (remainder a b) <  valuation b)
(val_mul : ∀ a b, b = 0 ∨ valuation a ≤ valuation (a*b))
/-
val_mul is often not a required in definitions of a euclidean domain since given the other properties we can show there is a (noncomputable) euclidean domain α with the property val_mul.
So potentially this definition could be split into two different ones (euclidean_domain_weak and euclidean_domain_strong) with a noncomputable function from weak to strong.
I've currently divided the lemmas into strong and weak depending on whether they require val_mul or not.
-/

class decidable_euclidean_domain (α : Type u) extends euclidean_domain α:=
(decidable_eq_zero : ∀ a : α, decidable (a = 0))
/-
We use this for basically everything.
It might be worth making it part of the original definition?
-/

namespace euclidean_domain
variable {α : Type u}

instance decidable_eq_zero  [ed : decidable_euclidean_domain α] (a : α) : decidable (a = 0) :=
 decidable_euclidean_domain.decidable_eq_zero a

instance euclidean_domain_has_div [euclidean_domain α] : has_div α := { 
    div := quotient
}

instance euclidean_domain_has_mod [euclidean_domain α] : has_mod α := {
    mod := remainder
}

instance ed_has_sizeof [euclidean_domain α] : has_sizeof α := {
    sizeof := λ x : α, valuation x,
}

definition gcd_decreasing [euclidean_domain α] (a b : α) (w : a ≠ 0) : has_well_founded.r (b % a) a := 
begin
    cases val_mod b a,
    { contradiction },
    { exact h }
end

def gcd [decidable_euclidean_domain α] : α → α → α
| a b := if a_zero : a = 0 then b
         else have h : has_well_founded.r (b % a) a := gcd_decreasing a b a_zero,
              gcd (b%a) a

/- weak lemmas -/

@[simp] lemma mod_zero [ed : euclidean_domain α] (a : α)  : a % 0 = a :=
begin
    have := euclidean_domain.witness a 0,
    simp at this,
    exact this,
end

lemma dvd_mod_self [decidable_euclidean_domain α] (a : α) : a ∣ a % a :=
begin
    let d := (a/a)*a, -- ring tactic can't solve things without this
    have : a%a = a - (a/a)*a, from
        calc
            a%a = d + a%a  - d : by ring
            ... = (a/a)*a + a%a - (a/a)*a : by dsimp [d]; refl
            ... = a - (a/a)*a : by dsimp [(%),(/)]; rw [witness a a],
    rw this,
    exact dvd_sub (dvd_refl a) (dvd_mul_left a (a/a)),
end

lemma mod_lt [decidable_euclidean_domain α]  :
                     ∀ (a : α) {b : α}, valuation b > valuation (0:α) →  valuation (a%b) < valuation b :=
begin
    intros a b h,
    cases decidable.em (b=0) with h',
    {
        rw h' at h,
        have := lt_irrefl (valuation (0:α)),
        contradiction,
    },
    {
        cases val_mod a b with h h',
        { contradiction },
        { exact h' }
    }
end

lemma neq_zero_lt_mod_lt [decidable_euclidean_domain α]  (a b : α) :  b ≠ 0 → valuation (a%b) < valuation b :=
begin
    intro hnb,
    cases val_mod a b,
    { contradiction },
    { exact h }
end

lemma dvd_mod [decidable_euclidean_domain α] {a b c : α} : c ∣ a → c ∣ b → c ∣ a % b :=
begin
    intros dvd_a dvd_b,
    have : remainder a b = a - quotient a b * b, from
    calc 
        a%b = quotient a b * b + a%b - quotient a b * b : by ring
        ... = a - quotient a b * b : by {dsimp[(%)]; rw (witness a b)},
    dsimp [(%)], rw this,
    exact dvd_sub dvd_a (dvd_mul_of_dvd_right dvd_b (a/b)),
end

/- strong lemmas -/

lemma val_lt_one [decidable_euclidean_domain α] (a : α) : 
valuation a < valuation (1:α) → a = 0 :=
begin
    intro a_lt,
    cases val_mul (1:α) a,
    { exact h },
    {
        simp at h,
        have := not_le_of_lt a_lt,
        contradiction
    }
end

lemma val_dvd_le [decidable_euclidean_domain α] (a b : α) :
    b ∣ a → a ≠ 0 → valuation b ≤ valuation a :=
begin
    intros b_dvd ha,
    induction b_dvd with x hx, rw hx,
    cases val_mul b x,
    {
        rw h at hx, simp at hx,
        contradiction,
    },
    {
        exact h,
    }
end

@[simp] lemma mod_one [decidable_euclidean_domain α] (a : α) : a % 1 = 0 :=
begin
    cases val_mod a 1,
    { 
        have := one_ne_zero, 
        contradiction,
    },
    {
        exact val_lt_one (a % 1) h,
    }
end 

@[simp] lemma zero_mod  [decidable_euclidean_domain α] (b : α) : 0 % b = 0 :=
begin
    have h1 := witness 0 b,
    have h2 : remainder 0 b = b * (-quotient 0 b ), from
        calc
            remainder 0 b = quotient 0 b * b + remainder 0 b + b * (-quotient 0 b ) : by ring
            ...                       = b * (-quotient 0 b ) : by rw [h1, zero_add],
    cases val_mul b (-quotient 0 b),
    {
        simp at h, rw h at h1, simp at h1,
        exact h1,
    },
    {
        rw [←h2] at h,
        cases val_mod 0 b,
        {
            rw h_1, exact mod_zero (0:α),
        },
        {
            have := not_le_of_lt h_1,
            contradiction,
        }
    }
end

@[simp] lemma zero_div [decidable_euclidean_domain α] (b : α) (hnb : b ≠ 0) : 0 / b = 0 :=
begin
    have h1 := zero_mod b, dsimp [(%)] at h1,
    have h2 := euclidean_domain.witness 0 b,
    rw h1 at h2,
    simp at h2,
    dsimp [(/)],
    cases eq_zero_or_eq_zero_of_mul_eq_zero h2,
    {exact h},
    {contradiction}
end

@[simp] lemma mod_self [decidable_euclidean_domain α] (a : α) : a % a = 0 :=
begin
    have := witness a a,
    cases (dvd_mod_self a) with m a_mul,
    cases val_mul a m,
    {
        rw [h, mul_zero] at a_mul,
        exact a_mul,
    },
    {
        cases  val_mod a a, 
        {rw h_1, exact mod_zero (0:α)},
        {
            have := not_le_of_lt h_1,
            dsimp [(%)] at a_mul,
            rw a_mul at this,
            contradiction,
        }
    }
end 

lemma div_self [decidable_euclidean_domain α] (a : α) : a ≠ 0 → a / a = (1:α) :=
begin
    intro hna,
    have wit_aa := witness a a,
    have a_mod_a := mod_self a, 
    dsimp [(%)] at a_mod_a,
    rw a_mod_a at wit_aa, simp at wit_aa,
    have h1 : 1 * a = a, from one_mul a,
    conv at wit_aa {for a [4] {rw ←h1}},
    exact eq_of_mul_eq_mul_right hna wit_aa
end

/- weak gcd lemmas -/

@[simp] theorem gcd_zero_left [decidable_euclidean_domain α] (a : α) : gcd 0 a = a := 
begin
    rw gcd,
    simp,
end

@[elab_as_eliminator]
theorem gcd.induction [decidable_euclidean_domain α] 
                    {P : α → α → Prop}
                    (a b : α)
                    (H0 : ∀ x, P 0 x)
                    (H1 : ∀ a b, a ≠ 0 → P (b%a) a → P a b) :
                P a b := 
@well_founded.induction _ _ (has_well_founded.wf α) (λa, ∀b, P a b) a (λc IH,
    by {cases decidable.em (c=0), rw h, exact H0,
        exact λ b, H1 c b (h) (IH (b%c) (neq_zero_lt_mod_lt b c h) c)}) b

theorem gcd_dvd [decidable_euclidean_domain α] (a b : α) : (gcd a b ∣ a) ∧ (gcd a b ∣ b) :=
gcd.induction a b
    (λ b, by simp)
    (λ a b aneq,
    begin
        intro h_dvd,
        rw gcd, simp [aneq],
        induction h_dvd,
        split,
        { exact h_dvd_right },
        {
            conv {for b [2] {rw ←(witness b a)}},
            have h_dvd_right_a:= dvd_mul_of_dvd_right h_dvd_right (b/a),
            exact dvd_add h_dvd_right_a h_dvd_left
        }
    end )

theorem gcd_dvd_left [decidable_euclidean_domain α] (a b : α) :
    gcd a b ∣ a := (gcd_dvd a b).left

theorem gcd_dvd_right [decidable_euclidean_domain α] (a b : α) :
    gcd a b ∣ b := (gcd_dvd a b).right

theorem dvd_gcd [decidable_euclidean_domain α] {a b c : α} : c ∣ a → c ∣ b → c ∣ gcd a b :=
gcd.induction a b
    (λ b,
    begin
        intros dvd_0 dvd_b,
        simp, exact dvd_b
    end)
    (λ a b hna,
    begin
        intros d dvd_a dvd_b,
        rw gcd, simp [hna],
        exact d (dvd_mod dvd_b dvd_a) dvd_a,
    end)

/- strong gcd lemmas -/

@[simp] theorem gcd_zero_right [decidable_euclidean_domain α]  (a : α) : gcd a 0 = a :=
begin
    cases decidable.em (a=0),
    {
        rw h,
        simp,
    },
    {
        rw gcd,
        simp [h],
    }
end

@[simp] theorem gcd_one_left [decidable_euclidean_domain α] (a : α) : gcd 1 a = 1 := 
begin
    rw [gcd],
    simp,
end

theorem gcd_next [decidable_euclidean_domain α] (a b : α) : gcd a b = gcd (b % a) a :=
begin
    cases decidable.em (a=0),
    {
        simp [h],
    },
    {
        rw gcd,
        simp [h],
    }
end

@[simp] theorem gcd_self [decidable_euclidean_domain α] (a : α) : gcd a a = a :=
by rw [gcd_next a a, mod_self a, gcd_zero_left]

end euclidean_domain