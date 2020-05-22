
import data.nat.prime
import data.nat.basic
import data.zmod.basic
import tactic
import algebra.pi_instances
import group_theory.order_of_element
import data.rat.basic
import tactic.interactive
import data.multiset

open nat

section mathlib_supplementation

/- Additions to Mathlib -/

-- The square of the smallest prime factor of a natural number n is less than or equal to n.
lemma min_fac_sq (n : ℕ) (h_1 : 0 < n) (h : ¬ prime n) : (min_fac n)^2 ≤ n :=
begin
  have t : (min_fac n) ≤ (n/min_fac n) := min_fac_le_div h_1 h,
  calc
   (min_fac n)^2 = (min_fac n) *(min_fac n) :  by exact pow_two (min_fac n)
             ... ≤ (n/min_fac n)* (min_fac n) : by exact mul_le_mul_right (min_fac n) t
             ... ≤ n : by exact div_mul_le_self n (min_fac n)
end

-- Credit Bhavik Mehta
lemma pow_monotonic { a m n : ℕ } ( ha : 2 ≤ a ) ( k : a^n ≤ a^m ) : n ≤ m :=
  le_of_not_gt (λ r, not_le_of_lt (pow_lt_pow_of_lt_right ha r) k)

-- Credit Bhavik Mehta
lemma pow_inj (a b c : ℕ) (h : 2 ≤ a) (h_2 : a^b = a^c) : b = c :=
by apply le_antisymm; apply pow_monotonic h; apply le_of_eq; rw h_2

-- If p is prime, then p^k divides p^l implies that k is less than or equal to l.
lemma prime_pow_dvd_prime_pow {p k l : ℕ} (pp : prime p) : p^k ∣ p^l ↔ k ≤ l :=
begin
split,
{ intro h,
  have t :=  (dvd_prime_pow pp).1 h,
  rcases t with ⟨m, ⟨h₁, h₂⟩⟩,
  have t : k = m := pow_inj p k m (prime.two_le pp) h₂,
  subst t, exact h₁ },
exact pow_dvd_pow p,
end

-- If p is prime, a doesn't divide p^k, but a does divide p^(k+1) then a = p^(k+1)
lemma dvd_prime_power (a p k : ℕ) (pp : prime p) (h₁ : ¬(a ∣ p^k)) (h₂ : a ∣ p^(k+1)) : a = p^(k+1) :=
begin
  rcases (dvd_prime_pow pp).1 h₂ with ⟨l,⟨h,rfl⟩⟩,
  -- l is some natural number less than k or equal to k+1
  congr,
  have : k < l := not_le.1 ((not_congr (prime_pow_dvd_prime_pow pp)).1 h₁),
  linarith,
end

-- Credit Scott Morrison
-- Order properties
variables {G : Type} [group G] [fintype G] [decidable_eq G]

lemma order_of_dvd_iff {n : ℕ} {g : G} : order_of g ∣ n ↔ g^n = 1 :=
⟨λ h,
 begin
   rcases h with ⟨k,rfl⟩,
   simp only [pow_mul, _root_.one_pow, pow_order_of_eq_one]
 end,
 order_of_dvd_of_pow_eq_one⟩

lemma multiple_mod {a : ℤ} {b : ℕ} (h : a % b = 0) : ∃ (k : ℤ), k * b = a :=
⟨a / b, int.div_mul_cancel (int.dvd_of_mod_eq_zero h)⟩

end  mathlib_supplementation

section Mersenne

/- Defining the Mersenne Numbers -/

def M (p : ℕ) : ℕ := 2^p - 1

lemma M_pos {p : ℕ} (h : 0 < p) : 0 < M p :=
begin
  dsimp [M],
  calc 0 < 2^1 - 1 : by norm_num
     ... ≤ 2^p - 1 : pred_le_pred (pow_le_pow_of_le_right (succ_pos 1) h)
end

end Mersenne


def s' (p : ℕ) : ℕ → zmod (2^p - 1)
| 0 := 4
| (i+1) := ((s' i)^2 - 2)

def s : ℕ → ℤ
| 0 := 4
| (i+1) := (s i)^2 - 2

lemma s_eq_s' (p : ℕ) (w : 1 < p) (i : ℕ) : ((s i) : zmod (2^p - 1)) = s' p i :=
begin
  induction i with i ih,
  { dsimp [s, s'], norm_num, },
  { dsimp [s, s'],
    push_cast,
    rw ih, },
end


/- Lucas Lehmer Residue -/

def Lucas_Lehmer_residue (p : ℕ) := s' p (p-2)

/- Test for Primality -/

@[derive decidable_pred]
def Lucas_Lehmer_test (p : ℕ) := Lucas_Lehmer_residue p = 0

-- q is defined as the minimum factor of (M p)
def q (p : ℕ) : ℕ+ := ⟨min_fac (M p), by exact min_fac_pos (M p)⟩

/- X q : the group of tuples (a,b) taken modulo q, of the form a + (3)^(1/2) -/

@[derive add_comm_group]
def X (q : ℕ+) := (zmod q) × (zmod q)

namespace X
variable {q : ℕ+}

@[ext]
lemma ext {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y :=
begin
  cases x, cases y,
  congr; assumption
end

@[simp] lemma add_fst (x y : X q) : (x + y).1 = x.1 + y.1 := rfl
@[simp] lemma add_snd (x y : X q) : (x + y).2 = x.2 + y.2 := rfl

instance : has_mul (X q) :=
{ mul := λ x y, (x.1*y.1 + 3*x.2*y.2, x.1*y.2 + x.2*y.1) }

@[simp] lemma mul_fst (x y : X q) : (x * y).1 = x.1 * y.1 + 3 * x.2 * y.2 := rfl
@[simp] lemma mul_snd (x y : X q) : (x * y).2 = x.1 * y.2 + x.2 * y.1 := rfl

instance : has_one (X q) :=
{ one := ⟨1,0⟩ }

@[simp] lemma one_fst : (1 : X q).1 = 1 := rfl
@[simp] lemma one_snd : (1 : X q).2 = 0 := rfl

instance : monoid (X q) :=
{ mul_assoc := λ x y z, by { ext; { dsimp, ring }, },
  one := ⟨1,0⟩,
  one_mul := λ x, by { ext; simp, },
  mul_one := λ x, by { ext; simp, },
  ..(infer_instance : has_mul (X q)) }

lemma left_distrib (x y z : X q) : x * (y + z) = x * y + x * z :=
by { ext; { dsimp, ring }, }

lemma right_distrib (x y z : X q) : (x + y) * z = x * z + y * z :=
by { ext; { dsimp, ring }, }

instance : ring (X q) :=
{ left_distrib := left_distrib,
  right_distrib := right_distrib,
  ..(infer_instance : add_comm_group (X q)),
  ..(infer_instance : monoid (X q)) }

instance : comm_ring (X q) :=
{ mul_comm := λ x y, by { ext; { dsimp, ring }, },
  ..(infer_instance : ring (X q))}

instance fintype_zmod_pnat : fintype (zmod q) :=
begin
  rcases q with ⟨q,p⟩, cases q,
  { exfalso, cases p, },
  { dsimp [zmod],
    apply_instance, },
end

instance fintype_X : fintype (X q) :=
begin
  dsimp [X],
  apply_instance,
end

instance fact_pnat_pos : fact ((0 : ℕ) < q) :=
q.2

/-- The cardinality of the group `zmod q` is q. -/
lemma fin_zmod : fintype.card (zmod q) = q :=
by convert zmod.card q

/-- The cardinality of X is q^2. -/
lemma X_card : fintype.card (X q) = q^2 :=
begin
  dsimp [X],
  simp only [fintype.card_prod, fin_zmod],
  ring,
end


-- For the purpose of this we do not need to produce the list of units so leave as non-computable
noncomputable instance fintype_units : fintype (units (X q)) :=
fintype.of_injective (coe : units (X q) → (X q)) units.ext

/- The cardinality of the units is less than q^2.
Mathematically the cardinality of the units will be
less than or equal to the cardinality of X q. However 0 in X q,
is a known element without an inverse, thus the inequality holds.
-/
lemma units_card : fintype.card (units (X q)) < q^2 := sorry


def ω : X q := (2, 1)
def ωb : X q := (2, -1)

lemma val_inverse (q : ℕ+): (ω : X q) * ωb = 1 :=
begin
  dsimp [ω, ωb],
  ext; simp; ring,
end

lemma inverse_val (q : ℕ+): (ωb : X q) * ω = 1 :=
begin
  dsimp [ω, ωb],
  ext; simp; ring,
end

instance : has_coe ℤ (X q) :=
{ coe := λ n, (n, 0) }

@[simp]
lemma coe_fst (n : ℤ) : (n : X q).fst = n := rfl
@[simp]
lemma coe_snd (n : ℤ) : (n : X q).snd = 0 := rfl


@[norm_cast]
lemma coe_mul (n m : ℤ) : ((n * m : ℤ) : X q) = (n : X q) * (m : X q) :=
by { ext; simp; ring }

@[norm_cast]
lemma coe_nat (n : ℕ) : ((n : ℤ) : X q) = (n : X q) :=
begin
  induction n with n ih,
  { ext; refl, },
  { ext; simp [←ih], }
end

/- Closed form solution for the recurrence relation -/

lemma closed_form (i : ℕ) : (s i : X q) = (ω : X q)^(2^i) + (ωb : X q)^(2^i) :=
begin
  induction i with i ih,
  { dsimp[s, ω, ωb],
    ext; { dsimp, norm_num, }, },
  { calc (s (succ i) : X q) = (((s i)^2 - 2) : ℤ) : begin dsimp[s], refl, end
              ... = ((((s i) : X q) ^2 - 2)) : sorry /- the coercion from ↑(s i^2-2) to ↑(s i)^2-2 -/
              ... = (ω^(2^i) + ωb^(2^i))^2 - 2 : by rw ih
              ... = ω^(2^i)^2 + ωb^(2^i)^2 + 2*ωb^(2^i)*ω^(2^i) - 2 : sorry /- (a + b)^2 = a^2 + b^2 + 2*a*b -/
              ... = ω^(2^i)^2 + ωb^(2^i)^2 + 2*(ωb*ω)^(2^i) - 2 : sorry
              ... = ω^(2^i)^2 + ωb^(2^i)^2 + 2*1^(2^i) - 2 : by rw inverse_val
              ... = ω^(2^i)^2 + ωb^(2^i)^2 + 2*1 - 2 : by simp only [_root_.one_pow]
              ... = ω^(2^i)^2 + ωb^(2^i)^2 : by simp only [mul_one, add_sub_cancel]
              ... = ω^(2^i*2) + ωb^(2^i*2) : sorry /- (2^(2^i))^2 = (2^((2^i)+(2^i)) = 2^(2*(2^i)) -/
              ... = ω^(2^(succ i)) + ωb^(2^(succ i)) : sorry /- 2^i * 2 = 2^(i+1) -/ }
end


end X

open X
section residue_zero

@[simp]
lemma min_fac_eq_one_iff (n : ℕ) : min_fac n = 1 ↔ n = 1 := sorry
@[simp]
lemma min_fac_eq_two_iff (n : ℕ) : min_fac n = 2 ↔ 2 ∣ n := sorry

-- q is at least 2
lemma minimum_q {p : ℕ} (w : 1 < p) : 2 < q p := begin
  by_contradiction,
  simp at a,
  interval_cases q p; clear a,
  { dsimp [q] at h, injection h with h', clear h,
    simp [M] at h',
    sorry, },
  { dsimp [q] at h, injection h with h', clear h,
    simp [M] at h',
    sorry, }
end

lemma foo' {p : ℕ} (w : 1 < p) : 2^(p-1) = 2^(p-2) + 2^(p-2) :=
begin
  cases p,
  cases w,
  cases p,
  cases w with _ w, cases w,
  simp only [nat.sub_zero, succ_sub_succ_eq_sub],
  apply mul_two,
end

theorem multiple_k (p : ℕ) (w : 1 < p) (h : Lucas_Lehmer_residue p = 0) :
  ∃ (k : ℤ), (ω : X (q p))^(2^(p-1)) = k * (M p) * ((ω : X (q p))^(2^(p-2))) - 1 :=
begin
  dsimp [Lucas_Lehmer_residue] at h,
  rewrite ←s_eq_s' p w at h,
  replace h : ((2^p - 1 : ℕ) : ℤ) ∣ s (p-2) := sorry,
  cases h with k h,
  use k,
  replace h := congr_arg (λ (n : ℤ), (n : X (q p))) h, -- coercion from ℤ to X q
  dsimp at h,
  rewrite closed_form at h,
  dsimp [M],
  replace h := congr_arg (λ x, ω^2^(p-2) * x) h,
  dsimp at h,
  rw [mul_add, ←pow_add ω, ←foo' w, ←mul_pow ω ωb (2^(p-2)), val_inverse, _root_.one_pow] at h,
  rw [mul_comm, coe_mul] at h,
  rw [mul_comm _ (k : X (q p))] at h,
  replace h := eq_sub_of_add_eq h,
  push_cast at h,
  exact h,
end

/- This theorem holds as q is by definition the minimum factor of M p.sorry
As a multiple of q, M p evaluates to 0 mod q -/
theorem modulo_q (p : ℕ ) : ((M p) : X (q p)) = 0 := sorry

theorem sufficiency_simp (p : ℕ) (w : 1 < p) (h : Lucas_Lehmer_residue p = 0) : (ω : X (q p))^(2^(p-1)) = -1 :=
begin
  have w := multiple_k p w h,
  cases w with k w,
  rw [modulo_q] at w,
  simp at w,
  exact w,
end

/- This result is achieved by squaring the above equation.-/
theorem suff_squared (p : ℕ) (w : 1 < p) (h : Lucas_Lehmer_residue p = 0) :
  (ω : X (q p))^(2^p) = 1 :=
calc (ω : X (q p))^2^p = (ω^(2^(p-1)))^2 : sorry
         ... = (-1)^2                    : by rw sufficiency_simp _ w h
         ... = 1                         : by simp

def omega_unit (p : ℕ) : units (X (q p)) :=
{ val := ω,
  inv := ωb,
  val_inv := by simp [val_inverse],
  inv_val := by simp [inverse_val], }

@[simp] lemma omega_unit_coe (p : ℕ) : (omega_unit p : X (q p)) = ω := rfl

-- Coercion from omega_unit to X (q p)
lemma coercion (p : ℕ) (h : omega_unit p ^ 2 ^ (p - 1) = 1) : (ω : X (q p))^(2^(p-1)) = 1 :=
begin
 have := congr_arg (units.coe_hom (X (q p)) : units (X (q p)) → X (q p)) h,
 convert this,
 simp,
end

lemma mod_eq_one_or_two (q : ℕ+) (h : (2 : zmod q) = 0) : q = 1 ∨ q = 2 :=
begin
  have w : (2 : zmod q) = (2 : ℕ) := begin apply fin.eq_of_veq, simp, end,
  rw w at h,
  replace h := congr_arg fin.val h,
  rw zmod.val_cast_nat at h,
  simp at h,
  by_cases t : q ≤ 2,
  { -- case bashing
    rcases q with ⟨q,qp⟩,
    cases q, cases qp,
    cases q, left, refl,
    cases q, right, refl,
    cases t, dsimp at t_a, cases t_a, cases t_a_a, },
  { simp at t,
    have t' : 2 % ↑q = 2 := mod_eq_of_lt t,
    rw t' at h,
    cases h, }
end

-- the order of omega is 2^p
theorem order_omega (p : ℕ) (w : 1 < p) (h : Lucas_Lehmer_residue p = 0) :
  order_of (omega_unit p) = 2^p :=
begin
  have t : p = p - 1 + 1 := (nat.sub_eq_iff_eq_add sorry).mp rfl,
  conv { to_rhs, rw t },
  apply dvd_prime_power, -- the order of ω divides 2^p
  { norm_num, },
  { intro o,
    have ω_pow := coercion _ (order_of_dvd_iff.1 o),
    have h' := sufficiency_simp p w h,
    have h_2 := (ω_pow.symm).trans h',
    have h_3 := congr_arg (prod.fst) h_2,
    have h_4 : (1 : zmod (q p)) = -1 := h_3,
    have h_5 : (2 : zmod (q p)) = 0 :=
      calc 2 = (1 + 1 : zmod (q p))  : rfl
         ... = (1 + -1 : zmod (q p)) : by rw ←h_4
         ... = 0                     : add_neg_self 1,
    have h_6 : q p = 1 ∨ q p = 2 := mod_eq_one_or_two _ h_5,
    have h_7 : 2 < q p := minimum_q w,
    cases h_6,
    rw h_6 at h_7, cases h_7, cases h_7_a,
    rw h_6 at h_7, cases h_7, cases h_7_a, cases h_7_a_a, },
  { rw ←t,
    apply order_of_dvd_iff.2,
    apply units.ext,
    simp,
    exact (suff_squared _ w h), }
end

-- The order of an element is at most the size of the group.
lemma order_ineq (p : ℕ) (w : 1 < p) (h : Lucas_Lehmer_residue p = 0) : 2^p < (q p : ℕ)^2 :=
calc 2^p = order_of (omega_unit p)    : (order_omega _ w h).symm
     ... ≤ fintype.card (units (X _)) : order_of_le_card_univ
     ... < (q p : ℕ)^2                : units_card

end residue_zero

theorem final (p : ℕ) : Lucas_Lehmer_residue p = 0 → prime (M p) :=
begin
by_cases w : 1 < p,
{ contrapose,
  intros a t,
  have h₁ := order_ineq p w t,
  have h₂ := min_fac_sq (M p) (M_pos w) a,
  dsimp [q] at h₁,
  have h := lt_of_lt_of_le h₁ h₂,
  dsimp [M] at h,
  exfalso,
  exact not_lt_of_ge (nat.sub_le _ _) h, },
{ simp at w, subst w, intro h, cases h, }
end

theorem Lucas_Lehmer_sufficiency (p : ℕ) (pp : prime p) (h : p > 2) (w: Lucas_Lehmer_test p) : prime (M p) :=
begin
  dsimp [Lucas_Lehmer_test] at w,
  apply final p,
  exact w,
end

example : prime (M 5) := Lucas_Lehmer_sufficiency _ (by norm_num) (by norm_num) dec_trivial
