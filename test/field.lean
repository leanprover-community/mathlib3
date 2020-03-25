
import algebra.group_power
import data.nat.parity
import system.random.basic
import .nat

namespace int

variables {i : ℤ} {n : ℕ}

lemma le_sub_iff_add_le (c x y : ℤ) : x ≤ y - c ↔ x + c ≤ y :=
begin
  split; intro h,
  { suffices : x + c + -c ≤ y + (-c), from le_of_add_le_add_right this,
    rwa [add_neg_cancel_right,← sub_eq_add_neg], },
  { suffices : x + c ≤ y - c + c, from le_of_add_le_add_right this,
    rwa [sub_add_cancel], },
end

lemma abs_eq_self_of_nn (hi : 0 ≤ i) : abs i = i :=
begin
  rw abs, apply le_antisymm,
  { rw max_le_iff, refine ⟨le_refl _, le_trans _ hi⟩,
    replace hi := neg_le_neg hi, rw neg_zero at hi, exact hi },
  { apply le_of_forall_le', simp [max_le_iff],
    intros, assumption }
end

lemma nat_abs_mod_lt [h : fact (0 < n)] : int.nat_abs (i % ↑n) < n :=
int.lt_of_coe_nat_lt_coe_nat $
  by { rw [← int.abs_eq_nat_abs,int.abs_eq_self_of_nn], apply int.mod_lt_of_pos,
       exact int.coe_nat_lt.2 h,
       rw [int.mod_def,int.le_sub_iff_add_le,zero_add,mul_comm,← int.le_div_iff_mul_le],
       rw ← int.coe_nat_lt at h, exact h }

lemma nat_abs_coe_eq_self (n : ℕ) : nat_abs n = n := rfl

lemma mod_mul_mod (p q n : ℤ) : p * (q % n) % n = p * q % n :=
begin
  have h₀ := eq_sub_of_add_eq (mod_add_div q n),
  rw [int.mod_eq_mod_iff_mod_sub_eq_zero,← dvd_iff_mod_eq_zero,← mul_sub,h₀],
  rw [sub_sub,add_comm,← sub_sub,sub_self,zero_sub,neg_mul_eq_mul_neg],
  rw [mul_comm n,← mul_assoc], apply dvd_mul_left
end

end int


variables {n : ℕ}

namespace fin

def of_int [h : fact (0 < n)] (i : ℤ) : fin n :=
⟨(i % n).nat_abs, int.nat_abs_mod_lt⟩

@[simp]
lemma val_of_int (h : fact (0 < n)) (i : ℤ) : (of_int i : fin n).val = (i % n).nat_abs :=
rfl

end fin

namespace fin
open int nat

def inv' (p : fin n) : fin n :=
let x := gcd_a p.val n in
@fin.of_int _ (lt_of_le_of_lt (nat.zero_le _) p.is_lt) x

def neg (p : fin n) : fin n :=
@fin.of_nat' _ (lt_of_le_of_lt (nat.zero_le _) p.is_lt) (n - p.val)
-- ⟨ n - p.val, nat.sub_lt _ p.is_lt ⟩

instance fact_pos [h : fact (1 < n)] : fact (0 < n) :=
lt_trans dec_trivial h

instance fact_one_lt_of_prime [h : fact (prime n)] : fact (1 < n) :=
prime.one_lt h

instance fin.has_zero' {n} [h : fact (0 < n)] : has_zero (fin n) :=
{ zero := ⟨0,h⟩ }

instance has_one' [fact (0 < n)] : has_one (fin n) :=
{ one := fin.of_nat' 1 }

def inv [fact (0 < n)] (p : fin n) : fin n :=
if p = 0 then 0
else inv' p

@[simp]
lemma zero_def'  {n} [h : fact (0 < n)] : (0 : fin n).val = 0 := rfl

@[simp]
lemma one_def'  {n} [h : fact (1 < n)] : (1 : fin n).val = 1 :=
nat.mod_eq_of_lt h

lemma fin.mul_comm (a b : fin n) : a * b = b * a :=
by ext; simp [fin.mul_def,mul_comm]

lemma inv_mul_of_coprimes [h : fact (1 < n)] (p : fin n) (hp : coprime p.val n) :
  inv' p * p = 1 :=
begin
  apply eq_of_veq, simp [mul_def,inv'],
  have := gcd_eq_gcd_ab p.val n,
  rw mul_comm,
  replace this : ↑(nat.gcd p.val n) - ↑n * gcd_b p.val n = ↑(p.val) * gcd_a p.val n,
  { rw [this,add_sub_cancel], },
  { rw [← int.coe_nat_eq_coe_nat_iff,coe_nat_mod,int.coe_nat_mul,← abs_eq_nat_abs,abs_eq_self_of_nn,mod_mul_mod,← this,← neg_add_eq_sub],
    rw coprime at hp,
    rw [neg_mul_eq_mul_neg,add_comm,mul_comm,int.add_mul_mod_self,hp,int.mod_eq_of_lt],
    { simp [has_one.one] },
    { erw coe_nat_lt_coe_nat_iff, apply h },
    { apply int.mod_nonneg, apply ne_of_gt,
      erw [(>),coe_nat_lt_coe_nat_iff],
      apply lt_trans (dec_trivial : 0 < 1) h } }
end

lemma mul_inv_cancel [h : fact (prime n)] (p : fin n) (hp : p ≠ 0) :
  p * inv p = 1 :=
begin
  rw [inv,if_neg hp],
  rw [fin.mul_comm,inv_mul_of_coprimes],
  apply coprime.symm ((prime.coprime_iff_not_dvd h).2 _),
  intro h', cases h' with x hx,
  apply hp, apply fin.eq_of_veq, simp ,
  have := p.is_lt, rw hx at this ⊢,
  clear_except this,
  have : n * x < n * 1, rwa mul_one,
  replace this := lt_of_mul_lt_mul_left this (nat.zero_le n),
  replace this := le_antisymm (le_of_lt_succ this) (nat.zero_le x),
  simp only [this, mul_zero]
end

lemma inv_zero [h : fact (0 < n)] :
  inv (0 : fin n) = 0 :=
by simp only [inv, if_true, eq_self_iff_true]

end fin


-- #eval (fin.inv 3 : fin 7)
-- #eval (fin.inv 3 * 5 : fin 7)

-- #exit


-- instance {n} [h : fact (1 < n)] : group (pfin n) :=
-- { one := ⟨@fin.of_nat' n (lt_trans dec_trivial h) 1, by simp * ⟩,
--   mul := λ x y, ⟨x.val * y.val, _⟩ }

instance {n} [h : fact (1 < n)] : monoid (fin n) :=
{ one := 1,
  mul := (*),
  mul_one := by { intros; ext; simp only [nat.mod_eq_of_lt h,nat.mod_eq_of_lt a.is_lt,fin.mul_def,fin.one_def',mul_one], },
  one_mul := by { intros; ext, simp only [nat.mod_eq_of_lt h,nat.mod_eq_of_lt a.is_lt,fin.mul_def,fin.one_def',one_mul], },
  mul_assoc := by haveI h' : fact (0 < n) := lt_trans dec_trivial h;
                  intros; ext; simp only [nat.mod_eq_of_lt,a.is_lt,nat.mod_mul_mod_left _ _ h',
                  nat.mod_mul_mod_right _ _ h',fin.mul_def,mul_assoc] }

instance {n} [h : fact (0 < n)] : add_comm_monoid (fin n) :=
{ zero := 0,
  add := (+),
  add_zero := by { intros; ext; simp only [nat.mod_eq_of_lt,a.is_lt,fin.add_def,add_zero,fin.zero_def'] },
  zero_add := by { intros; ext; simp only [nat.mod_eq_of_lt,a.is_lt,fin.add_def,zero_add,fin.zero_def'] },
  add_assoc := by intros; ext; simp only [nat.mod_eq_of_lt,a.is_lt,nat.mod_add_mod_left _ _ h,
                  nat.mod_add_mod_right _ _ h,fin.add_def,add_assoc],
  add_comm := by intros; ext; simp only [nat.mod_eq_of_lt,a.is_lt,nat.mod_add_mod_left _ _ h,
                  nat.mod_add_mod_right _ _ h,fin.add_def,add_comm],
 }

instance [h : fact (0 < n)] : has_neg  (fin n) :=
⟨ fin.neg ⟩

section

variables [h₀ : fact (0 < n)] (a b c : fin n)
include h₀
lemma fin.left_distrib : a * (b + c) = a * b + a * c :=
begin
  intros; ext,
  simp [nat.mod_eq_of_lt,a.is_lt,fin.add_def,fin.mul_def,monoid.mul,add_comm_monoid.add],
  simp [nat.mod_mul_mod_right _ _ h₀,nat.mod_add_mod_right _ _ h₀,nat.mod_add_mod_left _ _ h₀],
  simp [left_distrib]
end

lemma fin.right_distrib : (a + b) * c = a * c + b * c :=
begin
  intros; ext,
  simp [nat.mod_eq_of_lt,a.is_lt,fin.add_def,fin.mul_def,monoid.mul,add_comm_monoid.add],
  simp [nat.mod_mul_mod_left _ _ h₀,nat.mod_add_mod_right _ _ h₀,nat.mod_add_mod_left _ _ h₀],
  simp [right_distrib],
end

lemma fin.neg_def (a : fin n) : (-a).val = (n - a.val) % n := rfl

lemma fin.add_left_neg (a : fin n) : -a + a = 0 :=
begin
  intros; ext,
  simp only [fin.add_def, fin.neg_def, nat.mod_add_mod_left _ _ h₀, fin.zero_def'],
  rw [nat.sub_add_cancel,nat.mod_self],
  apply le_of_lt a.is_lt,
end

lemma fin.mul_comm (a b : fin n) : a * b = b * a :=
by ext; simp [fin.mul_def,mul_comm]

end

instance {n} [h : fact (1 < n)] : ring (fin n) :=
{ neg := fin.neg,
  left_distrib := fin.left_distrib,
  right_distrib := fin.right_distrib,
  add_left_neg := fin.add_left_neg,
  .. fin.add_comm_monoid,
  .. fin.monoid,
  .. fin.has_neg }

instance {n} [h : fact (1 < n)] : comm_ring (fin n) :=
{ mul_comm := fin.mul_comm,
  .. fin.ring }

instance {n} [h : fact (nat.prime n)] : field (fin n) :=
{ one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  inv := fin.inv,
  mul_inv_cancel := fin.mul_inv_cancel,
  inv_zero := fin.inv_zero,
  zero_ne_one := by simp [(≠),fin.ext_iff],
  .. fin.comm_ring }
