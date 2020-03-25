
import .nat
import data.nat.basic
import data.fin
import logic.basic

namespace nat

lemma sub_div {x y : ℕ} (h : y > 0) : (x - y) / y = x / y - 1 :=
begin
  apply eq_of_forall_le_iff, intro,
  cases le_or_gt y x with h' h',
  { have : 1 ≤ x / y, { simp [le_div_iff_mul_le,*], },
    simp [le_div_iff_mul_le,nat.le_sub_left_iff_add_le,right_distrib,*] },
  { rw [nat.sub_eq_zero_of_le,nat.div_eq_of_lt h,nat.div_eq_of_lt h'],
    apply le_of_lt h' }
end

end nat

open nat (hiding fact)

-- def fin.of_nat_pos {n} (hn : 0 < n) (i : ℕ) : fin n :=
-- ⟨i % n, nat.mod_lt _ hn⟩

-- @[simp]
-- lemma fin.val_of_nat_pos {n} (hn : 0 < n) (i : ℕ) :
--   (fin.of_nat_pos hn i).val = i % n := rfl

@[simp]
lemma fin.val_mod {n} (i : fin n) :
  i.val % n = i.val := nat.mod_eq_of_lt i.is_lt

-- @[class]
-- def fact (p : Prop) := p

instance fin.monoid {n} [hn : fact (0 < n)] : monoid (fin n) :=
{ one := fin.of_nat' 1,
  mul_one := λ x, fin.eq_of_veq $
  by { simp only [fin.mul_def,fin.val_of_nat_eq_mod']; rw [mod_mul_mod_right _ _ hn,mul_one,fin.val_mod], },
  one_mul := λ x, fin.eq_of_veq $
  by { simp only [fin.mul_def,fin.val_of_nat_eq_mod']; rw [mod_mul_mod_left _ _ hn,one_mul,fin.val_mod], },
  mul_assoc := λ a b c, fin.eq_of_veq $
  by { simp only [fin.mul_def,fin.val_of_nat_eq_mod']; rw [mod_mul_mod_left _ _ hn,mod_mul_mod_right _ _ hn,mul_assoc], },
  .. fin.has_mul }

instance fin.comm_monoid {n} [hn : fact (0 < n)] : comm_monoid (fin n) :=
{ mul_comm := by intros; ext; simp [fin.mul_def,mul_comm],
  .. fin.monoid }

instance of_nat.is_monoid_hom {n} [hn : fact (0 < n)] : is_monoid_hom (@fin.of_nat' n _) :=
{ map_one := by { intros, ext, refl },
  map_mul := by { intros, ext,
    rw fact at hn,
    simp [fin.mul_def,mod_mul_mod_left,mod_mul_mod_right,hn], } }
