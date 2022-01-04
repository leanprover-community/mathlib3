
import tactic

-- import data.equiv.basic
-- import group_theory.perm.cycle_type
-- import group_theory.specific_groups.alternating

variables {M : Type*} [comm_monoid M]

lemma multiset.prod_pow_sum {m : multiset ℕ} {a : M} :
  (multiset.map (λ n, a^n) m).prod = a ^ (m.sum) :=
multiset.induction_on m (by simp) (λ n m h, by simp [h,pow_add])

lemma test3 {m : multiset ℕ} {f : ℕ →* M} :
  (multiset.map f m).prod = f (m.sum) :=
begin
  rw multiset.prod_hom ,
-- prove ⇑f m.prod = ⇑f m.sum
sorry,
end
