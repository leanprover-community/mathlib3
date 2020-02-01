/- Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

Normalized linear integer arithmetic terms. -/

import tactic.omega.coeffs

namespace omega

/-- Shadow syntax of normalized terms. The first element
    represents the constant term and the list represents
    the coefficients. -/
def term : Type := int × list int

namespace term

/-- Evaluate a term using the valuation v. -/
@[simp] def val (v : nat → int) : term → int
| (b,as) := b + coeffs.val v as

@[simp] def neg : term → term
| (b,as) := (-b, list.func.neg as)

@[simp] def add : term → term → term
| (c1,cfs1) (c2,cfs2) := (c1+c2, list.func.add cfs1 cfs2)

@[simp] def sub : term → term → term
| (c1,cfs1) (c2,cfs2) := (c1 - c2, list.func.sub cfs1 cfs2)

@[simp] def mul (i : int) : term → term
| (b,as) := (i * b, as.map ((*) i))

@[simp] def div (i : int) : term → term
| (b,as) := (b/i, as.map (λ x, x / i))

lemma val_neg {v : nat → int} {t : term} :
(neg t).val v = -(t.val v) :=
begin
  cases t with b as,
  simp only [val, neg_add, neg, val, coeffs.val_neg]
end

@[simp] lemma val_sub {v : nat → int} {t1 t2 : term} :
(sub t1 t2).val v = t1.val v - t2.val v :=
begin
  cases t1, cases t2,
  simp only [add_assoc, coeffs.val_sub, neg_add_rev,
    val, sub, add_comm, add_left_comm, sub_eq_add_neg]
end

@[simp] lemma val_add {v : nat → int} {t1 t2 : term} :
(add t1 t2).val v = t1.val v + t2.val v :=
begin
  cases t1, cases t2,
  simp only [coeffs.val_add, add,
    val, add_comm, add_left_comm]
end

@[simp] lemma val_mul {v : nat → int} {i : int} {t : term} :
val v (mul i t) = i * (val v t) :=
begin
  cases t,
  simp only [mul, mul_add, add_mul, list.length_map,
    coeffs.val, coeffs.val_between_map_mul, val, list.map]
end

lemma val_div {v : nat → int} {i b : int} {as : list int} :
  i ∣ b → (∀ x ∈ as, i ∣ x) → (div i (b,as)).val v = (val v (b,as)) / i :=
begin
  intros h1 h2, simp only [val, div, list.map],
  rw [int.add_div_of_dvd h1 (coeffs.dvd_val h2)],
  apply fun_mono_2 rfl,
  rw ← coeffs.val_map_div h2
end

/-- Fresh de Brujin index not used by any variable ocurring in the term -/
def fresh_index (t : term) : nat := t.snd.length

def to_string (t : term) : string :=
t.2.enum.foldr (λ ⟨i, n⟩ r,
  to_string n ++ " * x" ++ to_string i ++ " + " ++ r) (to_string t.1)

instance : has_to_string term := ⟨to_string⟩

end term

/-- Fresh de Brujin index not used by any variable ocurring in the list of terms -/
def terms.fresh_index : list term → nat
| []      := 0
| (t::ts) := max t.fresh_index (terms.fresh_index ts)

end omega
