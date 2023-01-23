import data.nat.pow
import group_theory.sylow
import logic.equiv.fin

import .iterated
import .fintype
import .sylow_mwe
import data.nat.factorization.basic

import data.nat.multiplicity

open nat


section card_computation
variables (p n : ℕ) 
  (G : Type*) [group G] [fintype G] [decidable_eq G]

instance : fintype (iterated_wreath_product G G n) := begin
  induction n with n ih,
  {
    change fintype triv_group,
    apply_instance,
  },
  {
    change fintype (iterated_wreath_product G G n ≀[G] G),
    resetI,
    apply_instance,
  }
end

@[simp]
lemma card_iterated_wreath_product_zero : fintype.card (iterated_wreath_product G G 0) = 1 := begin
  refl,
end


@[simp]
lemma card_iterated_wreath_product_succ : fintype.card (iterated_wreath_product G G (succ n)) = (fintype.card (iterated_wreath_product G G n))^(fintype.card G) * (fintype.card G) := begin
  change fintype.card (iterated_wreath_product G G n ≀[G] G) =
    fintype.card (iterated_wreath_product G G n) ^ fintype.card G * fintype.card G,
  rw wreath_product_card,
end

lemma part_enat_coe_smul (a b : ℕ) : (a • ↑b : part_enat) = ↑ (a * b) :=
begin
  induction a with a ih,
  {
    simp only [zero_smul, zero_mul, cast_zero]
  },
  {
    have succ_d: a.succ = a + 1, by refl,
    rw succ_d,
    rw [add_smul, add_mul],
    simp,
    rw ih,
  }
end

lemma multiplicity_pow_succ_factorial'  (pprime : nat.prime p) : multiplicity p (p ^ n.succ).factorial =  1 + p • multiplicity p (p ^ n).factorial := begin
  induction n with n ih,
  {
    rw pow_succ,
    rw nat.prime.multiplicity_factorial_mul pprime,
    simp,
    rw nat.prime.multiplicity_one pprime,
    simp,
  },
  {
    rw pow_succ,
    rw nat.prime.multiplicity_factorial_mul pprime,
    conv
      begin to_lhs,
      rewrite ih,
      end,
    rw pow_succ,
    rw nat.prime.multiplicity_factorial_mul pprime,
    simp,
    rw add_assoc,
    rw part_enat_coe_smul,
  }
end

lemma is_p_group.iterated_wreath_product
[fact (nat.prime p)]
(h : fintype.card G = p)
: is_p_group p (iterated_wreath_product G G n) := begin
  induction n with n ih,
  {
    rw is_p_group.iff_card,
    use 0,
    refl,
  },
  {
    rw is_p_group.iff_card at *,
    simp,
    cases ih with m eq_m,
    use (p * m + 1),
    rw [eq_m, h],
    rw [pow_add, ← pow_mul, pow_one, mul_comm m _],
  },
end

lemma iterated_wreath_product_multiplicity
[hp: fact (nat.prime p)]
(h : fintype.card G = p)
: multiplicity p (fintype.card (iterated_wreath_product G G n)) = multiplicity p (factorial (p^n)) :=
begin
  induction n with n ih,
  {
    refl,
  },
  {
    simp,
    rw multiplicity_pow_succ_factorial' p n hp.out,
    rw nat.prime.multiplicity_mul hp.out,
    rw nat.prime.multiplicity_pow hp.out,
    rw ih,
    rw h,
    rw nat.prime.multiplicity_self hp.out,
    rw add_comm,
  }
end

lemma iterated_wreath_product_card_p
[hp: fact (nat.prime p)]
(h : fintype.card G = p)
: fintype.card (iterated_wreath_product G G n) = p^nat.factorization (factorial (p^n)) p :=
begin
  obtain ⟨m, eq_m⟩ : ∃ m, fintype.card (iterated_wreath_product G G n) = p^m :=
  begin
    rw ← is_p_group.iff_card,
    apply is_p_group.iterated_wreath_product,
    exact h,
  end,
  rw eq_m,
  apply congr_arg2 _ rfl,
  rw ← part_enat.coe_inj,
  rw ← nat.prime.multiplicity_pow_self hp.out,
  rw ← eq_m,
  rw iterated_wreath_product_multiplicity _ _ _ h,
  apply nat.multiplicity_eq_factorization hp.out,
  apply nat.factorial_ne_zero,
end

end card_computation

noncomputable def sylow_perm_prime_power' (p n : ℕ) [hp: fact (nat.prime p)]
  (G : Type*) [group G] [fintype G] [decidable_eq G] (h : fintype.card G = p)
  : sylow p (equiv.perm (words G n)) :=
begin
  let a : mul_action (iterated_wreath_product G G n) (words G n) := infer_instance,
  let H : subgroup (equiv.perm (words G n)) := (subgroup.map (mul_action.to_perm_hom (iterated_wreath_product G G n) (words G n)) ⊤),
  classical,
  apply card_eq_multiplicity_to_sylow H,
  have eq_card : fintype.card H = fintype.card (iterated_wreath_product G G n)  :=
  begin
    apply fintype.card_congr,
    apply mul_equiv.to_equiv,
    symmetry,
    let foo := @subgroup.top_equiv (iterated_wreath_product G G n) _,
    apply mul_equiv.trans _ ,
    apply subgroup.equiv_map_of_injective,
    have : has_faithful_smul (iterated_wreath_product G G n) (words G n) := begin
      have : inhabited G := {default := 1},
      resetI,
      apply faithful_iterated_wreath_product,
    end,
    resetI,
    apply mul_action.to_perm_injective,
    symmetry,
    exact foo,
  end,
  rw eq_card,
  rw iterated_wreath_product_card_p p n,
  rw fintype.card_perm,
  rw words_card,
  rw h,
  exact h,
  exact hp,
end


noncomputable lemma sylow_perm_prime_power (p n : ℕ) [fact (nat.prime p)]
  (G : Type*) [group G] [fintype G] [decidable_eq G] (h : fintype.card G = p)
  (P : sylow p (equiv.perm (fin (p^n)))) : ↥P ≃* iterated_wreath_product G G n :=begin
  sorry
end
