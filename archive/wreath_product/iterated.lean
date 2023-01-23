-- TODO: does it make sense to go directly into src/?
import .defs
import .imprimitive

import tactic.derive_fintype

open nat


universe u

@[derive inhabited, derive fintype]
inductive triv_group : Type u 
| e : triv_group

lemma triv_group.ext (a b : triv_group) : a = b := begin
  cases a,
  cases b,
  refl,
end

instance : group triv_group :=
{
  one := triv_group.e,
  mul := (λ a b, triv_group.e),
  inv := (λ a, triv_group.e),
  mul_assoc := (λ a b c, triv_group.ext _ _),
  one_mul := (λ a, triv_group.ext _ _),
  mul_one := (λ a, triv_group.ext _ _),
  mul_left_inv := (λ a, triv_group.ext _ _),
}

instance : has_smul triv_group triv_group := {
  smul := (λ a b, triv_group.e)
}

def iterated_wreath_product (G : Type u) (L : Type u) : ℕ → Type u
| zero := triv_group
| (succ n) := iterated_wreath_product n ≀[L] G

lemma iterated_wreath_product_zero (G : Type u) (L : Type u): iterated_wreath_product G L zero = triv_group := rfl

lemma iterated_wreath_product_succ (G : Type u) (L : Type u) (n : ℕ) : iterated_wreath_product G L (succ n) = (iterated_wreath_product G L n ≀[L] G) := rfl


instance (G : Type u) (L : Type u) [group G] [mul_action G L] (n : ℕ) : group (iterated_wreath_product G L n) :=
begin
  induction n with n ih,
  {
    rw iterated_wreath_product_zero,
    apply_instance
  },
  {
    rw iterated_wreath_product_succ,
    resetI,
    apply_instance,
  }
end

@[reducible]
def words (L : Type u) : ℕ → Type u
| 0 := triv_group
| (succ n) := words n × L

instance (L : Type u) [inhabited L] (n : ℕ) : inhabited (words L n) := begin
  induction n with n ih,
  {
    change inhabited triv_group,
    apply_instance,
  },
  {
    change inhabited (words L n × L),
    resetI,
    apply_instance,
  }
end


instance (L : Type u) [fintype L] (n : ℕ) : fintype (words L n) := begin
  induction n with n ih,
  {
    change fintype triv_group,
    apply_instance,
  },
  {
    change fintype (words L n × L),
    resetI,
    apply_instance,
  }
end

lemma words_card (L : Type u) [fintype L] (n : ℕ) : fintype.card (words L n) = (fintype.card L)^n :=
begin
  induction n with n ih,
  {
    refl,
  },
  {
    simp,
    rw ih,
    rw pow_succ,
    rw mul_comm,
  }
end

instance (G : Type u) (L : Type u) [group G] [mul_action G L] (n : ℕ) : mul_action (iterated_wreath_product G L n) (words L n) :=
begin
  induction n with n ih,
  {
    change mul_action (triv_group) (triv_group),
    apply_instance,
  },
  {
    change mul_action (iterated_wreath_product G L n ≀[L] G) (words L n × L),
    apply imprimitive,
    exact ih,
  }
end

instance faithful_iterated_wreath_product (G : Type u) (L : Type u) [group G] [mul_action G L] [inhabited L] (n : ℕ) [has_faithful_smul G L] : has_faithful_smul (iterated_wreath_product G L n) (words L n) :=
begin
  induction n with n ih,
  {
    change has_faithful_smul (triv_group) (triv_group),
    apply_instance,
  },
  {
    resetI,
    change has_faithful_smul (iterated_wreath_product G L n ≀[L] G) (words L n × L),
    apply imprimitive_faithful,
  }

end
