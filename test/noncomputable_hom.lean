-- see note [inline attributes for morphisms]
-- None of the `example`s in this file should be made noncomputable by `A.add_zero_class`.

import algebra.hom.equiv
import algebra.group.prod
import algebra.group.pi

def A : Type* := ℕ
@[instance]
noncomputable constant A.add_zero_class : add_zero_class A

def ok : A ≃+ A :=
{ to_fun := id,
  inv_fun := id,
  left_inv := λ _, rfl,
  right_inv := λ _, rfl,
  map_add' := λ _ _, rfl }

example : A → A := ok
example : A ≃ A := ok.to_equiv
example : A ≃+ A := add_equiv.refl _
example : A ≃+ A := ok.trans ok
example : A ≃+ A := ok.symm
example : A →+ A := ok.to_add_monoid_hom
example : multiplicative A ≃* multiplicative A := ok.to_multiplicative

example : A × A →+ A := add_monoid_hom.fst _ _
example : A × A →+ A := add_monoid_hom.snd _ _
example : (ℕ → A) →+ A := pi.eval_add_monoid_hom _ 0
