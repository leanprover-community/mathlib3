import order.bounded_lattice -- for `pi` instances

variables {α β : Type*} [preorder α]

lemma monotone.sup [semilattice_sup β] {f g : α → β} (hf : monotone f) (hg : monotone g) :
  monotone (f ⊔ g) :=
λ x y h, sup_le_sup (hf h) (hg h)

lemma monotone.inf [semilattice_inf β] {f g : α → β} (hf : monotone f) (hg : monotone g) :
  monotone (f ⊓ g) :=
λ x y h, inf_le_inf (hf h) (hg h)

lemma monotone.max [linear_order β] {f g : α → β} (hf : monotone f) (hg : monotone g) :
  monotone (λ x, max (f x) (g x)) :=
hf.sup hg

lemma monotone.min [linear_order β] {f g : α → β} (hf : monotone f) (hg : monotone g) :
  monotone (λ x, min (f x) (g x)) :=
hf.inf hg
