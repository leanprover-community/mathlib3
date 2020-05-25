import data.multiset

@[reducible] def free_comm_monoid (α : Type*) := multiplicative (multiset α)

namespace free_comm_monoid

section lift

variables {α : Type*} {M : Type*} [comm_monoid M]

def of (x : α) : free_comm_monoid α := multiplicative.of_add [x]

@[simp] lemma to_add_of (x : α) : (of x).to_add = [x] := rfl

@[elab_as_eliminator]
lemma induction_on (x : free_comm_monoid α) {p : free_comm_monoid α → Prop}
  (h1 : p 1) (h : ∀ x s, p s → p (of x * s)) :
  p x :=
multiset.induction_on x h1 h

@[ext] lemma hom_eq {f g : free_comm_monoid α →* M} (h : ∀ x : α, f (of x) = g (of x)) :
  f = g :=
monoid_hom.ext $ λ x, induction_on x (f.map_one.trans g.map_one.symm) $ λ a s hs, by simp [*]

def lift : (α → M) ≃ (free_comm_monoid α →* M) :=
{ to_fun := λ f, ⟨λ s, (s.to_add.map f).prod, rfl, λ x y, by simp⟩,
  inv_fun := λ f, f ∘ of,
  left_inv := λ f, funext $ λ x, multiset.prod_singleton _,
  right_inv := λ f, by { ext x, simp } }

@[simp] lemma lift_symm_apply (f : free_comm_monoid α →* M) :
  lift.symm f = f ∘ of := rfl

@[simp] lemma lift_eval_of (f : α → M) (x : α) : lift f (of x) = f x :=
lift.symm_apply_apply f

end lift

end free_comm_monoid
