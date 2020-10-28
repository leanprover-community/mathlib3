import order.preorder_hom
import category_theory.sites.grothendieck

universes v u

namespace category_theory

variables {C : Type u} [category.{v} C]

structure closure_operator (α : Type*) [preorder α] extends α →ₘ α :=
(inflationary : ∀ x, x ≤ to_fun x)
(idem : ∀ x, to_fun (to_fun x) = to_fun x)
(order_preserving : ∀ x y, x ≤ y → to_fun x ≤ to_fun y)

instance {α : Type*} [preorder α] : has_coe_to_fun (closure_operator α) :=
⟨_, λ t, t.to_fun⟩

def natural_on_sieves (c : Π ⦃X : C⦄, closure_operator (sieve X)) : Prop :=
∀ {X Y : C} (f : Y ⟶ X) (S : sieve X), c (S.pullback f) = (c S).pullback f

#check subtype.prop
def natural_operator_equiv_topology :
  {c : Π ⦃X : C⦄, closure_operator (sieve X) // natural_on_sieves c} ≃ grothendieck_topology C :=
{ to_fun := λ c,
  { sieves := λ X S, (c : Π ⦃X : C⦄, closure_operator (sieve X)) S = ⊤,
    top_mem' := λ X,
    begin
      change _ = _,
      rw eq_top_iff,
      exact closure_operator.inflationary _ _,
    end,
    pullback_stable' := λ X Y S f hS,
    begin
      change _ = _ at hS,
      change _ = _,
      rw [c.prop f S, hS, sieve.pullback_top],
    end,
    transitive' := λ X S (hS : _ = _) R (hR : ∀ ⦃Y f⦄, S f → _ = _),
    begin
      change _ = _,
      have : S ≤ (c : Π ⦃X : C⦄, closure_operator (sieve X)) R,
        intros Y f hf,
        rw sieve.pullback_eq_top_iff_mem,
        rw ← c.prop,
        apply hR hf,
      rw eq_top_iff,
      rw ← hS,
      -- rw ← closure_operator.idem,

      -- have := closure_operator.order_preserving _ _ _ this,
      -- have : S ≤ c R,
      -- have : (∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → ((c : Π ⦃X : C⦄, closure_operator (sieve X)) R) f),
      --   intros Y f hf,
      --   rw sieve.pullback_eq_top_iff_mem,
      --   rw ← c.prop,
      --   apply hR, apply hf,

      -- change ∀ ⦃Y f⦄, _ → _ = _ at hR,
      -- apply le_antisymm,
      -- { intros Y g hg,

      --   -- have := (c.2 _ R),
      -- },
      -- { apply closure_operator.inflationary _ _ },
    end
  }

}
