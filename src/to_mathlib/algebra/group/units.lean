import algebra.group.units
import algebra.order.monoid.order_dual

open function

universe u
variable {α : Type u}

lemma is_unit.inf [monoid α] [linear_order α] {x y : α} (hx : is_unit x) (hy : is_unit y) :
  is_unit (x ⊓ y) :=
begin
  cases le_total x y with h;
  simp [h, hx, hy]
end

lemma is_unit.sup [monoid α] [linear_order α] {x y : α} (hx : is_unit x) (hy : is_unit y) :
  is_unit (x ⊔ y) :=
@is_unit.inf αᵒᵈ _ _ _ _  hx hy
