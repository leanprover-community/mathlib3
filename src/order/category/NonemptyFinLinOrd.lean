/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import data.fintype.order
import data.set.finite
import order.category.LinearOrder
import category_theory.limits.shapes.images
import category_theory.limits.shapes.regular_mono

/-!
# Nonempty finite linear orders

This defines `NonemptyFinLinOrd`, the category of nonempty finite linear orders with monotone maps.
This is the index category for simplicial objects.
-/

universes u v

open category_theory category_theory.limits

/-- A typeclass for nonempty finite linear orders. -/
class nonempty_fin_lin_ord (α : Type*) extends fintype α, linear_order α :=
(nonempty : nonempty α . tactic.apply_instance)

attribute [instance] nonempty_fin_lin_ord.nonempty

@[priority 100]
instance nonempty_fin_lin_ord.to_bounded_order (α : Type*) [nonempty_fin_lin_ord α] :
  bounded_order α :=
fintype.to_bounded_order α

instance punit.nonempty_fin_lin_ord : nonempty_fin_lin_ord punit := { }

instance fin.nonempty_fin_lin_ord (n : ℕ) : nonempty_fin_lin_ord (fin (n+1)) := { }

instance ulift.nonempty_fin_lin_ord (α : Type u) [nonempty_fin_lin_ord α] :
  nonempty_fin_lin_ord (ulift.{v} α) :=
{ .. linear_order.lift' equiv.ulift (equiv.injective _) }

instance (α : Type*) [nonempty_fin_lin_ord α] : nonempty_fin_lin_ord αᵒᵈ :=
{ ..order_dual.fintype α }

/-- The category of nonempty finite linear orders. -/
def NonemptyFinLinOrd := bundled nonempty_fin_lin_ord

namespace NonemptyFinLinOrd

instance : bundled_hom.parent_projection @nonempty_fin_lin_ord.to_linear_order := ⟨⟩

attribute [derive [large_category, concrete_category]] NonemptyFinLinOrd

instance : has_coe_to_sort NonemptyFinLinOrd Type* := bundled.has_coe_to_sort

/-- Construct a bundled `NonemptyFinLinOrd` from the underlying type and typeclass. -/
def of (α : Type*) [nonempty_fin_lin_ord α] : NonemptyFinLinOrd := bundled.of α

@[simp] lemma coe_of (α : Type*) [nonempty_fin_lin_ord α] : ↥(of α) = α := rfl

instance : inhabited NonemptyFinLinOrd := ⟨of punit⟩

instance (α : NonemptyFinLinOrd) : nonempty_fin_lin_ord α := α.str

instance has_forget_to_LinearOrder : has_forget₂ NonemptyFinLinOrd LinearOrder :=
bundled_hom.forget₂ _ _

/-- Constructs an equivalence between nonempty finite linear orders from an order isomorphism
between them. -/
@[simps] def iso.mk {α β : NonemptyFinLinOrd.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply x },
  inv_hom_id' := by { ext, exact e.apply_symm_apply x } }

/-- `order_dual` as a functor. -/
@[simps] def dual : NonemptyFinLinOrd ⥤ NonemptyFinLinOrd :=
{ obj := λ X, of Xᵒᵈ, map := λ X Y, order_hom.dual }

/-- The equivalence between `FinPartialOrder` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : NonemptyFinLinOrd ≌ NonemptyFinLinOrd :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

lemma mono_iff_injective {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B) :
  mono f ↔ function.injective f :=
begin
  refine ⟨_, concrete_category.mono_of_injective f⟩,
  introI,
  intros a₁ a₂ h,
  let X : NonemptyFinLinOrd.{u} := ⟨ulift (fin 1)⟩,
  let g₁ : X ⟶ A := ⟨λ x, a₁, λ x₁ x₂ h, by refl⟩,
  let g₂ : X ⟶ A := ⟨λ x, a₂, λ x₁ x₂ h, by refl⟩,
  change g₁ (ulift.up (0 : fin 1)) = g₂ (ulift.up (0 : fin 1)),
  have eq : g₁ ≫ f = g₂ ≫ f := by { ext x, exact h, },
  rw cancel_mono at eq,
  rw eq,
end

lemma epi_iff_surjective {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B) :
  epi f ↔ function.surjective f :=
begin
  split,
  { introI,
    by_contra' hf',
    rcases hf' with ⟨m, hm⟩,
    let Y : NonemptyFinLinOrd.{u} := ⟨ulift (fin 2)⟩,
    let p₁ : B ⟶ Y := ⟨λ b, if b < m then ulift.up 0 else ulift.up 1, λ x₁ x₂ h, begin
      simp only,
      split_ifs with h₁ h₂ h₂,
      any_goals { apply fin.zero_le, },
      { exfalso,
        exact h₁ (lt_of_le_of_lt h h₂), },
      { refl, },
    end⟩,
    let p₂ : B ⟶ Y := ⟨λ b, if b ≤ m then ulift.up 0 else ulift.up 1, λ x₁ x₂ h, begin
      simp only,
      split_ifs with h₁ h₂ h₂,
      any_goals { apply fin.zero_le, },
      { exfalso,
        exact h₁ (h.trans h₂), },
      { refl, },
    end⟩,
    have h : p₁ m = p₂ m,
    { congr,
      rw ← cancel_epi f,
      ext a : 2,
      simp only [comp_apply, order_hom.coe_fun_mk],
      split_ifs with h₁ h₂ h₂,
      any_goals { refl, },
      { exfalso, exact h₂ (le_of_lt h₁), },
      { exfalso, exact hm a (eq_of_le_of_not_lt h₂ h₁), }, },
    simpa only [order_hom.coe_fun_mk, lt_self_iff_false, if_false, le_refl, if_true,
      ulift.up_inj, fin.one_eq_zero_iff, nat.succ_succ_ne_one] using h, },
  { intro h,
    exact concrete_category.epi_of_surjective f h, },
end

instance : split_epi_category NonemptyFinLinOrd.{u} :=
⟨λ X Y f hf, begin
  have H : ∀ (y : Y), nonempty (f⁻¹' { y }),
  { rw epi_iff_surjective at hf,
    intro y,
    exact nonempty.intro ⟨(hf y).some, (hf y).some_spec⟩, },
  let φ : Y → X := λ y, (H y).some.1,
  have hφ : ∀ (y : Y), f (φ y) = y := λ y, (H y).some.2,
  refine is_split_epi.mk' ⟨⟨φ, _⟩, _⟩, swap,
  { ext b,
    apply hφ, },
  { intros a b,
    contrapose,
    intro h,
    simp only [not_le] at h ⊢,
    suffices : b ≤ a,
    { apply lt_of_le_of_ne this,
      intro h',
      exfalso,
      simpa only [h', lt_self_iff_false] using h, },
    simpa only [hφ] using f.monotone (le_of_lt h), },
end⟩

instance : has_strong_epi_mono_factorisations NonemptyFinLinOrd.{u} :=
⟨λ X Y f, begin
  let I : NonemptyFinLinOrd.{u} := ⟨set.image (coe_fn f) ⊤, ⟨⟩⟩,
  let e : X ⟶ I := ⟨λ x, ⟨f x, ⟨x, by tidy⟩⟩, λ x₁ x₂ h, f.monotone h⟩,
  let m : I ⟶ Y := ⟨λ y, y, by tidy⟩,
  haveI : epi e := by { rw epi_iff_surjective, tidy, },
  haveI : strong_epi e := strong_epi_of_epi e,
  haveI : mono m := concrete_category.mono_of_injective _ (by tidy),
  exact nonempty.intro
  { I := I,
    m := m,
    e := e, },
end⟩

end NonemptyFinLinOrd

lemma NonemptyFinLinOrd_dual_comp_forget_to_LinearOrder :
  NonemptyFinLinOrd.dual ⋙ forget₂ NonemptyFinLinOrd LinearOrder =
    forget₂ NonemptyFinLinOrd LinearOrder ⋙ LinearOrder.dual := rfl
