/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import category_theory.adjunction.opposites
import order.category.BoundedOrder
import order.category.Lattice

/-!
# The category of bounded lattices

This file defines `BoundedLattice`, the category of bounded lattices.

In literature, this is sometimes called `Lat`, the category of lattices, because being a lattice is
understood to entail having a bottom and a top element.
-/

universes u

open category_theory

/-- The category of bounded lattices with bounded lattice morphisms. -/
structure BoundedLattice :=
(to_Lattice : Lattice)
[is_bounded_order : bounded_order to_Lattice]

namespace BoundedLattice

instance : has_coe_to_sort BoundedLattice Type* := ⟨λ X, X.to_Lattice⟩
instance (X : BoundedLattice) : lattice X := X.to_Lattice.str

attribute [instance] BoundedLattice.is_bounded_order

/-- Construct a bundled `BoundedLattice` from `lattice` + `bounded_order`. -/
def of (α : Type*) [lattice α] [bounded_order α] : BoundedLattice := ⟨⟨α⟩⟩

@[simp] lemma coe_of (α : Type*) [lattice α] [bounded_order α] : ↥(of α) = α := rfl

instance : inhabited BoundedLattice := ⟨of punit⟩

instance : large_category.{u} BoundedLattice :=
{ hom := λ X Y, bounded_lattice_hom X Y,
  id := λ X, bounded_lattice_hom.id X,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, bounded_lattice_hom.comp_id,
  comp_id' := λ X Y, bounded_lattice_hom.id_comp,
  assoc' := λ W X Y Z _ _ _, bounded_lattice_hom.comp_assoc _ _ _ }

instance : concrete_category BoundedLattice :=
{ forget := ⟨coe_sort, λ X Y, coe_fn, λ X, rfl, λ X Y Z f g, rfl⟩,
  forget_faithful := ⟨λ X Y, by convert fun_like.coe_injective⟩ }

instance has_forget_to_Lattice : has_forget₂ BoundedLattice Lattice :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y, bounded_lattice_hom.to_lattice_hom } }

instance has_forget_to_BoundedOrder : has_forget₂ BoundedLattice BoundedOrder :=
{ forget₂ := { obj := λ X, BoundedOrder.of X,
               map := λ X Y, bounded_lattice_hom.to_bounded_order_hom } }

lemma forget_Lattice_PartialOrder_eq_forget_BoundedOrder_PartialOrder :
  forget₂ BoundedLattice Lattice ⋙ forget₂ Lattice PartialOrder =
    forget₂ BoundedLattice BoundedOrder ⋙ forget₂ BoundedOrder PartialOrder := rfl

/-- Constructs an equivalence between bounded lattices from an order isomorphism
between them. -/
@[simps] def iso.mk {α β : BoundedLattice.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : BoundedLattice ⥤ BoundedLattice :=
{ obj := λ X, of (order_dual X), map := λ X Y, bounded_lattice_hom.dual }

/-- The equivalence between `BoundedLattice` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : BoundedLattice ≌ BoundedLattice :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end BoundedLattice

lemma BoundedLattice_dual_comp_forget_to_Lattice :
  BoundedLattice.dual ⋙ forget₂ BoundedLattice Lattice =
    forget₂ BoundedLattice Lattice ⋙ Lattice.dual := rfl

lemma BoundedLattice_dual_comp_forget_to_BoundedOrder :
  BoundedLattice.dual ⋙ forget₂ BoundedLattice BoundedOrder =
    forget₂ BoundedLattice BoundedOrder ⋙ BoundedOrder.dual := rfl

namespace sup_hom
variables {α β γ : Type*} [semilattice_sup α] [semilattice_sup β] [semilattice_sup γ]

@[simps] protected def with_top (f : sup_hom α β) : sup_hom (with_top α) (with_top β) :=
{ to_fun := option.map f,
  map_sup' := begin
    rintro (_ | a) b,
    { refl },
    cases b,
    { refl },
    { exact congr_arg _ (f.map_sup' _ _) }
  end }

@[simp] lemma with_top_id : (sup_hom.id α).with_top = sup_hom.id _ :=
fun_like.coe_injective option.map_id

@[simp] lemma with_top_comp (f : sup_hom β γ) (g : sup_hom α β) :
  (f.comp g).with_top = f.with_top.comp g.with_top :=
fun_like.coe_injective (option.map_comp_map _ _).symm

@[simps] protected def with_bot (f : sup_hom α β) : sup_hom (with_bot α) (with_bot β) :=
{ to_fun := option.map f,
  map_sup' := begin
    rintro (_ | a) (_ | b),
    { refl },
    { refl },
    { refl },
    { exact congr_arg _ (f.map_sup' _ _) }
  end }

@[simp] lemma with_bot_id : (sup_hom.id α).with_bot = sup_hom.id _ :=
fun_like.coe_injective option.map_id

@[simp] lemma with_bot_comp (f : sup_hom β γ) (g : sup_hom α β) :
  (f.comp g).with_bot = f.with_bot.comp g.with_bot :=
fun_like.coe_injective (option.map_comp_map _ _).symm

@[simps] def with_top' [order_top β] (f : sup_hom α β) : sup_hom (with_top α) β :=
{ to_fun := λ a, a.elim ⊤ f,
  map_sup' := λ a b, match a, b with
    | none, none := by simp only [sup_idem]
    | none, some b := begin
        simp only [with_bot.none_eq_bot, option.elim, bot_inf_eq],
        exact top_sup_eq.symm,
      end
    | some a, none := begin
        simp only [with_bot.none_eq_bot, option.elim, bot_inf_eq],
        exact sup_top_eq.symm,
      end
    | some a, some b := f.map_sup' _ _
  end }

@[simps] def with_bot' [order_bot β] (f : sup_hom α β) : sup_hom (with_bot α) β :=
{ to_fun := λ a, a.elim ⊥ f,
  map_sup' := λ a b, match a, b with
    | none, none := bot_sup_eq.symm
    | none, some b := bot_sup_eq.symm
    | some a, none := by { rw [with_bot.none_eq_bot, sup_bot_eq], exact sup_bot_eq.symm }
    | some a, some b := f.map_sup' _ _
  end }

end sup_hom

namespace inf_hom
variables {α β γ : Type*} [semilattice_inf α] [semilattice_inf β] [semilattice_inf γ]

@[simps] protected def with_top (f : inf_hom α β) : inf_hom (with_top α) (with_top β) :=
{ to_fun := option.map f,
  map_inf' := begin
    rintro (_ | a) (_ | b),
    { refl },
    { refl },
    { refl },
    { exact congr_arg _ (f.map_inf' _ _) }
  end }

@[simp] lemma with_top_id : (inf_hom.id α).with_top = inf_hom.id _ :=
fun_like.coe_injective option.map_id

@[simp] lemma with_top_comp (f : inf_hom β γ) (g : inf_hom α β) :
  (f.comp g).with_top = f.with_top.comp g.with_top :=
fun_like.coe_injective (option.map_comp_map _ _).symm

@[simps] protected def with_bot (f : inf_hom α β) : inf_hom (with_bot α) (with_bot β) :=
{ to_fun := option.map f,
  map_inf' := begin
    rintro (_ | a) b,
    { refl },
    cases b,
    { refl },
    { exact congr_arg _ (f.map_inf' _ _) }
  end }

@[simp] lemma with_bot_id : (inf_hom.id α).with_bot = inf_hom.id _ :=
fun_like.coe_injective option.map_id

@[simp] lemma with_bot_comp (f : inf_hom β γ) (g : inf_hom α β) :
  (f.comp g).with_bot = f.with_bot.comp g.with_bot :=
fun_like.coe_injective (option.map_comp_map _ _).symm

@[simps] def with_top' [order_top β] (f : inf_hom α β) : inf_hom (with_top α) β :=
{ to_fun := λ a, a.elim ⊤ f,
  map_inf' := λ a b, match a, b with
    | none, none := top_inf_eq.symm
    | none, some b := top_inf_eq.symm
    | some a, none := by { rw [with_top.none_eq_top, inf_top_eq], exact inf_top_eq.symm }
    | some a, some b := f.map_inf' _ _
  end }

@[simps] def with_bot' [order_bot β] (f : inf_hom α β) : inf_hom (with_bot α) β :=
{ to_fun := λ a, a.elim ⊥ f,
  map_inf' := λ a b, match a, b with
    | none, none := by simp only [inf_idem]
    | none, some b := begin
        simp only [with_bot.none_eq_bot, option.elim, bot_inf_eq],
        exact bot_inf_eq.symm,
      end
    | some a, none := begin
        simp only [with_bot.none_eq_bot, option.elim, bot_inf_eq],
        exact inf_bot_eq.symm,
      end
    | some a, some b := f.map_inf' _ _
  end }

end inf_hom

namespace lattice_hom
variables {α β γ : Type*} [lattice α] [lattice β] [lattice γ]

@[simps] protected def with_top (f : lattice_hom α β) : lattice_hom (with_top α) (with_top β) :=
{ ..f.to_sup_hom.with_top, ..f.to_inf_hom.with_top }

@[simp] lemma with_top_id : (lattice_hom.id α).with_top = lattice_hom.id _ :=
fun_like.coe_injective option.map_id

@[simp] lemma with_top_comp (f : lattice_hom β γ) (g : lattice_hom α β) :
  (f.comp g).with_top = f.with_top.comp g.with_top :=
fun_like.coe_injective (option.map_comp_map _ _).symm

@[simps] protected def with_bot (f : lattice_hom α β) : lattice_hom (with_bot α) (with_bot β) :=
{ ..f.to_sup_hom.with_bot, ..f.to_inf_hom.with_bot }

@[simp] lemma with_bot_id : (lattice_hom.id α).with_bot = lattice_hom.id _ :=
fun_like.coe_injective option.map_id

@[simp] lemma with_bot_comp (f : lattice_hom β γ) (g : lattice_hom α β) :
  (f.comp g).with_bot = f.with_bot.comp g.with_bot :=
fun_like.coe_injective (option.map_comp_map _ _).symm

@[simps] def with_top_with_bot (f : lattice_hom α β) :
  bounded_lattice_hom (with_top $ with_bot α) (with_top $ with_bot β) :=
{ to_lattice_hom := f.with_bot.with_top, map_top' := rfl, map_bot' := rfl }

@[simp] lemma with_top_with_bot_id :
  (lattice_hom.id α).with_top_with_bot = bounded_lattice_hom.id _ :=
fun_like.coe_injective $ begin
  refine (congr_arg option.map _).trans option.map_id,
  rw with_bot_id,
  refl,
end

@[simp] lemma with_top_with_bot_comp (f : lattice_hom β γ) (g : lattice_hom α β) :
  (f.comp g).with_top_with_bot = f.with_top_with_bot.comp g.with_top_with_bot :=
fun_like.coe_injective $ (congr_arg option.map $ (option.map_comp_map _ _).symm).trans
  (option.map_comp_map _ _).symm

@[simps] def with_top' [order_top β] (f : lattice_hom α β) : lattice_hom (with_top α) β :=
{ ..f.to_sup_hom.with_top', ..f.to_inf_hom.with_top' }

@[simps] def with_bot' [order_bot β] (f : lattice_hom α β) : lattice_hom (with_bot α) β :=
{ ..f.to_sup_hom.with_bot', ..f.to_inf_hom.with_bot' }

@[simps] def with_top_with_bot' [bounded_order β] (f : lattice_hom α β) :
  bounded_lattice_hom (with_top $ with_bot α) β :=
{ to_lattice_hom := f.with_bot'.with_top', map_top' := rfl, map_bot' := rfl }

end lattice_hom

/--  The functor that adds a bottom and a top element to a lattice. This is the free functor. -/
def Lattice_to_BoundedLattice : Lattice.{u} ⥤ BoundedLattice :=
{ obj := λ X, BoundedLattice.of $ with_top $ with_bot X,
  map := λ X Y, lattice_hom.with_top_with_bot,
  map_id' := λ X, lattice_hom.with_top_with_bot_id,
  map_comp' := λ X Y Z _ _, lattice_hom.with_top_with_bot_comp _ _ }

/-- `Lattice_to_BoundedLattice` is left adjoint to the forgetful functor, meaning it is the free
functor from `Lattice` to `BoundedLattice`. -/
def Lattice_to_BoundedLattice_forget_adjunction :
  Lattice_to_BoundedLattice.{u} ⊣ forget₂ BoundedLattice Lattice :=
adjunction.mk_of_hom_equiv
  { hom_equiv := λ X Y,
    { to_fun := λ f,
      { to_fun := f ∘ some ∘ some,
        map_sup' := λ a b, (congr_arg f $ by refl).trans (f.map_sup' _ _),
        map_inf' := λ a b, (congr_arg f $ by refl).trans (f.map_inf' _ _) },
      inv_fun := lattice_hom.with_top_with_bot',
      left_inv := λ f, bounded_lattice_hom.ext $ λ a, match a with
          | none := f.map_top'.symm
          | some none := f.map_bot'.symm
          | some (some a) := rfl
        end,
      right_inv := λ f, lattice_hom.ext $ λ a, rfl },
  hom_equiv_naturality_left_symm' := λ X Y Z f g, bounded_lattice_hom.ext $ λ a, match a with
          | none := rfl
          | some none := rfl
          | some (some a) := rfl
        end,
  hom_equiv_naturality_right' := λ X Y Z f g, lattice_hom.ext $ λ a, rfl }

/-- `Lattice_to_BoundedLattice` and `order_dual` commute. -/
@[simps] def Lattice_to_BoundedLattice_comp_dual_iso_dual_comp_Lattice_to_BoundedLattice :
 (Lattice_to_BoundedLattice.{u} ⋙ BoundedLattice.dual) ≅
    (Lattice.dual ⋙ Lattice_to_BoundedLattice) :=
adjunction.left_adjoint_uniq
    (Lattice_to_BoundedLattice_forget_adjunction.comp _ _ BoundedLattice.dual_equiv.to_adjunction)
    (Lattice.dual_equiv.to_adjunction.comp _ _ Lattice_to_BoundedLattice_forget_adjunction)
