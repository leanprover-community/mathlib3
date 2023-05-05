/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.hom.lattice

/-!
# To move
-/

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
