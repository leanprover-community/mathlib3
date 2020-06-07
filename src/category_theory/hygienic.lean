/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.canonical

/-!
-/

namespace category_theory

universes v u

section

variables {C : Type u} [category.{v} C]

class hygienic (p : C → Prop) : Prop :=
(map : Π {X Y : C}, (X ≅ Y) → (p X → p Y))

def hygienic.map_iso (p : C → Prop) [hygienic.{v} p] {X Y : C} (φ : X ≅ Y) : p X ↔ p Y :=
⟨hygienic.map.{v} φ, hygienic.map.{v} φ.symm⟩

instance subsingleton_hygienic (p : C → Prop) : subsingleton (hygienic.{v} p) :=
⟨by { rintros ⟨a⟩ ⟨b⟩, congr }⟩

def hygienic_not (p : C → Prop) [hygienic.{v} p] : hygienic.{v} (λ X, ¬ p X) :=
{ map := λ X Y i h w, h (hygienic.map.{v} i.symm w) }

def hygienic_and (p q : C → Prop) [hygienic.{v} p] [hygienic.{v} q] :
  hygienic.{v} (λ X, p X ∧ q X) :=
{ map := λ X Y i h, ⟨hygienic.map.{v} i h.1, hygienic.map.{v} i h.2⟩ }

def hygienic_or (p q : C → Prop) [hygienic.{v} p] [hygienic.{v} q] :
  hygienic.{v} (λ X, p X ∨ q X) :=
{ map := λ X Y i, or.imp (λ h, hygienic.map.{v} i h) (λ h, hygienic.map.{v} i h) }

end

section

variables {C : Type (u+1)} [large_category C] [concrete_category C]

local attribute [instance] concrete_category.has_coe_to_sort
local attribute [instance] concrete_category.has_coe_to_fun

instance hygienic_canonical_eq_canonical
  (x y : Π (Y : C), (Y : Type u)) [canonical x] [canonical y] :
  hygienic.{u} (λ Y : C, x Y = y Y) :=
{ map := λ X Y φ,
  begin
    intro h,
    replace h := congr_arg (φ.hom : X → Y) h,
    simpa using h,
  end }

end

open tactic

meta def backtrack_aux (tactics : list (tactic unit)) : ℕ → tactic unit
| 0 := done <|> failed
| (n+1) := done <|> (tactics.map (λ t : tactic unit, t >> backtrack_aux n)).mfirst id

meta def backtrack (tactics : list (tactic unit)) : tactic unit :=
backtrack_aux tactics 5

example : ∃ n : ℕ, n = 2 :=
begin
  backtrack [`[fsplit], `[refl], `[exact 1], `[exact 2]],
end

meta def apply_no_instances (n : name) : tactic unit :=
do
  e ← mk_const n,
  tactic.apply e {instances := ff},
  skip

/-- Given a tactic `tac` that can solve an application of `cls` in the right context,
    `tactic_derive_handler` uses it to build an instance declaration of `cls n`. -/
-- This is a simplified version of `instance_derive_handler` from core,
-- which only works for inductive types.
-- If it were posisble to unify them, that would be great,
-- but I don't understand `instance_derive_handler` well enough to do that.
meta def tactic_derive_handler (cls : name) (tac : tactic unit) : derive_handler :=
λ p n,
if p.is_constant_of cls then
do decl ← get_decl n,
   cls_decl ← get_decl cls,
   env ← get_env,
   let ls := decl.univ_params.map level.param,
   let tgt : expr := expr.const n ls,
   tgt ← mk_app cls [tgt],
   (_, val) ← tactic.solve_aux tgt (intros >> tac),
   val ← instantiate_mvars val,
   let trusted := decl.is_trusted ∧ cls_decl.is_trusted,
   add_protected_decl
     (declaration.defn (n ++ cls)
             decl.univ_params
             tgt val reducibility_hints.abbrev trusted),
   set_basic_attribute `instance (n ++ cls) tt,
   pure true
else pure false

@[derive_handler, priority 2000] meta def hygienic_instance : derive_handler :=
tactic_derive_handler ``hygienic $
backtrack [`[apply_instance], apply_no_instances `category_theory.hygienic_canonical_eq_canonical, synthesize_canonical]

end category_theory
