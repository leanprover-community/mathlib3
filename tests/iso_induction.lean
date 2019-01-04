import category_theory.isomorphism
import category_theory.types

open category_theory

universes u₁ v₁ u₂ v₂

namespace tactic
open tactic
open interactive
open interactive.types
open lean.parser
#check reflected
meta def check_equal (a b : ℕ) : tactic unit :=
do let a' := reflected.to_expr `(a),
   let b' := reflected.to_expr `(b),
   trace a',
   trace b',
   failed

example : false :=
begin
check_equal 3 7
end

section
variables {D : Type (u₁+1)} [𝒟 : large_category D]
include 𝒟

set_option pp.universes true

structure functorial_preimage (e : D) :=
(E : Type (u₁+1) )
[ℰ : large_category E]
(F : E ⥤ D) 
(e' : E)
(w : F.obj e' = e)
end


-- namespace functorial_preimage
-- variables {D : Type (u₁+1)} [𝒟 : large_category D]
-- include 𝒟

-- def comp 
--   {e : D}
--   (p : functorial_preimage e)
--   (q : functorial_preimage p.e') :
--   functorial_preimage e

-- end functorial_preimage

variables {C : Type (u₁+1)} [𝒞 : large_category C]
include 𝒞


meta def make_more_functorial (X : C) (e : Type u₁) (p : functorial_preimage e) :
  tactic (list (functorial_preimage e)) := sorry

meta def make_functorial_aux (X : C) (e : Type u₁) (p : functorial_preimage e) :
  tactic (functorial_preimage e) :=
do
  -- Check if X = p.e' (as expressions?!)
  -- If so, just return p, it's what we want.
  -- Otherwise, call make_more_functorial X e p, and invoke make_functorial_aux on each element of that list.
  fail ""

meta def make_functorial' (X : C) (e : Type u₁) :
  tactic (functorial_preimage e) :=
let p : functorial_preimage e :=
{ E := Type u₁,
  F := functor.id (Type u₁),
  e' := e,
  w := by refl } in
do make_functorial_aux X e p

meta def make_functorial (X : C) (e : Type u₁) :
  tactic { F : C ⥤ Type u₁ // F.obj X = e } :=
-- We do the final step without "do" blocks, because the universe levels need to change.
λ s,
match make_functorial' X e s with
| (interaction_monad.result.success q s') := interaction_monad.result.success ⟨ unchecked_cast q.F, unchecked_cast q.w ⟩ s'
| _ := sorry -- TODO handle exceptions!
end


namespace interactive
/--
`iso_rw e`, where `e : X ≅ Y`, `X Y : C` should try to replace all instances of `X` in the goal with `Y`.
To do this, it attempts to:
1. Re-expresses the goal as some functor `F : C ⥤ Type` applied to the object `X`.
2. Invokes `apply F.map (e.inv)`, to obtain the goal `F.obj Y`.
3. Substitute back in the definition of `F`, and definitionally simplify.
-/
meta def iso_rw (e : parse texpr) : tactic unit := sorry
end interactive
end tactic

variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

example (X Y Z : C) (α : X ≅ Y) (f : Y ⟶ Z) : X ⟶ Z :=
begin
  iso_rw α,
  exact f,
end

variables (D : Type u) [𝒟 : category.{u v} D]
include 𝒟

example (F G : C ⥤ D) (α : F ≅ G) (X : C) (Y : D) (f : G X ⟶ Y) : F X ⟶ Y :=
begin
  iso_rw α,
  exact f,
end

example 
