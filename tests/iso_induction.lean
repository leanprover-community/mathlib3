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
variables {D : Type u₁} [𝒟 : category.{u₁ v₁} D]
include 𝒟

set_option pp.universes true

structure functorial_preimage (e : D) :=
(E : Type u₂) 
[ℰ : category.{u₂ v₂} E]
(F : (@category_theory.functor.{u₂ v₂ u₁ v₁} E ℰ D 𝒟)) 
(e' : E)
(w : @functor.obj E ℰ D 𝒟 F e' = e)
end


-- namespace functorial_preimage
-- variables {E : Type u₁} [ℰ : category.{u₁ v₁} E]
-- include ℰ

-- def comp 
--   {e : D}
--   (p : functorial_preimage.{u₁ v₁} e)
--   (q : functorial_preimage.{u₁ v₁} p.e') :
--   functorial_preimage.{u₁ v₁} e

-- end functorial_preimage

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
include 𝒞


meta def make_more_functorial (X : C) (e : Type u₁) (p : functorial_preimage.{u₁+1 u₁} e) :
  tactic (list (functorial_preimage.{u₁+1 u₁ u₁ v₁} e)) := sorry

#check unchecked_cast

meta def make_functorial_aux (X : C) (e : Type u₁) (p : functorial_preimage.{u₁+1 u₁} e) :
  tactic (functorial_preimage.{u₁+1 u₁ u₁ v₁} e) :=
do
  -- Check if X = p.e' (as expressions?!)
  -- If so, just return p, it's what we want.
  -- 
  
  fail ""


meta def make_functorial' (X : C) (e : Type u₁) :
  tactic (functorial_preimage.{u₁+1 u₁ u₁ v₁} e) :=
let p : functorial_preimage.{u₁+1 u₁ u₁ v₁} e :=
{ E := Type u₁, --- argh!
  F := functor.id (Type u₁),
  e' := e,
  w := by refl } in
do make_functorial_aux X e p

meta def make_functorial (X : C) (e : Type u₁) :
  tactic { F : C ⥤ Type u₁ // F.obj X = e } :=
-- We do the final step without "do" blocks, because the universe levels need to change.
λ s,
match make_functorial' X e s with
| (interaction_monad.result.success q s') := interaction_monad.result.success ⟨ @unchecked_cast _ (C ⥤ Type u₁) q.F, q.w ⟩ s'
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
