/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/

import data.qpf.multivariate.basic

/-!
# The quotient of QPF is itself a QPF

The quotients are here defined using a surjective function and
its right inverse. They are very similar to the `abs` and `repr`
functions found in the definition of `mvqpf`
-/

universes u
open_locale mvfunctor

namespace mvqpf

variables {n : ℕ}
variables {F : typevec.{u} n → Type u}

section repr

variables [mvfunctor F] [q : mvqpf F]
variables {G : typevec.{u} n → Type u} [mvfunctor G]
variable  {FG_abs  : Π {α}, F α → G α}
variable  {FG_repr : Π {α}, G α → F α}

/-- If `F` is a QPF then `G` is a QPF as well. Can be used to
construct `mvqpf` instances by transporting them across
surjective functions -/
def quotient_qpf
    (FG_abs_repr : Π {α} (x : G α), FG_abs (FG_repr x) = x)
    (FG_abs_map  : ∀ {α β} (f : α ⟹ β) (x : F α), FG_abs (f <$$> x) = f <$$> FG_abs x) :
 mvqpf G :=
{ P := q.P,
  abs := λ α p, FG_abs (abs p),
  repr := λ α x, repr (FG_repr x),
  abs_repr := λ α x, by rw [abs_repr,FG_abs_repr],
  abs_map := λ α β f p, by rw [abs_map,FG_abs_map] }

end repr

section rel

variables (R : ∀ ⦃α⦄, F α → F α → Prop)

/-- Functorial quotient type -/
def quot1 (α : typevec n) :=
quot (@R α)

instance quot1.inhabited {α : typevec n} [inhabited $ F α] : inhabited (quot1 R α) :=
⟨ quot.mk _ (default _) ⟩

variables [mvfunctor F] [q : mvqpf F]
variables (Hfunc : ∀ ⦃α β⦄ (a b : F α) (f : α ⟹ β), R a b → R (f <$$> a) (f <$$> b))

/-- `map` of the `quot1` functor -/
def quot1.map ⦃α β⦄ (f : α ⟹ β) : quot1.{u} R α → quot1.{u} R β :=
quot.lift (λ x : F α, quot.mk _ (f <$$> x : F β)) $ λ a b h,
  quot.sound $ Hfunc a b _ h

/-- `mvfunctor` instance for `quot1` with well-behaved `R` -/
def quot1.mvfunctor : mvfunctor (quot1 R) :=
{ map := quot1.map R Hfunc }

/-- `quot1` is a qpf -/
noncomputable def rel_quot : @mvqpf _ (quot1 R) (mvqpf.quot1.mvfunctor R Hfunc) :=
@quotient_qpf n F _ q _ (mvqpf.quot1.mvfunctor R Hfunc) (λ α x, quot.mk _ x) (λ α, quot.out)
  (λ α x, quot.out_eq _)
  (λ α β f x, rfl)

end rel

end mvqpf
