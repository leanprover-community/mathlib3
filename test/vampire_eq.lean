/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek
-/

import tactic.vampire

section

variables {α : Type} [inhabited α]

variables {f g i : α → α}
variables {p q : α → Prop}
variables {mult : α → α → α}
local notation x `*` y := mult x y

open tactic expr vampire


 example (x y z : ℕ) (p : ℕ → Prop) :
   x = y → y = z → (∀ w, w = z → p w) → p x :=
 by vampire
 
 example : ∀ x y : ℕ, x = y ∨ ¬ x = y := 
 by vampire
 
 example : ∀ x y, (p x ∧ x = f y) → p (f y) :=
 by vampire

example :
   forall e,
   (forall x y z, x * (y * z) = (x * y) * z) ∧
   (forall x, e * x = x) ∧
   (forall x, i x * x = e) →
   forall x, x * i x = e :=
by vampire

#exit



#exit

-- example :
--    (exists x, x = f(g(x)) ∧ forall x', x' = f(g(x')) → x = x') ↔
--    (exists y, y = g(f(y)) ∧ forall y', y' = g(f(y')) → y = y') :=
-- by vampire
-- 
-- example :
--    (exists x, x = f(g(x)) ∧ forall x', x' = f(g(x')) → x = x') ↔
--    (exists y, y = g(f(y)) ∧ forall y', y' = g(f(y')) → y = y') :=
-- by vampire


#exit

let ewd =
   (forall x, f(x) → g(x)) ∧
   (exists x, f(x)) ∧
   (forall x y. g(x) ∧ g(y) → x = y)
   → forall y, g(y) → f(y) := sorry

let wishnu =
   (exists x, x = f(g(x)) ∧ forall x'. x' = f(g(x')) → x = x') ↔
   (exists y, y = g(f(y)) ∧ forall y'. y' = g(f(y')) → y = y') := sorry

let group1 =
   (forall x y z. x * (y * z) = (x * y) * z) ∧
   (forall x, e * x = x) ∧
   (forall x, i(x) * x = e)
   → forall x, x * e = x := sorry

let group2 =
   (forall x y z. x * (y * z) = (x * y) * z) ∧
   (forall x, e * x = x) ∧
   (forall x, i(x) * x = e)
   → forall x, x * i(x) = e := sorry

time bmeson ewd;;
time emeson ewd;;

(***********

time bmeson wishnu;;
time emeson wishnu;;

time bmeson group1;;
time emeson group1;;

time bmeson group2;;
time emeson group2;;

 *************)

(* ------------------------------------------------------------------------- *)
(* Nice function composition exercise from "Conceptual Mathematics".         *)
(* ------------------------------------------------------------------------- *)

(**************

let fm =
   (forall x y z. x * (y * z) = (x * y) * z) ∧ p * q * p = p
   → exists q'. p * q' * p = p ∧ q' * p * q' = q' := sorry

time bmeson fm;;        (** Seems to take a bit longer than below version  **)

time emeson fm;;        (** Works in 64275 seconds(!), depth 30, on laptop **)

****************)

(**** Some other predicate formulations no longer in the main text

meson
   (forall x, P(1,x,x)) ∧
   (forall x, P(i(x),x,1)) ∧
   (forall u v w x y z. P(x,y,u) ∧ P(y,z,w) → (P(x,w,v) ↔ P(u,z,v)))
   → forall x, P(x,1,x) := sorry

meson
   (forall x, P(1,x,x)) ∧
   (forall x, P(i(x),x,1)) ∧
   (forall u v w x y z. P(x,y,u) ∧ P(y,z,w) → (P(x,w,v) ↔ P(u,z,v)))
   → forall x, P(x,i(x),1) := sorry

(* ------------------------------------------------------------------------- *)
(* See how efficiency drops when we assert completeness.                     *)
(* ------------------------------------------------------------------------- *)

meson
   (forall x, P(1,x,x)) ∧
   (forall x, P(x,x,1)) ∧
   (forall x y. exists z, P(x,y,z)) ∧
   (forall u v w x y z. P(x,y,u) ∧ P(y,z,w) → (P(x,w,v) ↔ P(u,z,v)))
   → forall a b c. P(a,b,c) → P(b,a,c) := sorry

****)

(*** More reductions, not now explicitly in the text.

meson
   (forall x, R(x,x)) ∧
   (forall x y z. R(x,y) ∧ R(y,z) → R(x,z))
   ↔ (forall x y. R(x,y) ↔ (forall z, R(y,z) → R(x,z))) := sorry

meson
   (forall x y. R(x,y) →  R(y,x)) ↔
   (forall x y. R(x,y) ↔ R(x,y) ∧ R(y,x)) := sorry

(* ------------------------------------------------------------------------- *)
(* Show how Equiv' reduces to triviality.                                    *)
(* ------------------------------------------------------------------------- *)

meson
   (forall x, (forall w, R'(x,w) ↔ R'(x,w))) ∧
   (forall x y. (forall w, R'(x,w) ↔ R'(y,w))
                → (forall w, R'(y,w) ↔ R'(x,w))) ∧
   (forall x y z. (forall w, R'(x,w) ↔ R'(y,w)) ∧
                  (forall w, R'(y,w) ↔ R'(z,w))
                  → (forall w, R'(x,w) ↔ R'(z,w))) := sorry

(* ------------------------------------------------------------------------- *)
(* More auxiliary proofs for Brand's S and T modification.                   *)
(* ------------------------------------------------------------------------- *)

meson
   (forall x y. R(x,y) ↔ (forall z, R'(x,z) ↔ R'(y,z))) ∧
   (forall x, R'(x,x))
   → forall x y. ~R'(x,y) → ~R(x,y) := sorry

meson
   (forall x y. R(x,y) ↔ (forall z, R'(y,z) → R'(x,z))) ∧
   (forall x, R'(x,x))
   → forall x y. ~R'(x,y) → ~R(x,y) := sorry

meson
   (forall x y. R(x,y) ↔ R'(x,y) ∧ R'(y,x))
   → forall x y. ~R'(x,y) → ~R(x,y) := sorry

***)

END_INTERACTIVE;;
