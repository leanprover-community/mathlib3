/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Reification of goals into deeply embedded SOL.
-/

import tactic.vampire.form2 logic.basic

open expr tactic

namespace vampire

meta def is_func_type (dx : expr) : expr → bool
| `(%%x → %%y) := (x = dx) && (is_func_type y)
| x            := x = dx

meta def is_pred_type (dx : expr) : expr → bool
| `(%%x → %%y) := (x = dx) && (is_pred_type y)
| x            := x = `(Prop)

-- meta def compare : expr → expr → tactic unit
-- | (expr.app x y) (expr.app z w) :=
--   if x = z
--   then trace "Fst eq"
--   else trace "Fst not eq" >>
--   if y = w
--   then trace "Snd eq"
--   else trace "Snd not eq"
-- | _ _ := trace "Not apps"
--
-- meta def get_head : list expr → tactic expr
-- | [] := failed
-- | (x :: _) := return x

meta def get_symb_aux (dx x : expr) (xs : list expr) : tactic expr :=
if x ∈ xs
then failed
else do tx ← infer_type x,
        if (is_pred_type dx tx || is_func_type dx tx)
        then return x
        else failed

meta def get_symb (dx : expr) (xs : list expr) : expr → tactic expr
| `(true)   := failed
| `(false)  := failed
| `(¬ %%px) := get_symb px
| `(%%px ∨ %%qx) := get_symb px <|> get_symb qx
| `(%%px ∧ %%qx) := get_symb px <|> get_symb qx
| (pi _ _ _ px) := get_symb px
| `(Exists %%(expr.lam _ _ _ px)) := get_symb px
| `(Exists %%prx) := get_symb prx
| x@(app x1 x2) :=
       get_symb x1
  <|>  get_symb x2
  <|>  get_symb_aux dx x xs
| x := get_symb_aux dx x xs

meta def subst_symb (y : expr) : nat → expr → expr
| k x@(app x1 x2) :=
  if y = x
  then var k
  else app (subst_symb k x1) (subst_symb k x2)
| k (lam n b tx x) := lam n b tx (subst_symb (k+1) x)
| k (pi n b tx x)  := pi n b tx (subst_symb (k+1) x)
| k x := if y = x then var k else x

meta def abst (dx : expr) : expr → tactic expr
| x :=
  (do y ← get_symb dx [] x,
      abst (pi name.anonymous binder_info.default dx (subst_symb y 0 x))) <|>
  (return x)

meta def abst_eq (dx eqx : expr) : expr → tactic expr
| x :=
  (do y ← get_symb dx [eqx] x,
      abst_eq (pi name.anonymous binder_info.default dx (subst_symb y 0 x))) <|>
  (return $ subst_symb eqx 0 x)

meta def get_domain_core : expr → tactic expr
| `(¬ %%p)     := get_domain_core p
| `(%%p ∨ %%q) := get_domain_core p <|> get_domain_core q
| `(%%p ∧ %%q) := get_domain_core p <|> get_domain_core q
| `(%%p ↔ %%q) := get_domain_core p <|> get_domain_core q
| (pi _ _ p q) := mcond (is_prop p) (get_domain_core p <|> get_domain_core q) (return p)
| `(@Exists %%t _) := return t
| _ := failed

meta def get_domain : tactic expr :=
(target >>= get_domain_core) <|> return `(unit)

local notation `#`     := term₂.var
local notation t `&` s := term₂.app t s

local notation `⟪` b `,` a `⟫` := form₂.lit b a
local notation p `∨₂` q := form₂.bin tt p q
local notation p `∧₂` q := form₂.bin ff p q
local notation `∃₂` p := form₂.qua tt p
local notation `∀₂` p := form₂.qua ff p

meta def to_term (k : nat) : expr → tactic term₂
| (app x y) :=
  do a ← to_term x,
     b ← to_term y,
     return (a & b)
| (var m) := return (# m)
| _ := failed

meta def to_form : nat → expr → tactic form₂
| k `(%%px ∨ %%qx) :=
  do φ ← to_form k px,
     χ ← to_form k qx,
     return (φ ∨₂ χ)
| k `(%%px ∧ %%qx) :=
  do φ ← to_form k px,
     χ ← to_form k qx,
     return (φ ∧₂ χ)
| k (pi _ _ _ px) :=
  do φ ← to_form (k+1) px, return (∀₂ φ)
| k `(Exists %%(expr.lam _ _ _ px)) :=
  do φ ← to_form (k+1) px, return (∃₂ φ)
| k `(Exists %%prx) :=
  do φ ← to_form (k+1) (app (prx.lift_vars 0 1) (var 0)),
     return (∃₂ φ)
| k `(¬ %%px) :=
  do a ← to_term k px,
     return ⟪ff, a⟫
| k px :=
  do a ← to_term k px,
     return ⟪tt, a⟫

run_cmd mk_simp_attr `sugar

attribute [sugar]
  -- logical constants
  or_false  false_or
  and_false false_and
  or_true   true_or
  and_true  true_and
  -- implication elimination
  classical.imp_iff_not_or
  classical.iff_iff_not_or_and_or_not
  -- NNF
  classical.not_not
  not_exists
  not_or_distrib
  classical.not_and_distrib
  classical.not_forall

meta def desugar := `[try {simp only with sugar}]

meta def reify : tactic (expr × expr × form₂) :=
do desugar,
   dx ← get_domain,
   ihx ← to_expr ``(inhabited),
   ix ← mk_instance (app ihx dx),
   p ← target >>= abst dx >>= to_form 0,
   return (dx, ix, p)

meta def reify_eq : tactic (expr × expr × form₂) :=
do desugar,
   dx ← get_domain,
   ihx ← to_expr ``(inhabited),
   ix ← mk_instance (app ihx dx),
   eqx ← to_expr ``(@eq %%dx),
   p ← target >>= abst_eq dx eqx >>= to_form 0,
   return (dx, ix, p)

end vampire
