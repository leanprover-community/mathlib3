/-
Copyright (c) 2017 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Traversal for Lean expressions
-/
universes u v

section expr
open expr
variables {m : Type → Type u} [monad m]
variables {elab elab' : bool}

variables f : expr elab → m (expr elab')

/- only traverses the direct descendents -/
meta def expr.traverse : expr elab → m (expr elab')
 | (var v)  := pure $ var v
 | (sort l) := pure $ sort l
 | (const n ls) := pure $ const n ls
 | (mvar n n' e) := mvar n n' <$> f e
 | (local_const n n' bi e) := local_const n n' bi <$> f e
 | (app e₀ e₁) := app <$> f e₀ <*> f e₁
 | (lam n bi e₀ e₁) := lam n bi <$> f e₀ <*> f e₁
 | (pi n bi e₀ e₁) := pi n bi <$> f e₀ <*> f e₁
 | (elet n e₀ e₁ e₂) := elet n <$> f e₀ <*> f e₁ <*> f e₂
 | (macro mac es) := macro mac <$> mmap f es

meta def expr.list_local_const (e : expr) : list expr :=
e.fold [] (λ e' _ es, if expr.is_local_constant e' ∧ ¬ e' ∈ es then e' :: es else es)

end expr

namespace tactic
open expr binder_info

meta def pis : list expr → expr → tactic expr
| (e@(local_const uniq pp info _) :: es) f := do
  t ← infer_type e,
  f' ← pis es f,
  pure $ pi pp info t (abstract_local f' uniq)
| _ f := pure f

meta def last_explicit_arg : expr → tactic expr
| (app f e) :=
do t ← infer_type f >>= whnf,
   if t.binding_info = binder_info.default
     then pure e
     else last_explicit_arg f
| e := pure e

private meta def get_expl_pi_arity_aux : expr → tactic nat
| (expr.pi n bi d b) :=
  do m     ← mk_fresh_name,
     let l := expr.local_const m n bi d,
     new_b ← whnf (expr.instantiate_var b l),
     r     ← get_expl_pi_arity_aux new_b,
     if bi = default then
       return (r + 1)
     else
       return r
| e                  := return 0

/-- Compute the arity of explicit arguments of the given (Pi-)type -/
meta def get_expl_pi_arity (type : expr) : tactic nat :=
whnf type >>= get_expl_pi_arity_aux

/-- Compute the arity of explicit arguments of the given function -/
meta def get_expl_arity (fn : expr) : tactic nat :=
infer_type fn >>= get_expl_pi_arity

end tactic
