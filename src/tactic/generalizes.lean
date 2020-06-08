/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

import tactic.core

universes u v w

namespace tactic

open expr

example {n m : ℕ} : unit :=
begin
  (do n ← get_local `n,
      m ← get_local `m,
      x ← kabstract `((%%n + 1) * %%m) `(%%n + 1) ,
      tactic.trace x),
  exact ()
end

-- Input must be in reverse dependency order!
-- Output constants are also in reverse dependency order.
meta def generalizes'_aux₁
  : expr → list expr → list (name × expr) → tactic (expr × list expr)
| e cnsts [] := pure (e, cnsts.reverse)
| e cnsts ((n, x) :: xs) := do
  x_type ← infer_type x,
  c ← mk_local' n binder_info.default x_type,
  e ← kreplace e x c,
  cnsts ← cnsts.mmap (λ c', kreplace c' x c),
  generalizes'_aux₁ e (c :: cnsts) xs

example {n m} {f : fin n} (g : fin m) : unit :=
begin
  (do n ← get_local `n,
      m ← get_local `m,
      f ← get_local `f,
      g ← get_local `g,
      e ← to_expr ``(%%f == %%g),
      (e, cnsts) ← generalizes'_aux₁ e [] [(`i, f), (`j, n)],
      trace e,
      cnsts.mmap' (λ c, do trace c, t ← infer_type c, trace t)
  ),
  exact ()
end

-- Input must be in reverse dependency order!
meta def generalizes'_aux₂ : expr → list (name × expr × expr) → tactic expr
| e [] := pure e
| e ((eq_name, cnst, arg) :: cs) := do
  cnst_type ← infer_type cnst,
  arg_type ← infer_type arg,
  sort u ← infer_type arg_type,
  let e :=
    pi cnst.local_pp_name binder_info.default cnst_type $
    pi eq_name binder_info.default ((const `heq [u]) cnst_type (var 0) arg_type arg) $
    (e.abstract cnst).lift_vars 0 1,
  generalizes'_aux₂ e cs

meta def generalizes' (xs : list (name × name × expr)) : tactic (list expr) := focus1 $ do
  tgt ← target,
  let xs_rev := xs.reverse,
  (result_type, cnsts) ← generalizes'_aux₁ tgt []
    (xs_rev.map (λ ⟨e_name, _, e⟩, (e_name, e))),
  let xs' := @list.map₂ (name × name × expr) expr _
    (λ ⟨x_name, eq_name, x⟩ cnst, (eq_name, cnst, x)) xs_rev cnsts,
  result_type ← generalizes'_aux₂ result_type xs',
  n ← mk_fresh_name,
  h ← assert n result_type,
  swap,
  apps ← xs.mmap $ λ ⟨_, _, x⟩, do {
    x_type ← infer_type x,
    sort u ← infer_type x_type,
    pure [x, (const `heq.refl [u]) x_type x]
  },
  exact $ h.mk_app apps.join,
  intron' $ xs.length * 2


namespace interactive

open interactive
open lean.parser

private meta def generalizes_arg_parser : lean.parser (name × pexpr × name) :=
with_desc "id : expr = id" $ do
  hyp_name ← ident,
  tk ":",
  e ← lean.parser.pexpr 0,
  (e, arg_name) ←
    match e with
    | (app (app (macro _ [const `eq _ ]) e) (local_const x _ _ _)) := pure (e, x)
    | _ := fail "parser error"
    end,
  pure $ (hyp_name, e, arg_name)

private meta def generalizes_args_parser
  : lean.parser (list (name × pexpr × name)) :=
with_desc "[id : expr = id, ...]" $
  tk "[" *> sep_by (tk ",") generalizes_arg_parser <* tk "]"

meta def generalizes (args : parse generalizes_args_parser) : tactic unit := do
  args ← args.mmap $ λ ⟨hyp_name, arg, arg_name⟩, do {
    arg ← to_expr arg,
    pure (arg_name, hyp_name, arg)
  },
  generalizes' args,
  pure ()

end interactive
end tactic

-- TODO everything below here is example code

inductive Fin : ℕ → Type
| zero {n} : Fin (n + 1)
| succ {n} (f : Fin n) : Fin (n + 1)

namespace Fin

inductive eq : ∀ n m, Fin n → Fin m → Prop
| zero {n m} : eq (n + 1) (m + 1) zero zero
| succ {n m} {f : Fin n} {g : Fin m} :
  eq n m f g →
  eq (n + 1) (m + 1) (succ f) (succ g)

end Fin

example {n m} (f : Fin n) (g : Fin m)
  : Fin.eq (n + 1) (m + 1) (Fin.succ f) (Fin.succ g)
  → Fin.eq n m f g :=
begin
  generalizes
    [ n'_eq : n + 1 = n'
    , m'_eq : m + 1 = m'
    , f'_eq : f.succ = f'
    , g'_eq : g.succ = g' ],
  intro h,
  induction h,
  { sorry },
  { sorry }
end
