/-
Copyright (c) 2017 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import tactic.core

open expr
open interactive
open lean.parser
open tactic

private meta def match_subexpr (p : pattern) : expr → tactic (list expr)
| e := prod.snd <$> match_pattern p e <|>
  match e with
  | app e₁ e₂ := match_subexpr e₁ <|> match_subexpr e₂
  | pi _ _ _ b := mk_fresh_name >>= match_subexpr ∘ b.instantiate_var ∘ mk_local
  | lam _ _ _ b := mk_fresh_name >>= match_subexpr ∘ b.instantiate_var ∘ mk_local
  | _ := failed
  end

private meta def match_exact : pexpr → expr → tactic (list expr)
| p e :=
do (app p₁ p₂) ← pure p | match_expr p e,
   if pexpr.is_placeholder p₁ then
     -- `_ p` pattern ~> match `p` recursively
     do p ← pexpr_to_pattern p₂, match_subexpr p e
   else
     match_expr p e

meta def expr.get_pis : expr → tactic (list expr × expr)
| (pi n bi d b)  :=
do l ← mk_local' n bi d,
   (pis, b) ← expr.get_pis (b.instantiate_var l),
   pure (d::pis, b)
| e              := pure ([], e)

meta def pexpr.get_uninst_pis : pexpr → tactic (list pexpr × pexpr)
| (pi n bi d b)  :=
do (pis, b) ← pexpr.get_uninst_pis b,
   pure (d::pis, b)
| e              := pure ([], e)

private meta def match_hyps : list pexpr → list expr → list expr → tactic unit
| (p::ps) old_hyps (h::new_hyps) :=
do some _ ← try_core (match_exact p h) | match_hyps (p::ps) (h::old_hyps) new_hyps,
   match_hyps ps [] (old_hyps ++ new_hyps)
| [] _ _      := skip
| (_::_) _ [] := failed

private meta def match_sig (p : pexpr) (e : expr) : tactic unit :=
do (p_pis, p) ← p.get_uninst_pis,
   (pis, e)   ← e.get_pis,
   match_exact p e,
   match_hyps p_pis [] pis

private meta def trace_match (pat : pexpr) (ty : expr) (n : name) : tactic unit :=
try $ do
  guard ¬ n.is_internal,
  match_sig pat ty,
  ty ← pp ty,
  trace format!"{n}: {ty}"

/--
The `find` command from `tactic.find` allows to find definitions lemmas using
pattern matching on the type. For instance:

```lean
import tactic.find

run_cmd tactic.skip

#find _ + _ = _ + _
#find (_ : ℕ) + _ = _ + _
#find ℕ → ℕ
```

The tactic `library_search` is an alternate way to find lemmas in the library.
-/
@[user_command]
meta def find_cmd (_ : parse $ tk "#find") : lean.parser unit :=
do pat ← lean.parser.pexpr 0,
   env ← get_env,
   env.mfold () $ λ d _,
     match d with
     | declaration.thm n _ ty _ := trace_match pat ty n
     | declaration.defn n _ ty _ _ _ := trace_match pat ty n
     | _ := skip
     end

add_tactic_doc
{ name                     := "#find",
  category                 := doc_category.cmd,
  decl_names               := [`find_cmd],
  tags                     := ["search"] }

-- #find (_ : nat) + _ = _ + _
-- #find _ + _ = _ + _
-- #find _ (_ + _) → _ + _ = _ + _   -- TODO(Mario): no results
-- #find add_group _ → _ + _ = _ + _ -- TODO(Mario): no results
