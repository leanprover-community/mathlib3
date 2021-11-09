/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic.monotonicity.basic
import control.traversable
import control.traversable.derive
import data.dlist

variables {a b c p : Prop}

namespace tactic.interactive

open lean lean.parser  interactive
open interactive.types
open tactic

local postfix `?`:9001 := optional
local postfix *:9001 := many

meta inductive mono_function (elab : bool := tt)
 | non_assoc : expr elab → list (expr elab) → list (expr elab) → mono_function
 | assoc : expr elab → option (expr elab) → option (expr elab) → mono_function
 | assoc_comm : expr elab → expr elab → mono_function

meta instance : decidable_eq mono_function :=
by mk_dec_eq_instance

meta def mono_function.to_tactic_format : mono_function → tactic format
 | (mono_function.non_assoc fn xs ys) := do
  fn' ← pp fn,
  xs' ← mmap pp xs,
  ys' ← mmap pp ys,
  return format!"{fn'} {xs'} _ {ys'}"
 | (mono_function.assoc fn xs ys) := do
  fn' ← pp fn,
  xs' ← pp xs,
  ys' ← pp ys,
  return format!"{fn'} {xs'} _ {ys'}"
 | (mono_function.assoc_comm fn xs) := do
  fn' ← pp fn,
  xs' ← pp xs,
  return format!"{fn'} _ {xs'}"

meta instance has_to_tactic_format_mono_function : has_to_tactic_format mono_function :=
{ to_tactic_format := mono_function.to_tactic_format }

@[derive traversable]
meta structure ac_mono_ctx' (rel : Type) :=
  (to_rel : rel)
  (function : mono_function)
  (left right rel_def : expr)

@[reducible]
meta def ac_mono_ctx := ac_mono_ctx' (option (expr → expr → expr))
@[reducible]
meta def ac_mono_ctx_ne := ac_mono_ctx' (expr → expr → expr)

meta def ac_mono_ctx.to_tactic_format (ctx : ac_mono_ctx) : tactic format :=
do fn  ← pp ctx.function,
   l   ← pp ctx.left,
   r   ← pp ctx.right,
   rel ← pp ctx.rel_def,
   return format!"{{ function := {fn}\n, left  := {l}\n, right := {r}\n, rel_def := {rel} }"

meta instance has_to_tactic_format_mono_ctx : has_to_tactic_format ac_mono_ctx :=
{ to_tactic_format := ac_mono_ctx.to_tactic_format }

meta def as_goal (e : expr) (tac : tactic unit) : tactic unit :=
do gs ← get_goals,
   set_goals [e],
   tac,
   set_goals gs

open list (hiding map) functor dlist

section config

parameter opt : mono_cfg
parameter asms : list expr

meta def unify_with_instance (e : expr) : tactic unit :=
as_goal e $
apply_instance
<|>
apply_opt_param
<|>
apply_auto_param
<|>
tactic.solve_by_elim { lemmas := some asms }
<|>
reflexivity
<|>
applyc ``id
<|>
return ()

private meta def match_rule_head  (p : expr)
: list expr → expr → expr → tactic expr
 | vs e t :=
(unify t p >> mmap' unify_with_instance vs >> instantiate_mvars e)
<|>
do (expr.pi _ _ d b) ← return t | failed,
   v ← mk_meta_var d,
   match_rule_head (v::vs) (expr.app e v) (b.instantiate_var v)

meta def pi_head : expr → tactic expr
| (expr.pi n _ t b) :=
do v ← mk_meta_var t,
   pi_head (b.instantiate_var v)
| e := return e

meta def delete_expr (e : expr)
: list expr → tactic (option (list expr))
 | [] := return none
 | (x :: xs) :=
(compare opt e x >> return (some xs))
<|>
(map (cons x) <$> delete_expr xs)

meta def match_ac'
: list expr → list expr → tactic (list expr × list expr × list expr)
 | es (x :: xs) := do
    es' ← delete_expr x es,
    match es' with
     | (some es') := do
       (c,l,r) ← match_ac' es' xs, return (x::c,l,r)
     | none := do
       (c,l,r) ← match_ac' es xs, return (c,l,x::r)
    end
 | es [] := do
return ([],es,[])

meta def match_ac (l : list expr) (r : list expr)
: tactic (list expr × list expr × list expr) :=
do (s',l',r') ← match_ac' l r,
   s' ← mmap instantiate_mvars s',
   l' ← mmap instantiate_mvars l',
   r' ← mmap instantiate_mvars r',
   return (s',l',r')

meta def match_prefix
: list expr → list expr → tactic (list expr × list expr × list expr)
| (x :: xs) (y :: ys) :=
  (do compare opt x y,
      prod.map ((::) x) id <$> match_prefix xs ys)
<|> return ([],x :: xs,y :: ys)
| xs ys := return ([],xs,ys)

/--
`(prefix,left,right,suffix) ← match_assoc unif l r` finds the
longest prefix and suffix common to `l` and `r` and
returns them along with the differences  -/
meta def match_assoc (l : list expr) (r : list expr)
: tactic (list expr × list expr × list expr × list expr) :=
do (pre,l₁,r₁) ← match_prefix l r,
   (suf,l₂,r₂) ← match_prefix (reverse l₁) (reverse r₁),
   return (pre,reverse l₂,reverse r₂,reverse suf)

meta def check_ac : expr → tactic (bool × bool × option (expr × expr × expr) × expr)
 | (expr.app (expr.app f x) y) :=
   do t ← infer_type x,
      a ← try_core $ to_expr ``(is_associative %%t %%f) >>= mk_instance,
      c ← try_core $ to_expr ``(is_commutative %%t %%f) >>= mk_instance,
      i ← try_core (do
          v ← mk_meta_var t,
          l_inst_p ← to_expr ``(is_left_id %%t %%f %%v),
          r_inst_p ← to_expr ``(is_right_id %%t %%f %%v),
          l_v ← mk_meta_var l_inst_p,
          r_v ← mk_meta_var r_inst_p ,
          l_id ← mk_mapp `is_left_id.left_id [some t,f,v,some l_v],
          mk_instance l_inst_p >>= unify l_v,
          r_id ← mk_mapp `is_right_id.right_id [none,f,v,some r_v],
          mk_instance r_inst_p >>= unify r_v,
          v' ← instantiate_mvars v,
          return (l_id,r_id,v')),
      return (a.is_some,c.is_some,i,f)
 | _ := return (ff,ff,none,expr.var 1)

meta def parse_assoc_chain' (f : expr) : expr → tactic (dlist expr)
 | e :=
 (do (expr.app (expr.app f' x) y) ← return e,
     is_def_eq f f',
     (++) <$> parse_assoc_chain' x <*> parse_assoc_chain' y)
<|> return (singleton e)

meta def parse_assoc_chain (f : expr) : expr → tactic (list expr) :=
map dlist.to_list ∘ parse_assoc_chain' f

meta def fold_assoc (op : expr) :
  option (expr × expr × expr) → list expr → option (expr × list expr)
| _ (x::xs) := some (foldl (expr.app ∘ expr.app op) x xs, [])
| none []   := none
| (some (l_id,r_id,x₀)) [] := some (x₀,[l_id,r_id])

meta def fold_assoc1 (op : expr) : list expr → option expr
| (x::xs) := some $ foldl (expr.app ∘ expr.app op) x xs
| []   := none

meta def same_function_aux
: list expr → list expr → expr → expr → tactic (expr × list expr × list expr)
 | xs₀ xs₁ (expr.app f₀ a₀) (expr.app f₁ a₁) :=
   same_function_aux (a₀ :: xs₀) (a₁ :: xs₁) f₀ f₁
 | xs₀ xs₁ e₀ e₁ := is_def_eq e₀ e₁ >> return (e₀,xs₀,xs₁)

meta def same_function : expr → expr → tactic (expr × list expr × list expr) :=
same_function_aux [] []

meta def parse_ac_mono_function (l r : expr)
: tactic (expr × expr × list expr × mono_function) :=
do (full_f,ls,rs) ← same_function l r,
   (a,c,i,f) ← check_ac l,
   if a
   then if c
   then do
     (s,ls,rs) ← monad.join (match_ac
                   <$> parse_assoc_chain f l
                   <*> parse_assoc_chain f r),
     (l',l_id) ← fold_assoc f i ls,
     (r',r_id) ← fold_assoc f i rs,
     s' ← fold_assoc1 f s,
     return (l',r',l_id ++ r_id,mono_function.assoc_comm f s')
   else do -- a ∧ ¬ c
     (pre,ls,rs,suff) ← monad.join (match_assoc
                   <$> parse_assoc_chain f l
                   <*> parse_assoc_chain f r),
     (l',l_id) ← fold_assoc f i ls,
     (r',r_id) ← fold_assoc f i rs,
     let pre'  := fold_assoc1 f pre,
     let suff' := fold_assoc1 f suff,
     return (l',r',l_id ++ r_id,mono_function.assoc f pre' suff')
   else do -- ¬ a
     (xs₀,x₀,x₁,xs₁) ← find_one_difference opt ls rs,
     return (x₀,x₁,[],mono_function.non_assoc full_f xs₀ xs₁)

meta def parse_ac_mono_function' (l r : pexpr) :=
do l' ← to_expr l,
   r' ← to_expr r,
   parse_ac_mono_function l' r'

meta def ac_monotonicity_goal : expr → tactic (expr × expr × list expr × ac_mono_ctx)
 | `(%%e₀ → %%e₁) :=
  do (l,r,id_rs,f) ← parse_ac_mono_function e₀ e₁,
     t₀ ← infer_type e₀,
     t₁ ← infer_type e₁,
     rel_def ← to_expr ``(λ x₀ x₁, (x₀ : %%t₀) → (x₁ : %%t₁)),
     return (e₀, e₁, id_rs,
            { function := f
            , left := l, right := r
            , to_rel := some $ expr.pi `x binder_info.default
            , rel_def := rel_def })
 | `(%%e₀ = %%e₁) :=
  do (l,r,id_rs,f) ← parse_ac_mono_function e₀ e₁,
     t₀ ← infer_type e₀,
     t₁ ← infer_type e₁,
     rel_def ← to_expr ``(λ x₀ x₁, (x₀ : %%t₀) = (x₁ : %%t₁)),
     return (e₀, e₁, id_rs,
            { function := f
            , left := l, right := r
            , to_rel := none
            , rel_def := rel_def })
 | (expr.app (expr.app rel e₀) e₁) :=
  do (l,r,id_rs,f) ← parse_ac_mono_function e₀ e₁,
     return (e₀, e₁, id_rs,
            { function := f
            , left := l, right := r
            , to_rel := expr.app ∘ expr.app rel
            , rel_def := rel })
 | _ := fail "invalid monotonicity goal"

meta def bin_op_left (f : expr)  : option expr → expr → expr
| none e := e
| (some e₀) e₁ := f.mk_app [e₀,e₁]

meta def bin_op (f a b : expr) : expr :=
f.mk_app [a,b]

meta def bin_op_right (f : expr) : expr → option expr → expr
| e none := e
| e₀ (some e₁) := f.mk_app [e₀,e₁]

meta def mk_fun_app : mono_function → expr → expr
 | (mono_function.non_assoc f x y) z := f.mk_app (x ++ z :: y)
 | (mono_function.assoc f x y) z := bin_op_left f x (bin_op_right f z y)
 | (mono_function.assoc_comm f x) z := f.mk_app [z,x]

meta inductive mono_law
   /- `assoc (l₀,r₀) (r₁,l₁)` gives first how to find rules to prove
      x+(y₀+z) R x+(y₁+z);
      if that fails, helps prove (x+y₀)+z R (x+y₁)+z -/
 | assoc : expr × expr → expr × expr → mono_law
   /- `congr r` gives the rule to prove `x = y → f x = f y` -/
 | congr : expr → mono_law
 | other : expr → mono_law

meta def mono_law.to_tactic_format : mono_law → tactic format
 | (mono_law.other e) := do e ← pp e, return format!"other {e}"
 | (mono_law.congr r) := do e ← pp r, return format!"congr {e}"
 | (mono_law.assoc (x₀,x₁) (y₀,y₁)) :=
do x₀ ← pp x₀,
   x₁ ← pp x₁,
   y₀ ← pp y₀,
   y₁ ← pp y₁,
   return format!"assoc {x₀}; {x₁} | {y₀}; {y₁}"

meta instance has_to_tactic_format_mono_law : has_to_tactic_format mono_law :=
{ to_tactic_format := mono_law.to_tactic_format }

meta def mk_rel (ctx : ac_mono_ctx_ne) (f : expr → expr) : expr :=
ctx.to_rel (f ctx.left) (f ctx.right)

meta def mk_congr_args (fn : expr) (xs₀ xs₁ : list expr) (l r : expr) : tactic expr :=
do p ← mk_app `eq [fn.mk_app $ xs₀ ++ l :: xs₁,fn.mk_app $ xs₀ ++ r :: xs₁],
   prod.snd <$> solve_aux p
     (do iterate_exactly (xs₁.length) (applyc `congr_fun),
         applyc `congr_arg)

meta def mk_congr_law (ctx : ac_mono_ctx) : tactic expr :=
match ctx.function with
 | (mono_function.assoc f x₀ x₁) :=
    if (x₀ <|> x₁).is_some
       then mk_congr_args f x₀.to_monad x₁.to_monad ctx.left ctx.right
       else failed
 | (mono_function.assoc_comm f x₀) := mk_congr_args f [x₀] [] ctx.left ctx.right
 | (mono_function.non_assoc f x₀ x₁) := mk_congr_args f x₀ x₁ ctx.left ctx.right
end

meta def mk_pattern (ctx : ac_mono_ctx) : tactic mono_law :=
match (sequence ctx : option (ac_mono_ctx' _)) with
 | (some ctx) :=
   match ctx.function with
    | (mono_function.assoc f (some x) (some y)) :=
      return $ mono_law.assoc
       ( mk_rel ctx (λ i, bin_op f x (bin_op f i y))
       , mk_rel ctx (λ i, bin_op f i y))
       ( mk_rel ctx (λ i, bin_op f (bin_op f x i) y)
       , mk_rel ctx (λ i, bin_op f x i))
    | (mono_function.assoc f (some x) none) :=
      return $ mono_law.other $
        mk_rel ctx (λ e, mk_fun_app ctx.function e)
    | (mono_function.assoc f none (some y)) :=
      return $ mono_law.other $
        mk_rel ctx (λ e, mk_fun_app ctx.function e)
    | (mono_function.assoc f none none) :=
      none
    | _ :=
      return $ mono_law.other $
         mk_rel ctx (λ e, mk_fun_app ctx.function e)
   end
 | none := mono_law.congr <$> mk_congr_law ctx
end

meta def match_rule (pat : expr) (r : name) : tactic expr :=
do  r' ← mk_const r,
    t  ← infer_type r',
    t  ← expr.dsimp t { fail_if_unchanged := ff } tt [] [
      simp_arg_type.expr ``(monotone), simp_arg_type.expr ``(strict_mono)],
    match_rule_head pat [] r' t

meta def find_lemma (pat : expr) : list name → tactic (list expr)
 | [] := return []
 | (r :: rs) :=
 do (cons <$> match_rule pat r <|> pure id) <*> find_lemma rs

meta def match_chaining_rules (ls : list name) (x₀ x₁ : expr) : tactic (list expr) :=
do x' ← to_expr ``(%%x₁ → %%x₀),
   r₀ ← find_lemma x' ls,
   r₁ ← find_lemma x₁ ls,
   return (expr.app <$> r₀ <*> r₁)

meta def find_rule (ls : list name) : mono_law → tactic (list expr)
 | (mono_law.assoc (x₀,x₁) (y₀,y₁)) :=
(match_chaining_rules ls x₀ x₁)
<|> (match_chaining_rules ls y₀ y₁)
 | (mono_law.congr r) := return [r]
 | (mono_law.other p) := find_lemma p ls

universes u v

def apply_rel {α : Sort u} (R : α → α → Sort v) {x y : α}
  (x' y' : α)
  (h : R x y)
  (hx : x = x')
  (hy : y = y')
: R x' y' :=
by { rw [← hx,← hy], apply h }

meta def ac_refine (e : expr) : tactic unit :=
refine ``(eq.mp _ %%e) ; ac_refl

meta def one_line (e : expr) : tactic format :=
do lbl ← pp e,
   asm ← infer_type e >>= pp,
   return format!"\t{asm}\n"

meta def side_conditions (e : expr) : tactic format :=
do let vs := e.list_meta_vars,
   ts ← mmap one_line vs.tail,
   let r := e.get_app_fn.const_name,
   return format!"{r}:\n{format.join ts}"

open monad

/-- tactic-facing function, similar to `interactive.tactic.generalize` with the
exception that meta variables -/
private meta def monotonicity.generalize' (h : name) (v : expr) (x : name) : tactic (expr × expr) :=
do tgt ← target,
   t ← infer_type v,
   tgt' ← do {
     ⟨tgt', _⟩ ← solve_aux tgt (tactic.generalize v x >> target),
     to_expr ``(λ y : %%t, Π x, y = x → %%(tgt'.binding_body.lift_vars 0 1)) }
   <|> to_expr ``(λ y : %%t, Π x, %%v = x → %%tgt),
   t ← head_beta (tgt' v) >>= assert h,
   swap,
   r ← mk_eq_refl v,
   solve1 $ tactic.exact (t v r),
   prod.mk <$> tactic.intro x <*> tactic.intro h

private meta def hide_meta_vars (tac : list expr → tactic unit) : tactic unit :=
focus1 $
do tgt ← target >>= instantiate_mvars,
   tactic.change tgt,
   ctx ← local_context,
   let vs := tgt.list_meta_vars,
   vs' ← mmap (λ v,
             do h ← get_unused_name `h,
                x ← get_unused_name `x,
                prod.snd <$> monotonicity.generalize' h v x) vs,
     tac ctx;
     vs'.mmap' (try ∘ tactic.subst)

meta def hide_meta_vars' (tac : itactic) : itactic :=
hide_meta_vars $ λ _, tac

end config

meta def solve_mvar (v : expr) (tac : tactic unit) : tactic unit :=
do gs ← get_goals,
   set_goals [v],
   target >>= instantiate_mvars >>= tactic.change,
   tac, done,
   set_goals $ gs

def list.minimum_on {α β} [linear_order β] (f : α → β) : list α → list α
| [] := []
| (x :: xs) := prod.snd $ xs.foldl (λ ⟨k,a⟩ b,
     let k' := f b in
     if k < k' then (k,a)
     else if k' < k then (k', [b])
     else (k,b :: a)) (f x, [x])

open format mono_selection

meta def best_match {β} (xs : list expr) (tac : expr → tactic β) : tactic unit :=
do t ← target,
   xs ← xs.mmap (λ x,
     try_core $ prod.mk x <$> solve_aux t (tac x >> get_goals)),
   let xs := xs.filter_map id,
   let r := list.minimum_on (list.length ∘ prod.fst ∘ prod.snd) xs,
   match r with
   | [(_,gs,pr)] :=  tactic.exact pr >> set_goals gs
   | [] := fail "no good match found"
   | _ :=
     do lmms ← r.mmap (λ ⟨l,gs,_⟩,
          do ts ← gs.mmap infer_type,
             msg ← ts.mmap pp,
             pure $ foldl compose "\n\n" $
               list.intersperse "\n" $ to_fmt l.get_app_fn.const_name :: msg),
        let msg := foldl compose "" lmms,
        fail format!("ambiguous match: {msg}\n\n" ++
          "Tip: try asserting a side condition to distinguish between the lemmas")
   end

meta def mono_aux (dir : parse side) :
  tactic unit :=
do t ← target >>= instantiate_mvars,
   ns ← get_monotonicity_lemmas t dir,
   asms ← local_context,
   rs ← find_lemma asms t ns,
   focus1 $ () <$ best_match rs (λ law, tactic.refine $ to_pexpr law)

/--
- `mono` applies a monotonicity rule.
- `mono*` applies monotonicity rules repetitively.
- `mono with x ≤ y` or `mono with [0 ≤ x,0 ≤ y]` creates an assertion for the listed
  propositions. Those help to select the right monotonicity rule.
- `mono left` or `mono right` is useful when proving strict orderings:
   for `x + y < w + z` could be broken down into either
    - left:  `x ≤ w` and `y < z` or
    - right: `x < w` and `y ≤ z`
- `mono using [rule1,rule2]` calls `simp [rule1,rule2]` before applying mono.
- The general syntax is
  `mono '*'? ('with' hyp | 'with' [hyp1,hyp2])? ('using' [hyp1,hyp2])? mono_cfg?`

To use it, first import `tactic.monotonicity`.

Here is an example of mono:

```lean
example (x y z k : ℤ)
  (h : 3 ≤ (4 : ℤ))
  (h' : z ≤ y) :
  (k + 3 + x) - y ≤ (k + 4 + x) - z :=
begin
  mono, -- unfold `(-)`, apply add_le_add
  { -- ⊢ k + 3 + x ≤ k + 4 + x
    mono, -- apply add_le_add, refl
    -- ⊢ k + 3 ≤ k + 4
    mono },
  { -- ⊢ -y ≤ -z
    mono /- apply neg_le_neg -/ }
end
```

More succinctly, we can prove the same goal as:

```lean
example (x y z k : ℤ)
  (h : 3 ≤ (4 : ℤ))
  (h' : z ≤ y) :
  (k + 3 + x) - y ≤ (k + 4 + x) - z :=
by mono*
```

-/
meta def mono (many : parse (tk "*")?)
  (dir : parse side)
  (hyps : parse $ tk "with" *> pexpr_list_or_texpr <|> pure [])
  (simp_rules : parse $ tk "using" *> simp_arg_list <|> pure []) :
  tactic unit :=
do hyps ← hyps.mmap (λ p, to_expr p >>= mk_meta_var),
   hyps.mmap' (λ pr, do h ← get_unused_name `h, note h none pr),
   when (¬ simp_rules.empty) (simp_core { } failed tt simp_rules [] (loc.ns [none]) >> skip),
   if many.is_some
     then repeat $ mono_aux dir
     else mono_aux dir,
   gs ← get_goals,
   set_goals $ hyps ++ gs

add_tactic_doc
{ name       := "mono",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.mono],
  tags       := ["monotonicity"] }

/--
transforms a goal of the form `f x ≼ f y` into `x ≤ y` using lemmas
marked as `monotonic`.

Special care is taken when `f` is the repeated application of an
associative operator and if the operator is commutative
-/
meta def ac_mono_aux (cfg : mono_cfg := { mono_cfg . }) :
  tactic unit :=
hide_meta_vars $ λ asms,
do try `[simp only [sub_eq_add_neg]],
   tgt ← target >>= instantiate_mvars,
   (l,r,id_rs,g) ← ac_monotonicity_goal cfg tgt
             <|> fail "monotonic context not found",
   ns ← get_monotonicity_lemmas tgt both,
   p ← mk_pattern g,
   rules ← find_rule asms ns p <|> fail "no applicable rules found",
   when (rules = []) (fail "no applicable rules found"),
   err ← format.join <$> mmap side_conditions rules,
   focus1 $ best_match rules (λ rule, do
     t₀ ← mk_meta_var `(Prop),
     v₀ ← mk_meta_var t₀,
     t₁ ← mk_meta_var `(Prop),
     v₁ ← mk_meta_var t₁,
     tactic.refine $ ``(apply_rel %%(g.rel_def) %%l %%r %%rule %%v₀ %%v₁),
     solve_mvar v₀ (try (any_of id_rs rewrite_target) >>
             ( done <|>
               refl <|>
               ac_refl <|>
               `[simp only [is_associative.assoc]]) ),
     solve_mvar v₁ (try (any_of id_rs rewrite_target) >>
             ( done <|>
               refl <|>
               ac_refl <|>
               `[simp only [is_associative.assoc]]) ),
     n ← num_goals,
     iterate_exactly (n-1) (try $ solve1 $ apply_instance <|>
       tactic.solve_by_elim { lemmas := some asms }))

open sum nat

/-- (repeat_until_or_at_most n t u): repeat tactic `t` at most n times or until u succeeds -/
meta def repeat_until_or_at_most : nat → tactic unit → tactic unit → tactic unit
| 0        t _ := fail "too many applications"
| (succ n) t u := u <|> (t >> repeat_until_or_at_most n t u)

meta def repeat_until : tactic unit → tactic unit → tactic unit :=
repeat_until_or_at_most 100000

@[derive _root_.has_reflect, derive _root_.inhabited]
inductive rep_arity : Type
| one | exactly (n : ℕ) | many

meta def repeat_or_not : rep_arity → tactic unit → option (tactic unit) → tactic unit
 | rep_arity.one  tac none := tac
 | rep_arity.many tac none := repeat tac
 | (rep_arity.exactly n) tac none := iterate_exactly' n tac
 | rep_arity.one  tac (some until) := tac >> until
 | rep_arity.many tac (some until) := repeat_until tac until
 | (rep_arity.exactly n) tac (some until) := iterate_exactly n tac >> until

meta def assert_or_rule : lean.parser (pexpr ⊕ pexpr) :=
(tk ":=" *> inl <$> texpr <|> (tk ":" *> inr <$> texpr))

meta def arity : lean.parser rep_arity :=
rep_arity.many <$ tk "*" <|>
rep_arity.exactly <$> (tk "^" *> small_nat) <|>
pure rep_arity.one

/--

`ac_mono` reduces the `f x ⊑ f y`, for some relation `⊑` and a
monotonic function `f` to `x ≺ y`.

`ac_mono*` unwraps monotonic functions until it can't.

`ac_mono^k`, for some literal number `k` applies monotonicity `k`
times.

`ac_mono := h`, with `h` a hypothesis, unwraps monotonic functions and
uses `h` to solve the remaining goal. Can be combined with `*` or `^k`:
`ac_mono* := h`

`ac_mono : p` asserts `p` and uses it to discharge the goal result
unwrapping a series of monotonic functions. Can be combined with * or
^k: `ac_mono* : p`

In the case where `f` is an associative or commutative operator,
`ac_mono` will consider any possible permutation of its arguments and
use the one the minimizes the difference between the left-hand side
and the right-hand side.

To use it, first import `tactic.monotonicity`.

`ac_mono` can be used as follows:

```lean
example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : x ≤ y) :
  (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
  ac_mono,
  -- ⊢ (m + x + n) * z ≤ z * (y + n + m)
  ac_mono,
  -- ⊢ m + x + n ≤ y + n + m
  ac_mono,
end
```

As with `mono*`, `ac_mono*` solves the goal in one go and so does
`ac_mono* := h₁`. The latter syntax becomes especially interesting in the
following example:

```lean
example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : m + x + n ≤ y + n + m) :
  (m + x + n) * z + k ≤ z * (y + n + m) + k :=
by ac_mono* := h₁.
```

By giving `ac_mono` the assumption `h₁`, we are asking `ac_refl` to
stop earlier than it would normally would.
-/
meta def ac_mono (rep : parse arity) :
         parse assert_or_rule? →
         opt_param mono_cfg { mono_cfg . } →
         tactic unit
 | none opt := focus1 $ repeat_or_not rep (ac_mono_aux opt) none
 | (some (inl h)) opt :=
do focus1 $ repeat_or_not rep (ac_mono_aux opt) (some $ done <|> to_expr h >>= ac_refine)
 | (some (inr t)) opt :=
do h ← i_to_expr t >>= assert `h,
   tactic.swap,
   focus1 $ repeat_or_not rep (ac_mono_aux opt) (some $ done <|> ac_refine h)
/-
TODO(Simon): with `ac_mono := h` and `ac_mono : p` split the remaining
  gaol if the provided rule does not solve it completely.
-/

add_tactic_doc
{ name       := "ac_mono",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.ac_mono],
  tags       := ["monotonicity"] }

attribute [mono] and.imp or.imp

end tactic.interactive
