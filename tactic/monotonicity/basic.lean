
import tactic.basic
import category.basic

namespace tactic.interactive
open tactic list
open lean lean.parser  interactive
open interactive.types

structure mono_cfg :=
  (unify := ff)

@[derive [decidable_eq,has_reflect]]
inductive mono_selection : Type
| left : mono_selection
| right : mono_selection
| both : mono_selection

section compare

parameter opt : mono_cfg

meta def compare (e₀ e₁ : expr) : tactic unit := do
if opt.unify then do
guard (¬ e₀.is_mvar ∧ ¬ e₁.is_mvar),
unify e₀ e₁
else is_def_eq e₀ e₁

meta def find_one_difference
: list expr → list expr → tactic (list expr × expr × expr × list expr)
 | (x :: xs) (y :: ys) :=
   do c ← try_core (compare x y),
      if c.is_some
      then prod.map (cons x) id <$> find_one_difference xs ys
      else do
        guard (xs.length = ys.length),
        mzip_with' compare xs ys,
        return ([],x,y,xs)
 | xs ys := fail format!"find_one_difference: {xs}, {ys}"

end compare

def last_two {α : Type*} (l : list α) : option (α × α) :=
match l.reverse with
| (x₁ :: x₀ :: _) := some (x₀, x₁)
| _ := none
end

meta def match_imp : expr → tactic (expr × expr)
 | `(%%e₀ → %%e₁) :=
   do guard (¬ e₁.has_var),
      return (e₀,e₁)
 | _ := failed

meta def monotoncity.check_rel (xs : list expr) (l r : expr) : tactic unit :=
do (_,x,y,_) ← find_one_difference { mono_cfg . }
               l.get_app_args r.get_app_args,
   when (¬ l.get_app_fn = r.get_app_fn)
     (fail format!"{l} and {r} should be the f x and f y for some f"),
   t ← infer_type (list.ilast xs),
   (l',r') ← last_two t.get_app_args
     <|> match_imp t
     <|> fail format!"expecting assumption {t} to be a relation R x y",
   when (¬ x.is_local_constant) (fail format!"expecting a bound variable: {x}"),
   when (¬ y.is_local_constant) (fail format!"expecting a bound variable: {y}"),
   when ([l',r'] ≠ [x,y] ∧ [l',r'] ≠ [y,x])
     (fail "assumption {t} should be relating variables {l'} and {r'}"),
   return ()

meta def monotoncity.check_imp (x₀ : expr) : list expr → tactic unit
| (x₁ :: xs) := infer_type x₁ >>= monotoncity.check_rel xs.reverse x₀
| _ := fail "monotoncity.check_imp"

meta def monotoncity.check (lm_n : name) (prio : ℕ) (persistent : bool) : tactic unit :=
do lm ← mk_const lm_n,
   lm_t ← infer_type lm,
   (xs,h) ← mk_local_pis lm_t,
   x ← try_core (monotoncity.check_imp h xs.reverse),
   match x with
    | (some x) :=
      (do (l,r) ← last_two h.get_app_args,
          monotoncity.check_rel xs l r) <|> return x
    | none :=
      do (l,r) ← last_two h.get_app_args <|> fail format!"expecting: R x y\nactual: {h}",
         monotoncity.check_rel xs l r
   end

meta instance : has_to_format mono_selection :=
⟨ λ x, match x with
| mono_selection.left := "left"
| mono_selection.right := "right"
| mono_selection.both := "both"
end ⟩

meta def side : parser mono_selection :=
with_desc "expecting 'left', 'right' or 'both' (default)" $
do some n ← optional ident | pure mono_selection.both,
   if n = `left then pure $ mono_selection.left
   else if n = `right then pure $ mono_selection.right
   else if n = `both then pure $ mono_selection.both
   else fail format!"invalid argument: {n}, expecting 'left', 'right' or 'both' (default)"

@[user_attribute]
meta def monotonicity.attr : user_attribute unit mono_selection :=
{ name  := `monotonic
, descr := "monotonicity of functions wrt relations: R₀ x y → R₁ (f x) (f y)"
-- , after_set := some monotoncity.check
, parser := side }

meta def filter_instances (e : mono_selection) (ns : list name) : tactic (list name) :=
ns.mfilter $ λ n,
do d ← user_attribute.get_param_untyped monotonicity.attr n,
   d ← to_expr ``(id %%d) >>= eval_expr mono_selection,
   return (e = d)

meta def get_monotonicity_lemmas (e : mono_selection) : tactic (list name) :=
do ns  ← attribute.get_instances `monotonic,
   ns' ← filter_instances e ns,
   if e ≠ mono_selection.both then (++) ns' <$> filter_instances mono_selection.both ns
               else pure ns'

end tactic.interactive

attribute [monotonic] add_le_add mul_le_mul neg_le_neg mul_lt_mul_of_pos_left mul_lt_mul_of_pos_right
attribute [monotonic left] add_lt_add_of_le_of_lt mul_lt_mul'
attribute [monotonic right] add_lt_add_of_lt_of_le mul_lt_mul
