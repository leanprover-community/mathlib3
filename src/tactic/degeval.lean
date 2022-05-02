import tactic.move_add
import data.polynomial.degree.lemmas

open tactic interactive expr

namespace tactic.interactive
setup_tactic_parser
#check monoid.npow
#check @has_pow.pow


example {n : ℕ} : 0 = n :=
by do
  `(%%tl = %%tr) ← target,
  trace tl.to_nat
--#exit
--
--  unify tl `(has_zero.zero.{0} nat nat.has_zero),
--  let bo : bool := (tl = has_zero.zero nat nat.has_zero),
--  trace tl.to_string


/-
meta def monomial_weight (e : expr) : expr :=
match e.app_fn with
| `(coe_fn $ polynomial.monomial %%n) := n
| `(monoid.npow %%n %%x) := n
| (app f a) := if f.get_app_fn.const_name = `has_pow.pow then
                        f.get_app_args else []
--                        [a] else []
--| (app f a) := if f.get_app_fn.const_name = `polynomial.C then
--                  [] else
--                []
/-
                if f.get_app_fn.const_name = `has_pow.pow then
                match f.get_app_args with
                | (x::n) := n
                | _ := []
                end

                  [a]
                else
-/
| _ := []
end
-/
#check list.erase
#check expr.to_nat
meta def guess_deg (e : expr) : tactic expr :=
do n0 ← to_expr ``(nat.zero),
   n1 ← to_expr ``(bit1 nat.zero),
   pol ← to_expr ``(polynomial.X),pt ← infer_type pol, trace pt,
match e.app_fn with
--| (expr.app op a) := if (op.get_app_fn.const_name = `has_add.add) then a else a
| `(coe_fn $ polynomial.monomial %%n) := return n
| `(coe_fn $ polynomial.C) := --do `(some %%arg) ← e.get_app_args.nth 0, trace arg,
                              return n0
| a := do bo ← (succeeds $ unify e pol), if bo then return n1 else

--let cond : bool := e = pol, trace cond,trace e, trace pol,
       (--if cond then (do return n1) else
            (do let margs := e.get_app_args,
            hh ← margs.nth 4,
            return hh) <|>
            (do val ← to_expr ``(polynomial.nat_degree), return $ expr.mk_app val [e]))
--| `(polynomial.C %%a) := return a
--| a := do trace a, if a.const_name = ``polynomial.C then (do n0 ← to_expr ``(nat.zero), return n0) else
--    (do val ← to_expr ``(polynomial.nat_degree), return $ expr.mk_app val [e])
end

meta def get_factors_add : expr → tactic expr
| `(has_mul.mul %%a %%b) := do ga ← get_factors_add a, gb ← get_factors_add b,
                              tot ← mk_app `has_add.add [ga, gb],
                              return tot
--| `(expr.app $ coe_fn $ polynomial.monomial %%n) := [n]
| e := do ge ← guess_deg e, return ge


meta def fina : tactic unit :=
do `(polynomial.nat_degree %%tl = %%tr) ← target,
  let summ := (get_summands tl),
  let rere := summ.map get_factors_add,-- (get_factors_add t),
  trace rere
--  ret ← rere.foldl guess_deg t,


end tactic.interactive

open polynomial
open_locale polynomial
variables {R : Type*} [semiring R] {f g h : R[X]} {a b c d e : R}

lemma pro {h : C d ≠ 0} :
  nat_degree (monomial 5 c * monomial 1 c + f + monomial 7 d + C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + C d * X ^ 10 + C e * X + bit0 0 : R[X]) = 10 :=
begin
  fina,
end


meta def rec_ret_fac_add : expr → tactic (list (list expr))
| e@`(%%_ + %%_)     := return_factors e
| (expr.lam _ _ _ e) := rec_ret_fac e
| (expr.pi  _ _ _ e) := rec_ret_fac e
| e                  := do erf ← e.get_app_args.map rec_ret_fac,
                          do ferf ← list.list_to_cat (erf),
                          return ferf



meta def get_factors : expr → tactic (list expr)
| `(has_mul.mul %%a %%b) := do ga ← get_factors a, gb ← get_factors b, return (ga ++ gb)
--| `(expr.app $ coe_fn $ polynomial.monomial %%n) := [n]
| e := do ge ← guess_deg e, return [ge]

meta def return_factors (e : expr) : tactic (list (list expr)) :=
--let li_summands := get_summands e in
do let ges := get_summands e in
  do gls ← ges.mmap get_factors,
  return gls

def list.list_to_cat {α : Type*} : list (list α) → list α
| [] := []
| (l::ls) := l ++ ls.list_to_cat

meta def rec_ret_fac : expr → tactic (list (list expr))
| e@`(%%_ + %%_)     := return_factors e
| (expr.lam _ _ _ e) := rec_ret_fac e
| (expr.pi  _ _ _ e) := rec_ret_fac e
| e                  := do erf ← e.get_app_args.map rec_ret_fac,
                          do ferf ← list.list_to_cat (erf),
                          return ferf

meta def fina : tactic unit :=
do t ← target,
  let rere := (rec_ret_fac t),
  ret ← rere.foldl guess_deg t,


end tactic.interactive

open polynomial
open_locale polynomial
variables {R : Type*} [semiring R] {f g h : R[X]} {a b c d e : R}

lemma pro {h : C d ≠ 0} :
  nat_degree (monomial 5 c * monomial 1 c + f + monomial 7 d + C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + C d * X ^ 10 + C e * X : R[X]) = 10 :=
begin
  fina,
end


/-
meta def guess_deg : expr → tactic expr
--match e.app_fn with
--| (expr.app op a) := if (op.get_app_fn.const_name = `has_add.add) then a else a
| `(coe_fn $ polynomial.monomial %%n) := return n
--| `(polynomial.C %%a) := a
| a := do val ← to_expr ``(polynomial.nat_degree), return $ expr.mk_app val [a]
--end

meta def to_oper (f₁ f₂ : name) : expr → tactic expr
| (expr.app (expr.app op a) b) := do oa ← to_oper a, ob ← to_oper b,
                                    if op.get_app_fn.const_name = f₁ then
                                       (mk_app f₂ [oa, ob]) else (return (op oa ob))
--  The rest of the match is unchanged
| (expr.lam a b c e)         := do oc ← to_oper c, oe ← to_oper e,
                                  return (expr.lam a b oc oe)
| (expr.pi  a b c e)         := do oc ← to_oper c, oe ← to_oper e,
                                  return (expr.pi  a b oc oe)
| (expr.elet a b c e)        := do ob ← to_oper b, oc ← to_oper c, oe ← to_oper e,
                                  return (expr.elet  a ob oc oe)
| (expr.app a b)             := do oa ← to_oper a, ob ← to_oper b,
                                  return (expr.app oa ob)
| (expr.mvar u p e)          := do oe ← to_oper e,
                                  return (expr.mvar u p oe)
| (expr.local_const u p b e) := do oe ← to_oper e,
                                  return (expr.local_const u p b oe)
| (expr.macro md le)         := do ole ← le.mmap (to_oper),
                                  return (expr.macro md ole)
| e                          := return e



meta def recurse_on_expr_ : expr → list expr
| e@`(%%_ + %%_)     := get_summands e
| (expr.app f a)     := let rho :=f.get_app_args.map get_summands in
                          match rho with
                          | [] := []
                          | (r::rs) := r
                          end
--                          | _ := []
--                        return $ list.foldl _ _ rho
| (expr.lam _ _ _ e) := recurse_on_expr_ e
| (expr.pi  _ _ _ e) := recurse_on_expr_ e
| e                  := [e]

/--  Assuming that the expression `e` consists of a product of `C a, monomial n b, X, X ^ d`,
`get_exps` extracts the list of what should be the degrees of the factors. -/
meta def get_exps : expr → list expr
| `(has_mul.mul %%a %%b) := get_exps a ++ get_exps b
--| `(expr.app $ coe_fn $ polynomial.monomial %%n) := [n]
| e := monomial_weight e
/-
| (expr.app ft a) := match ft.app_fn with
  | `(coe_fn $ polynomial.monomial %%n) := [n]
  | e := []
  end


 nd.get_app_fn.const_name = `polynomial.monomial then
| (expr.app nd a) := if nd.get_app_fn.const_name = `polynomial.monomial then
          match a.get_app_args with
          | [n, r] := [n]
          | _ := [] end
          else []
| e := []
-/
--          end

-/
.
#check coe_fn
end tactic.interactive

open polynomial
open_locale polynomial
variables {R : Type*} [semiring R] {f g h : R[X]} {a b c d e : R}

lemma pro {h : C d ≠ 0} :
  nat_degree (monomial 5 c * monomial 1 c + f + monomial 7 d + C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + C d * X ^ 10 + C e * X : R[X]) = 10 :=
by do t ← target,
--    let rer := tactic.interactive.recurse_on_expr_ t,trace "rer",trace rer,trace "rer finito",trace t,
    match t.is_eq with
    | none := trace "target is not an equality"
    | some (tl, tr) := do
--      trace tl,
      match tl with
      | (expr.app nd a) := if nd.get_app_fn.const_name = `polynomial.nat_degree then
          (let sus := (interactive.get_summands a) in
            let fsu : list (list expr) := sus.map tactic.interactive.get_factors in
            match fsu with
            | [] := trace fsu
            | (fff::fffs) := trace $ fff.map tactic.interactive.guess_deg
--            let gd :=
--            trace fsu
--            else skip
--            end
--            sorry
--#exit
--          let ee : list (list expr) := list.map tactic.interactive.get_exps sus in
/-
          match sus with
          | [] := skip
          | (s1:: ss) := let vv := tactic.interactive.get_exps s1 in skip
--            trace ee
            --trace format!"{s1.local_pp_name} and {vv}"
          end
-/
--          trace ee
          )
           else skip
      | e := trace "no"
    end
    end
--        let s := interactive.get_summands tl,
--        let f := interactive.recurse_on_expr none [] t,
--    trace f
