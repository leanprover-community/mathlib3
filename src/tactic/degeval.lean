import tactic.move_add
import data.polynomial.degree.lemmas

open tactic interactive expr

namespace tactic.interactive
setup_tactic_parser
#check monoid.npow
#check @has_pow.pow
meta def monomial_weight (e : expr) : list expr :=
match e.app_fn with
| `(coe_fn $ polynomial.monomial %%n) := [n]
| `(monoid.npow %%n %%x) := [n]
| (app f a) := if f.get_app_fn.const_name = `has_pow.pow then
                        f.get_app_args else []
--                        [a] else []
| (app f a) := if f.get_app_fn.const_name = `polynomial.C then
                  [] else
                []
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

.
#check coe_fn
end tactic.interactive

open polynomial
open_locale polynomial
variables {R : Type*} [semiring R] {f g h : R[X]} {a b c d e : R}

lemma pro {h : C d ≠ 0} :
  nat_degree (monomial 5 c * monomial 1 c + f + monomial 7 d + C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + C d * X ^ 10 + C e * X : R[X]) = 10 :=
by do t ← target,
    --trace t,
    match t.is_eq with
    | none := trace "target is not an equality"
    | some (tl, tr) := do
      match tl with
      | (expr.app nd a) := if nd.get_app_fn.const_name = `polynomial.nat_degree then
          (let sus := (interactive.get_summands a) in
          let ee : list (list expr) := list.map tactic.interactive.get_exps sus in
          match sus with
          | [] := skip
          | (s1:: ss) := let vv := tactic.interactive.get_exps s1 in
            trace ee
            --trace format!"{s1.local_pp_name} and {vv}"
          end
--          trace ee
          )
           else skip
      | e := trace "no"
    end
    end
--        let s := interactive.get_summands tl,
--        let f := interactive.recurse_on_expr none [] t,
--    trace f
