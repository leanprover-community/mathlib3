import data.polynomial.degree.definitions
import tactic

open polynomial tactic
open_locale polynomial classical

meta def is_sum : expr → bool
| `(%%_ + %%_) := tt
| _            := ff

meta def get_monomials_from_sum_aux : expr → list (expr × option ℕ) → list (expr × option ℕ)
| `(%%a + %%b) l := do
  let as := match a.app_fn with
  | `(coe_fn $ polynomial.monomial %%n) := (a, expr.to_nat n) :: l
  | _ := if (is_sum a) then get_monomials_from_sum_aux a l else (a, none) :: l
  end,
  let bs := match b.app_fn with
  | `(coe_fn $ polynomial.monomial %%n) := (b, expr.to_nat n) :: l
  | _ := if (is_sum b) then get_monomials_from_sum_aux b l else (b, none) :: l
  end,
  as ++ bs
| _ l := l

meta def order_fn : expr × option ℕ → expr × option ℕ → bool
| (_, some a) (_, some b) := a < b
| (_, none) (_, some _) := tt
| (_, some _) (_, none) := ff
| _ _ := tt

meta def get_sorted_monomials_from_sum (e : expr) : list expr :=
do
  let l := (get_monomials_from_sum_aux e []).qsort order_fn,
  l.map (λ x, x.1)

meta def build_sum : expr → list expr → tactic expr
| ei ((e : expr)::es) := do
  e' ← build_sum ei es,
  mk_app `has_add.add [e', e]
| ei [] := pure ei

meta def sort_monomials_sum (e : expr) : tactic unit :=
match get_sorted_monomials_from_sum e with
| ei::es := do
  el' ← build_sum ei es.reverse,
  e_eq ← mk_app `eq [e, el'],
  n ← get_unused_name,
  assert n e_eq,
  reflexivity <|> `[{ simp only [add_comm, add_assoc, add_left_comm], done, }],
  h ← get_local n,
  rewrite_target h,
  clear h
| [] := skip
end

meta def sort_monomials : tactic unit :=
do
  -- e ← get_local `h,
  -- t ← infer_type e,
  t ← target,
  match t.is_eq with
  | none          := fail "not an equality"
  | some (el, er) := do
    sort_monomials_sum el,
    sort_monomials_sum er
  end

example {R : Type*} [semiring R] {r s t u : R} (r0 : t ≠ 0) :
  C u * X + X ^ 5 + C s + C t * X ^ 2 + X ^ 8 = 0 :=
begin
  try { unfold X },
  try { rw ← C_1 },
  repeat { rw ← monomial_zero_left },
  repeat { rw monomial_pow },
  repeat { rw monomial_mul_monomial },
  try { simp only [zero_add, add_zero, mul_one, one_mul, one_pow] },
  sort_monomials, sort_monomials,
  -- ⇑(monomial 0) s + (⇑(monomial 1) u + (⇑(monomial 2) t + (⇑(monomial 5) 1 + ⇑(monomial 8) 1))) = 0
end
