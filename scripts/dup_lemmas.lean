import tactic.lint
import system.io
import algebra.ring.basic
import all
open tactic native expr



section hash
-- goal is to create a hash function that identifies lemmas with the same arguments in different
-- orders, mostly looks like we go mod 2^31
-- binder type changes should give different hashes
-- idea is that the assumptions are a dag
-- some assumptions can really be permuted, m n of same type
-- e.g

lemma lem1 {R : Type*} [group R] (x y : R) (h : x * y = 1) : x * y * y⁻¹ = y⁻¹ := by rw [h]; group
lemma lem2 {R : Type*} (x y : R) [group R] (h : x * y = 1) : x * y * y⁻¹ = y⁻¹ := by rw [h]; group

lemma lem1 {R : Type*} [group R] (x y : R) (h : x * y = 1) : x * y * y⁻¹ = y⁻¹ := by rw [h]; group
lemma lem2 {R : Type*} (x y : R) [group R] (h : x * y = 1) : x * y * y⁻¹ = y⁻¹ := by rw [h]; group


/- we have

R__________
|       \  \
group R  x  y
|_______/__/
h

vs.
R_______
|  \    \
x   y   group R
|__/____/
h


-/

meta
def var_order (e : expr) : list ℕ :=
e.fold [] (λ e' n es, let o := e'.match_var in
  if o.is_some ∧ n ≤ o.get_or_else 0 then insert (o.get_or_else 0 - n) es else es)
#check expr.list_local_consts'
#check expr.list_local_consts
#eval var_order $ let e := `(∀ t r n : nat, (λ h, h + n) 0 + t = t + n) in e.nth_binding_body e.pi_arity
#eval var_order $ let e := `(∀ t r n : nat, n + t = t + n) in e.nth_binding_body e.pi_arity
#eval var_order $ let e := `(∀ r t n : nat, n + t = t + n) in e.nth_binding_body e.pi_arity
#eval var_order $ let e := `(∀ a b c : nat, c + b = b + c) in e.nth_binding_body e.pi_arity

run_cmd (tactic.open_pis `(∀ a b c : nat, c + b = b + c) >>= trace)
#check tactic.kdepends_on
section
open interaction_monad.result
meta
def tlt (n m : expr) (s : tactic_state) : bool :=
match tactic.kdepends_on n m transparency.reducible s with
| (success b _) := b
| (exception _ _ _) := ff
end
end
meta
def o_sort : list expr → expr → tactic (list expr) :=
λ l e,
do
  s ← tactic.read,
  let li := e.list_local_consts,
  return $ l.qsort (λ n m,
  if tlt n m s then
    ff
  else if tlt m n s then
    tt
  else li.index_of m < li.index_of n)

#check expr.abstract_locals
meta
def dup_hash : expr → tactic ℕ :=
λ e,
do
  (los, d) ← tactic.open_pis e,
  l ← o_sort los.reverse d,
  -- trace l,
  let o := d.abstract_locals (l.map expr.local_uniq_name),
  -- trace o,
  -- trace $ tactic.kdepends_on los.head los.tail.head,
  -- trace $ tactic.kdepends_on los.tail.head los.head,
  return o.hash
run_cmd dup_hash `(∀ (a : nat) (b : fin a) (c : nat), c + b = b + c) >>=trace
run_cmd dup_hash `(∀ (a : nat) (c : nat) (b : fin a), c + b = b + c) >>=trace
run_cmd dup_hash `(∀ (c : nat) (a : nat) (b : fin a), c + b = b + c) >>=trace
end hash

#check expr.alpha_eqv

#eval to_bool $ `(∀ (n : nat) (m : rat), 1 = 1) =ₐ
      `(∀ (n : rat) (m : nat), 1 = 1)

#eval expr.hash (var 0)
#eval expr.hash (var 1)
#eval expr.hash `(∀ n t : nat, n + t = t + n)
#eval expr.hash `(∀ t n : nat, n + t = t + n)
#eval expr.alpha_eqv `(∀ n t : nat, n + t = t + n) `(∀ m t : nat, m + t = t + m)
-- #check expr.has_decidable_eq.eq
#eval to_bool $ (`(∀ n t : nat, n + t = t + n) : expr)= `(∀ m t : nat, m + t = t + m)
open tactic
#eval expr.hash (var 1)
meta def have_same_binder_types : expr → expr → bool
| (pi e_var_name e_bi e_var_type e_body) (pi f_var_name f_bi f_var_type f_body) :=
  (e_bi = f_bi) && have_same_binder_types e_body f_body
| _ _ := true

#eval have_same_binder_types `(∀ {n : nat} (m : rat), 1 = 1) `(∀ (n : nat) (m : rat), 1 = 1)
#eval have_same_binder_types `(∀ (n : nat) (m : rat), 1 = 1) `(∀ (n : nat) (m : rat), 1 = 1)
#eval have_same_binder_types `(∀ (n : rat) (m : rat), 1 = 1) `(∀ (n : rat) (m : rat), 1 = 1)
#eval to_bool $(`(∀ (t : rat) (m : rat), 1 = 1) :expr) = `(∀ (n : rat) (m : rat), 1 = 1)
-- alias one_mul ← cat
-- #print cat
-- attribute [to_additive cat_add] cat
-- #print cat_add
run_cmd do
  e ← get_env,
  ohashes ← e.mfold (mk_rb_map : rb_lmap nat name) (λ d (ohashes : rb_lmap nat name), do
    b₁ ← has_attribute' `alias d.to_name,
    b₂ ← is_in_mathlib d.to_name,
    if d.is_theorem && !d.is_auto_or_internal e && !b₁ && b₂ then do
      h ← dup_hash d.type,
      -- let h := d.type.hash,
      return (ohashes.insert h d.to_name)
    else return ohashes) ,
  ohashes.mfold () (λ h l _, do if (l.length > 1) then (do
      ds ← l.mmap get_decl,
      (guard (1 < ((ds.map declaration.type).pw_filter
        (λ e₁ e₂, e₁ =ₐ e₂ ∧ have_same_binder_types e₁ e₂)).length) >>
        trace ((ds.map declaration.to_name)
        , (l.map (λ na, (e.decl_olean na).get_or_else "")).erase_dup
        )) <|>
      skip)
    else
      skip)

-- ([exists_comm, exists_swap], [/home/alex/mathlib/src/logic/basic.lean])
-- ([classical.not_ball, not_ball], [/home/alex/mathlib/src/logic/basic.lean])
-- ([imp_true_iff, forall_true_iff], [/home/alex/mathlib/src/logic/basic.lean])
-- ([imp_or_distrib', imp_or_distrib], [/home/alex/mathlib/src/logic/basic.lean])

-- #check not_ball
-- #check imp_true_iff
-- #check forall_true_iff
-- #check neg_add_self
-- #check add_left_neg
