import tactic.lint
import system.io
import all
open tactic native expr

#check expr.alpha_eqv

#eval to_bool $ `(∀ (n : nat) (m : rat), 1 = 1) =ₐ
      `(∀ (n : rat) (m : nat), 1 = 1)

#eval expr.hash (var 0)
#eval expr.hash `(∀ n t : nat, n + t = t + n)
#eval expr.hash `(∀ t m : nat , m + t = t + m)
#eval expr.hash (var 1)
meta def have_same_binder_types : expr → expr → bool
| (pi e_var_name e_bi e_var_type e_body) (pi f_var_name f_bi f_var_type f_body) := e_bi = f_bi ∧ have_same_binder_types e_body f_body
| _ _ := true

#eval have_same_binder_types `(∀ {n : nat} (m : rat), 1 = 1) `(∀ (n : nat) (m : rat), 1 = 1)
#eval have_same_binder_types `(∀ (n : nat) (m : rat), 1 = 1) `(∀ (n : nat) (m : rat), 1 = 1)
#eval have_same_binder_types `(∀ (n : rat) (m : rat), 1 = 1) `(∀ (n : rat) (m : rat), 1 = 1)
#eval to_bool $(`(∀ (t : rat) (m : rat), 1 = 1) :expr) = `(∀ (n : rat) (m : rat), 1 = 1)
alias one_mul ← cat
#print cat
attribute [to_additive cat_add] cat
#print cat_add
run_cmd do
  e ← get_env,
  ohashes ← e.mfold (mk_rb_map : rb_lmap nat name) (λ d (ohashes : rb_lmap nat name), do
    b₁ ← has_attribute' `alias d.to_name,
    b₂ ← is_in_mathlib d.to_name,
    if d.is_theorem && !d.is_auto_or_internal e && !b₁ && b₂ then do
      let h := d.type.hash,
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
