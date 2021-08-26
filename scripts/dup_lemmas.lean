import tactic.lint
import system.io
import all
open tactic native expr


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
      -- TODO check binder types here
      (guard (1 < ((ds.map declaration.type).pw_filter (λ e₁ e₂, (e₁ =ₐ e₂))).length) >>
        trace ((ds.map declaration.to_name)
        , (l.map (λ na, (e.decl_olean na).get_or_else "")).erase_dup
        )) <|>
      skip)
    else
      skip)
