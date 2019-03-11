
import tactic.monotonicity
import data.serial.basic
-- import data.nat.nursery
-- import tactic.nursery
import tactic.norm_num
import tactic.basic
import category.basic

namespace tactic

open serial
open tactic
open tactic.interactive (unfold norm_num trivial simp ac_mono)
open interactive

meta def mk_up (u : level) (e : expr) : tactic expr :=
do t  ← infer_type e,
   u' ← mk_meta_univ,
   (t,e)  ← mcond (succeeds $ infer_type t >>= unify (expr.sort (level.succ u')))
     (pure (t,e))
     (prod.mk <$> mk_app ``plift [t] <*> mk_app ``plift.up [e]),
   let up : expr := expr.const ``ulift.up [u,u'],
   pure $ up t e

meta def mk_down (u : level) (e t : expr) : tactic expr :=
do u' ← mk_meta_univ,
   e ← mk_app ``ulift.down [e],
   mcond (succeeds $ infer_type t >>= unify (expr.sort (level.succ u')))
     (pure (e))
     (mk_app ``plift.down [e])

meta def mk_ulift (u : level) (t : expr) : tactic expr :=
do u' ← mk_meta_univ,
   t  ← mcond (succeeds $ infer_type t >>= unify (expr.sort (level.succ u')))
     (pure t)
     (mk_app ``plift [t] <|> do { t ← pp t, fail format!"plift {t}" }),
   let ulift_t : expr := expr.const ``ulift [u,u'],
   pure $ ulift_t t

meta def induction_state := (list (name × list ((expr × option expr) × expr)))

meta def mk_encode (n : name) (u : level) : tactic $ bool × induction_state :=
do x ← intro1,
   b ← is_recursive_type n,
   when b $ do {
     size ← to_expr ``(sizeof %%x) >>= mk_up u,
     refine ``(encode %%size >> _) },
   vs ← better_induction x,
   gs ← get_goals,
   prod.mk b <$> mzip_with (λ (g : ℕ × expr) (c : name × list (expr × option expr) × list (name × expr)),
     do let ⟨i,g⟩ := g,
        set_goals [g],
        when (gs.length ≠ 1) $ refine ``(write_word (fin.of_nat %%(reflect i)) >> _),
        let ⟨c,vs,_⟩ := c,
        vs' ← vs.mmap $ infer_type ∘ prod.fst,
        vs.mmap' (λ v,
          do t ← infer_type v.1,
             match v.2 with
             | none := do
               v ← mk_up u v.1,
               refine ``(encode %%v >> _)
             | (some rec_call) := do
               refine ``(%%rec_call >> _)
             end ),
        refine ``(pure punit.star),
        (c,vs.zip vs') <$ done) gs.enum vs

meta def mk_parser (u : level) :
  expr →
  list ((expr × option expr) × expr) →
  list (name × expr) →
  option expr →
  tactic unit
| e [] _ rec_call := refine ``(pure %%e)
| e (((v,rec),t) :: vs) σ rec_call :=
do let t := t.instantiate_locals σ,
   ulift_t ← mk_ulift u t,
   v' ← match rec_call <* rec with
   | none :=
     do refine ``(decode %%ulift_t >>= _),
        v' ← intro1,
        mk_down u v' t
   | (some rec_call) :=
     refine ``(%%rec_call >>= _) >> intro1
   end,
   mk_parser (e v') vs ( (v.local_uniq_name,v') :: σ ) rec_call

meta def mk_decode (is_rec : bool) (args : list expr) (u : level) (n : name) (pat : induction_state) : tactic unit :=
do if pat.length = 1 then do
       let ⟨c,vs⟩ := pat.head,
       c ← mk_const c,
       mk_parser u (c.mk_app args) vs [] none
   else do
     rec_call ← if is_rec then do
       nat_t ← mk_ulift u `(nat),
       refine ``(decode %%nat_t >>= _),
       n ← intro1,
       refine ``(recursive_parser (ulift.down %%n) _),
       some <$> intro `rec_call
     else pure none,
     refine ``(select_tag _),
     pat.enum.mmap' $ λ ⟨i,c,vs⟩, do {
       v₀ ← mk_mvar, v₁ ← mk_mvar,
       refine ``((fin.of_nat %%(reflect i),%%v₀) :: %%v₁),
       set_goals [v₀],
       c ← mk_const c,
       mk_parser u (c.mk_app args) vs [] rec_call, done,
       set_goals [v₁] },
     refine ``([])

meta def reduce_select_tag (tag : expr) : expr → tactic unit
| `( list.cons (fin.of_nat %%n, %%br) %%brs ) :=
  if n =ₐ tag then do
    v ← mk_mvar,
    to_expr ``(read_write_tag_hit %%v) >>= rewrite_target <|>
      (to_expr ``(read_write_tag_hit' %%v) >>= rewrite_target),
    gs ← get_goals,
    set_goals [v], tactic.interactive.norm_num [] (loc.ns [none]), done,
    set_goals gs
  else do
    v ← mk_mvar,
    to_expr ``(read_write_tag_miss %%v) >>= rewrite_target,
    gs ← get_goals,
    set_goals [v],
    do { applyc ``fin.ne_of_vne,
         let rs := list.map simp_arg_type.expr
             [``(fin.of_nat),``(fin.val),``(nat.succ_eq_add_one)],
         tactic.interactive.norm_num rs (loc.ns [none]), done },
    set_goals gs,
    reduce_select_tag brs
| e := failed

meta def match_sum_branch : tactic unit :=
do brs ← mk_mvar, tag ← mk_mvar,
   tgt ← target,
   mcond (succeeds $
     to_expr ``(select_tag %%brs -<< (write_word (fin.of_nat %%tag) >> _) = _) >>= change <|>
       (to_expr ``(select_tag %%brs -<< (write_word (fin.of_nat %%tag)) = _) >>= change))
   (do brs ← instantiate_mvars brs,
       tag ← instantiate_mvars tag,
       reduce_select_tag tag brs)
   skip

meta def prove_bound (n : name) : tactic unit :=
solve1 $ do
  h ← get_local `h,
  transitivity; [skip, () <$ apply h],
  dunfold_target [``sizeof],
  dunfold_target [``sizeof,``has_sizeof.sizeof,n <.> "sizeof"],
  try $ to_expr  ``(1 + 0 ≤ _) >>= change,
  (`[ac_mono*]; try ( applyc ``nat.zero_le) ) <|> reflexivity,
  done <|> do {
    repeat $ applyc ``nat.le_add_right <|> applyc ``nat.le_add_of_le_left,
    try $ reflexivity },
  return ()

meta def mk_serial_correctness (is_rec : bool) (n encode_n decode_n : name) : tactic unit :=
do let rules := [``has_bind.and_then,
                 ``encode_decode_bind,``encode_decode_bind',
                 ``encode_decode_pure],
   rules ← rules.mmap ((<$>) simp_arg_type.expr ∘ resolve_name),
   w ← intro1,
   dunfold_target [decode_n],
   dunfold_target [encode_n],
   simp none ff rules [] (loc.ns [none]),
   hs ← if is_rec then
   do { tactic.interactive.generalize `h () (``(sizeof %%w),`k),
        k ← get_local `k,
        h ← get_local `h,
        replace `h ``(le_of_eq %%h),
        revert k,
        better_induction w <* all_goals (() <$ intro_lst [`k,`h]) }
   else better_induction w,
   gs ← get_goals,
   mzip_with' (λ g (h : name × list (expr × option expr) × list (name × expr)), do {
     set_goals [g],
     let ⟨_,ih,_⟩ := h,
     let ih := ih.filter_map prod.snd,
     when is_rec $ `[rw recursive_parser_unfold],
     solve1 $ do {
       match_sum_branch,
       ih.mmap' $ λ hh,
       do { try $ simp none ff rules [] (loc.ns [none]),
            bound ← mk_mvar,
            mcond (succeeds $ to_expr ``((_ >>= _) -<< (_ >> _) = _) >>= change)
              (do dunfold_target [``has_bind.and_then],
                  to_expr ``(read_write_mono $ %%hh _ %%bound) >>= rewrite_target)
              (do to_expr ``((_ >>= _) -<< _ = _) >>= change,
                  to_expr ``(read_write_mono_left $ %%hh _ %%bound) >>= rewrite_target),
            gs ← get_goals, set_goals [bound],
            h ← get_local `h,
            applyc ``nat.le_sub_right_of_add_le,
            prove_bound n,
            set_goals gs },
       simp none ff rules [] (loc.ns [none]) <|> reflexivity },
     when is_rec $ prove_bound n,
     done,
     pure ()
   }) gs hs

meta def mk_serial_instance : tactic unit :=
expand_untrusted $
do tgt ← target,
   let t := tgt.app_arg,
   let args := t.get_app_args,
   (expr.sort (level.succ u)) ← infer_type t,
   let n := t.get_app_fn.const_name,
   d ← get_decl n,
   let t := d.is_trusted,
   enc ← mk_mvar,
   dec ← mk_mvar,
   correct ← mk_mvar,
   reset_instance_cache,
   refine ``( { encode := %%enc,
                decode := %%dec,
                correctness := %%correct } ),
   let decode_n := n <.> "decode",
   let encode_n := n <.> "encode",
   set_goals [enc],
   (is_rec,vs) ← extract_def' encode_n t (mk_encode n u),
   set_goals [dec],
   extract_def' decode_n t (mk_decode is_rec args u n vs),
   set_goals [correct],
   mk_serial_correctness is_rec n encode_n decode_n

@[derive_handler] meta def serial_derive_handler : derive_handler :=
instance_derive_handler ``serial mk_serial_instance

end tactic
