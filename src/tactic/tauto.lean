
import logic.basic tactic.basic

namespace tactic

open expr
open tactic.interactive ( casesm constructor_matching )

/--
  find all assumptions of the shape `¬ (p ∧ q)` or `¬ (p ∨ q)` and
  replace them using de Morgan's law.
-/
meta def distrib_not : tactic unit :=
do hs ← local_context,
   hs.for_each $ λ h,
    all_goals $
    iterate_at_most 3 $
      do h ← get_local h.local_pp_name,
         e ← infer_type h,
         match e with
         | `(¬ _ = _) := replace h.local_pp_name ``(mt iff.to_eq %%h)
         | `(_ ≠ _)   := replace h.local_pp_name ``(mt iff.to_eq %%h)
         | `(_ = _)   := replace h.local_pp_name ``(eq.to_iff %%h)
         | `(¬ (_ ∧ _))  := replace h.local_pp_name ``(not_and_distrib'.mp %%h) <|>
                            replace h.local_pp_name ``(not_and_distrib.mp %%h)
         | `(¬ (_ ∨ _))  := replace h.local_pp_name ``(not_or_distrib.mp %%h)
         | `(¬ ¬ _)      := replace h.local_pp_name ``(of_not_not %%h)
         | `(¬ (_ → (_ : Prop))) := replace h.local_pp_name ``(not_imp.mp %%h)
         | `(¬ (_ ↔ _)) := replace h.local_pp_name ``(not_iff.mp %%h)
         | `(_ ↔ _) := replace h.local_pp_name ``(iff_iff_and_or_not_and_not.mp %%h) <|>
                       replace h.local_pp_name ``(iff_iff_and_or_not_and_not.mp (%%h).symm) <|>
                       () <$ tactic.cases h
         | `(_ → _)     := replace h.local_pp_name ``(not_or_of_imp %%h)
         | _ := failed
         end

meta def tauto_state := ref $ expr_map (option (expr × expr))

meta def modify_ref {α : Type} (r : ref α) (f : α → α) :=
read_ref r >>= write_ref r ∘ f

meta def add_refl (r : tauto_state) (e : expr) : tactic (expr × expr) :=
do m ← read_ref r,
   p ← mk_mapp `rfl [none,e],
   write_ref r $ m.insert e none,
   return (e,p)

meta def add_symm_proof (r : tauto_state) (e : expr) : tactic (expr × expr) :=
do env ← get_env,
   let rel := e.get_app_fn.const_name,
   some symm ← pure $ environment.symm_for env rel
     | add_refl r e,
   (do e' ← mk_meta_var `(Prop),
       iff_t ← to_expr ``(%%e = %%e'),
       (_,p) ← solve_aux iff_t
         (applyc `iff.to_eq ; () <$ split ; applyc symm),
       e' ← instantiate_mvars e',
       m ← read_ref r,
       write_ref r $ (m.insert e (e',p)).insert e' none,
       return (e',p) )
   <|> add_refl r e

meta def add_edge (r : tauto_state) (x y p : expr) : tactic unit :=
modify_ref r $ λ m, m.insert x (y,p)

meta def root (r : tauto_state) : expr → tactic (expr × expr) | e :=
do m ← read_ref r,
   let record_e : tactic (expr × expr) :=
       match e with
       | v@(expr.mvar _ _ _) :=
         (do (e,p) ← get_assignment v >>= root,
             add_edge r v e p,
             return (e,p)) <|>
         add_refl r e
       | _ := add_refl r e
       end,
   some e' ← pure $ m.find e | record_e,
   match e' with
   | (some (e',p')) :=
     do (e'',p'') ← root e',
        p'' ← mk_app `eq.trans [p',p''],
        add_edge r e e'' p'',
        pure (e'',p'')
   | none := prod.mk e <$> mk_mapp `rfl [none,some e]
   end

meta def symm_eq (r : tauto_state) : expr → expr → tactic expr | a b :=
do m ← read_ref r,
   (a',pa) ← root r a,
   (b',pb) ← root r b,
   (unify a' b' >> add_refl r a' *> mk_mapp `rfl [none,a]) <|>
    do p ← match (a', b') with
           | (`(¬ %%a₀), `(¬ %%b₀)) :=
             do p  ← symm_eq a₀ b₀,
                p' ← mk_app `congr_arg [`(not),p],
                add_edge r a' b' p',
                return p'
           | (`(%%a₀ ∧ %%a₁), `(%%b₀ ∧ %%b₁)) :=
             do p₀ ← symm_eq a₀ b₀,
                p₁ ← symm_eq a₁ b₁,
                p' ← to_expr ``(congr (congr_arg and %%p₀) %%p₁),
                add_edge r a' b' p',
                return p'
           | (`(%%a₀ ∨ %%a₁), `(%%b₀ ∨ %%b₁)) :=
             do p₀ ← symm_eq a₀ b₀,
                p₁ ← symm_eq a₁ b₁,
                p' ← to_expr ``(congr (congr_arg or %%p₀) %%p₁),
                add_edge r a' b' p',
                return p'
           | (`(%%a₀ ↔ %%a₁), `(%%b₀ ↔ %%b₁)) :=
             (do p₀ ← symm_eq a₀ b₀,
                 p₁ ← symm_eq a₁ b₁,
                 p' ← to_expr ``(congr (congr_arg iff %%p₀) %%p₁),
                 add_edge r a' b' p',
                 return p') <|>
             do p₀ ← symm_eq a₀ b₁,
                p₁ ← symm_eq a₁ b₀,
                p' ← to_expr ``(eq.trans (congr (congr_arg iff %%p₀) %%p₁)
                                         (iff.to_eq iff.comm ) ),
                add_edge r a' b' p',
                return p'
           | (`(%%a₀ → %%a₁), `(%%b₀ → %%b₁)) :=
             if ¬ a₁.has_var ∧ ¬ b₁.has_var then
             do p₀ ← symm_eq a₀ b₀,
                p₁ ← symm_eq a₁ b₁,
                p' ← mk_app `congr_arg [`(implies),p₀,p₁],
                add_edge r a' b' p',
                return p'
             else unify a' b' >> add_refl r a' *> mk_mapp `rfl [none,a]
           | (_, _) :=
             (do guard $ a'.get_app_fn.is_constant ∧
                         a'.get_app_fn.const_name = b'.get_app_fn.const_name,
                 (a'',pa') ← add_symm_proof r a',
                 guard $ a'' =ₐ b',
                 pure pa' )
           end,
           p' ← mk_eq_trans pa p,
           add_edge r a' b' p',
           mk_eq_symm pb >>= mk_eq_trans p'

meta def find_eq_type (r : tauto_state) : expr → list expr → tactic (expr × expr)
| e []         := failed
| e (H :: Hs) :=
  do t  ← infer_type H,
     t' ← infer_type e,
     (prod.mk H <$> symm_eq r e t) <|> find_eq_type e Hs

private meta def contra_p_not_p (r : tauto_state) : list expr → list expr → tactic unit
| []         Hs := failed
| (H1 :: Rs) Hs :=
  do t ← (extract_opt_auto_param <$> infer_type H1) >>= whnf,
     (do a   ← match_not t,
         (H2,p)  ← find_eq_type r a Hs,
         H2 ← to_expr ``( (%%p).mpr %%H2 ),
         tgt ← target,
         pr  ← mk_app `absurd [tgt, H2, H1],
         tactic.exact pr)
     <|> contra_p_not_p Rs Hs

meta def contradiction_with (r : tauto_state) : tactic unit :=
contradiction <|>
do tactic.try intro1,
   ctx ← local_context,
   contra_p_not_p r ctx ctx

meta def contradiction_symm :=
using_new_ref (native.rb_map.mk _ _) contradiction_with

meta def assumption_with (r : tauto_state) : tactic unit :=
do { ctx ← local_context,
     t   ← target,
     (H,p) ← find_eq_type r t ctx,
     mk_eq_mpr p H >>= tactic.exact }
<|> fail "assumption tactic failed"

meta def assumption_symm :=
using_new_ref (native.rb_map.mk _ _) assumption_with

meta def tautology (c : bool := ff) : tactic unit :=
do when c classical,
   using_new_ref (expr_map.mk _) $ λ r,
   do try (contradiction_with r);
      try (assumption_with r);
      repeat (do
        gs ← get_goals,
        () <$ tactic.intros;
        distrib_not;
        casesm (some ()) [``(_ ∧ _),``(_ ∨ _),``(Exists _),``(false)];
        try (contradiction_with r);
        try (target >>= match_or >> refine ``( or_iff_not_imp_left.mpr _));
        try (target >>= match_or >> refine ``( or_iff_not_imp_right.mpr _));
        () <$ tactic.intros;
        constructor_matching (some ()) [``(_ ∧ _),``(_ ↔ _),``(true)];
        try (assumption_with r),
        gs' ← get_goals,
        guard (gs ≠ gs') ) ;
      repeat
      (reflexivity <|> solve_by_elim <|>
       constructor_matching none [``(_ ∧ _),``(_ ↔ _),``(Exists _),``(true)] ) ;
      done

end tactic
