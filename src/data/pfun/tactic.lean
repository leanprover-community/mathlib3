import data.pfun.fix

variables {α : Type*} {β : Type*} {γ : Type*} {φ : Type*}

namespace complete_partial_order

open function has_fix complete_partial_order

section continuity_attr

open tactic native

@[user_attribute]
meta def continuity_attr : user_attribute (rb_map name $ list name) :=
{ name := `continuity,
  descr := "proof rule for continuity in the sense of complete partial orders",
  cache_cfg := { mk_cache := λ (ls : list name),
                             do { let m := rb_map.mk name (list name),
                                  ls.mfoldl (λ m n,
                                  do { (_,t) ← mk_const n >>= infer_type >>= mk_local_pis,
                                       `(continuous' %%f) ← pure t <|> fail format!"{t}",
                                       let l := f.binding_body,
                                       pure $ m.insert_cons l.get_app_fn.const_name n }) m
                                   },
                 dependencies := [] } }

end continuity_attr

section mono

variables  [preorder α]

lemma const_mono [preorder β] (f : β) : monotone (λ _ : α, f) :=
assume x y h, le_refl _

lemma ite_mono [preorder β] {f g : α → β}
  {p : Prop} {h : decidable p}
  (hf : monotone f) (hg : monotone g) :
  monotone (λ x, @ite _ h _ (f x) (g x)) :=
by intros x y h; dsimp; split_ifs; [apply hf h, apply hg h]

lemma bind_mono {β γ} (f : α → roption β)
                (g : α → β → roption γ)
  (hf : monotone f) (hg : monotone g) :
  monotone (λ x, f x >>= g x)  :=
begin
  intros x y h a, simp, intros b hb ha,
  refine ⟨b,hf h _ hb,hg h _ _ ha⟩,
end

end mono

section continuity

variables [complete_partial_order α] [complete_partial_order β] [complete_partial_order γ]
local attribute [instance] roption.complete_partial_order

lemma cont_const [complete_partial_order β] (f : β) (c : chain α) :
  Sup (c.map (λ _, f) (const_mono _)) = f :=
begin
  apply le_antisymm,
  { apply Sup_le, simp [chain.mem_map_iff],
    intros, subst f },
  { apply le_Sup, simp [chain.mem_map_iff], exact ⟨ c.elems 0,0,rfl ⟩ }
end

lemma cont_ite [complete_partial_order β] {p : Prop} {hp : decidable p} (c : chain α) (f g : α → β) (hf hg) :
  Sup (c.map (λ x, @ite p hp _ (f x) (g x)) (ite_mono hf hg)) = @ite p hp _ (Sup $ c.map f hf) (Sup $ c.map g hg) :=
by split_ifs; refl

lemma cont_bind {β γ} (c : chain α) (f : α → roption β) (g : α → β → roption γ) (h' h'') :
  Sup (c.map (λ x, f x >>= g x : α → roption γ) (bind_mono _ g h' h'')) = Sup (c.map (λ x, f x) h') >>= Sup (c.map (λ x, g x) h'') :=
begin
  apply eq_of_forall_ge_iff, intro x,
  simp [Sup_le_iff,roption.bind_le,-roption.bind_eq_bind,chain.mem_map_iff],
  split; intro h''',
  { intros b hb, apply Sup_le _ _ _,
    simp [-roption.bind_eq_bind,chain.mem_map_iff],
    intros y a z hz ha hy, subst a, subst y,
    { intros y hy, simp [roption.mem_Sup] at hb,
      replace h₀ := chain.exists_of_mem_map _ _ hb,
      rcases h₀ with ⟨k,h₂,h₃⟩,
      rw roption.eq_some_iff at h₃,
      cases chain.le_total_of_mem_of_mem _ hz h₂ with hh hh,
      { replace h''' := h''' _ k h₂ rfl,
        apply h''', simp, refine ⟨_,h₃,_⟩,
        apply h'' hh _ _ hy },
      { replace h''' := h''' _ z hz rfl,
        apply h''', simp, refine ⟨_,_,hy⟩,
        apply h' hh _ h₃ } } },
  { intros y a ha hy, subst hy, intros b hb, simp at hb,
    rcases hb with ⟨b',hb₀,hb₁⟩,
    apply h''' b' _ b _, revert hb₀,
    apply le_Sup _ (f a) _, apply chain.mem_map _ _ _ ha,
    apply le_Sup _ (g a b') _, exact hb₁,
    apply chain.mem_map _ _ _ ha, introv _ h, apply h'' h, },
end

@[continuity]
lemma cont_const' (f : β) :
  continuous' (λ x : α, f) :=
by { split, intro c; rw cont_const }

lemma cont_id' :
  continuous' (λ x : α, x) :=
by { split, intro c, erw chain.map_id }

@[continuity]
lemma cont_ite' {p : Prop} {hp : decidable p} (f g : α → β)
  (hf : continuous' f) (hg : continuous' g) :
  continuous' (λ x, @ite p hp _ (f x) (g x)) :=
by { split, intro c, rw [cont_ite,← hg.snd,← hf.snd] }

@[continuity]
lemma cont_bind' {β γ} (f : α → roption β) (g : α → β → roption γ)
  (hf : continuous' f)
  (hg : continuous' g) :
  continuous' (λ x, f x >>= g x) :=
by { split, intro c, rw [cont_bind,← hg.snd,← hf.snd] }


@[continuity]
lemma cont_map' {β γ : Type*} (f : β → γ) (g : α → roption β)
  (hg : continuous' g) :
  continuous' (λ x, f <$> g x) :=
begin
  simp [-roption.bind_eq_bind,-roption.map_eq_map,(bind_pure_comp_eq_map _ _ _).symm],
  apply cont_bind' _ _ hg, apply cont_const'
end

@[continuity]
lemma cont_seq' {β γ : Type*} (f : α → roption (β → γ)) (g : α → roption β)
  (hf : continuous' f)
  (hg : continuous' g) :
  continuous' (λ x, f x <*> g x) :=
begin
  simp [-roption.bind_eq_bind,seq_eq_bind_map], apply cont_bind' _ _ hf,
  apply pi.continuous_ext, intro x, apply cont_map' _ _ hg,
end

end continuity

end complete_partial_order

namespace tactic

open tactic expr
open function has_fix complete_partial_order

meta def continuity_ext : tactic (list expr) :=
do `(continuous' %%f) ← target,
   (args,_) ← infer_type f >>= mk_local_pis,
   let arity := args.length - 1,
   iterate_exactly' arity $
     applyc ``pi.continuous_ext >> intro1

meta def continuity_step' : tactic unit :=
do continuity_ext,
   e@`(continuous' %%f) ← target,
   (lam n bi d b) ← pure f,
   m ← continuity_attr.get_cache,
   match b.get_app_fn with
   | (const n _) :=
     do ls ← m.find n <|> pure [``cont_const'],
        ls.any_of applyc
   | v@(var _) :=
     do let args := b.get_app_args,
        vs ← args.mmap $ infer_type >=> mk_local_def `v,
        let f' := lam n bi d $ v.mk_app vs,
        let e' := (e.app_fn f').pis vs,
        g ← mk_meta_var e',
        exact $ g.mk_app args,
        gs ← get_goals,
        set_goals $ g :: gs,
        vs ← intron' args.length,
        vs.reverse.mmap' $ λ v, refine ``(pi.continuous_congr _ %%v _),
        refine ``(cont_id')
   | t := do
     f ← pp f,
     fail format!"unsupported {f}"
   end

meta def interactive.show_continuity' : tactic unit :=
focus1 $
do `(continuous' %%f) ← target,
   vs ← continuity_ext,
   dunfold_target [f.get_app_fn.const_name] <|>
     (() <$ cases vs.head; dunfold_target [f.get_app_fn.const_name]),
   all_goals $ repeat continuity_step',
   skip

open interactive expr

meta def mk_cpo_instance : expr → tactic expr
| (pi n bi d b) :=
do v ← mk_local' n bi d,
   let b' := lam n bi d b,
   inst ← mk_cpo_instance (b.instantiate_var v) >>= lambdas [v],
   mk_mapp ``pi.complete_partial_order [d,b',inst]
| `(roption %%α) := mk_mapp ``roption.complete_partial_order [α]
| _ := fail "mk_cpo_instance"

meta def functional_type_aux : expr → expr → list expr → tactic (list expr × expr)
| e (pi n bi d b) vs :=
  if d =ₐ b
    then return (vs.reverse, e)
    else do v ← mk_local' n bi d,
            e' ← head_beta $ e v,
            functional_type_aux e' (b.instantiate_var v) (v :: vs)
| e _ _ := failed

meta def get_functional (n : name) : tactic (list expr × expr) :=
do d ← get_decl n,
   let ls := d.univ_params,
   let t  := d.type,
   let c : expr := const n $ ls.map level.param,
   functional_type_aux c t []

meta def mk_continuous_stmt (e : expr) (vs : list expr) : tactic expr :=
do t ← infer_type e,
   let t' := t.binding_domain,
   inst ← mk_cpo_instance t',
   mk_mapp ``continuous' [t',t',inst,inst,e] >>= pis vs

meta def mk_rec_eqns (n p cont_n : name) (vs : list expr) : tactic unit :=
do { ls ← get_eqn_lemmas_for ff n,
     ls.mmap' $ λ l : name,
     do let l' := l.replace_prefix n p,
        d ← get_decl l,
        t ← instantiate_mvars d.type,
        (ps,e) ← mk_local_pis t,
        let arity := vs.length,
        let ps₀ := ps.take arity,
        let ps₁ := ps.drop arity,
        let ls := d.univ_params,
        let fn := (expr.const n $ ls.map level.param : expr).mk_app ps₀ ps₁.head,
        let defn := (expr.const p $ ls.map level.param : expr).mk_app ps₀,
        e ← kabstract e fn >>= flip kabstract ps₁.head,
        let ps := ps₀ ++ ps₁.tail,
        eqn ← pis ps $ e.instantiate_var defn,
        pr ← run_async $ do
          { pr ← mk_meta_var eqn,
            set_goals [pr],
            ps ← intron' ps.length,
            let ps₀ := ps.take arity,
            let ps₁ := ps.drop arity,
            let cont_l := (expr.const cont_n $ ls.map level.param : expr).mk_app ps₀,
            dunfold_target [p],
            (l,r) ← target >>= match_eq,
            fix_eq ← mk_mapp ``lawful_fix.fix_eq [none, none, none, none, none, cont_l],
            (_,p,_) ← rewrite fix_eq l, exact p,
            done,
            pr ← instantiate_mvars pr,
            pure pr },
        add_decl $ declaration.thm l' ls eqn pr }

@[user_attribute]
meta def recursive_decl_attr : user_attribute :=
{ name := `recursive_decl,
  descr := "Create a recursive declaration from a functional",
  after_set := some $ λ n _ b,
    do d ← get_decl n,
       let ls := d.univ_params,
       let p := n.get_prefix,
       let cont_n := p <.> "cont",
       (vs, fn) ← get_functional n,
       do { cont_t ← mk_continuous_stmt fn vs,
            pr ← run_async $ do
              { pr ← mk_meta_var cont_t,
                set_goals [pr],
                intron vs.length,
                interactive.show_continuity',
                pr ← instantiate_mvars pr,
                pure pr },
            add_decl $ declaration.thm cont_n ls cont_t pr },
       do { df ← mk_app ``has_fix.fix [fn] >>= lambdas vs,
            t  ← infer_type df,
            add_decl $ mk_definition p ls t df },
       mk_rec_eqns n p cont_n vs,
       skip
  }

end tactic
