/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Generation function for iff rules for inductives, like for `list.chain`:

    ∀{α : Type*} (R : α → α → Prop) (a : α) (l : list α),
      chain R a l ↔ l = [] ∨ ∃{b : α} {l' : list α}, R a b ∧ chain R b l ∧ l = b :: l'

-/

namespace tactic

open tactic expr

meta def mk_iff (e₀ : expr) (e₁ : expr) : expr := `(%%e₀ ↔ %%e₁)

meta def select : ℕ → ℕ → tactic unit
| 0 0             := skip
| 0 (n + 1)       := left >> skip
| (m + 1) (n + 1) := right >> select m n
| (n + 1) 0       := failure

/-- `compact_relation bs as_ps`: Produce a relation of the form:
  R as := ∃ bs, Λ_i a_i = p_i[bs]
This relation is user visible, so we compact it by removing each `b_j` where a `p_i = b_j`, and
hence `a_i = b_j`. We need to take care when there are `p_i` and `p_j` with `p_i = p_j = b_k`.

TODO: this is copied from Lean's `coinductive_predicates.lean`, export it there.
 -/
private meta def compact_relation :
  list expr → list (expr × expr) → list (option expr) × list (expr × expr)
| []        ps := ([], ps)
| (b :: bs) ps :=
  match ps.span (λap:expr × expr, ¬ ap.2 =ₐ b) with
    | (_, [])           := let (bs, ps) := compact_relation bs ps in (b::bs, ps)
    | (ps₁, list.cons (a, _) ps₂) :=
      let
        i := a.instantiate_local b.local_uniq_name,
        (bs, ps) := compact_relation (bs.map i) ((ps₁ ++ ps₂).map (λ⟨a, p⟩, (a, i p)))
      in (none :: bs, ps)
  end

meta def constr_to_prop (univs : list level) (g : list expr) (idxs : list expr) (c : name) :
  tactic ((list (option expr) × (expr ⊕ ℕ)) × expr) := do
  e ← get_env,
  decl ← get_decl c,
  some type' ← return $ decl.instantiate_type_univ_params univs,
  type ← drop_pis g type',
  (args, res) ← mk_local_pis type,
  let idxs_inst := res.get_app_args.drop g.length,
  let (bs, eqs) := compact_relation args (idxs.zip idxs_inst),
  let bs' := bs.filter_map id,
  eqs ← eqs.mmap (λ⟨idx, inst⟩, do
    let ty := idx.local_type,
    inst_ty ← infer_type inst,
    sort u ← infer_type ty,
    (is_def_eq ty inst_ty >> return ((const `eq [u] : expr) ty idx inst)) <|>
      return ((const `heq [u] : expr) ty idx inst_ty inst)),
  (n, r) ← match bs', eqs with
  | [], [] := return (sum.inr 0, mk_true)
  | _, []  := do
    let t : expr := bs'.ilast.local_type,
    sort l ← infer_type t,
    if l = level.zero then do
      r ← mk_exists_lst bs'.init t,
      return (sum.inl bs'.ilast, r)
    else do
      r ← mk_exists_lst bs' mk_true,
      return (sum.inr 0, r)
  | _, _ := do
    r ← mk_exists_lst bs' (mk_and_lst eqs),
    return (sum.inr eqs.length, r)
  end,
  return ((bs, n), r)

private meta def to_cases (s : list $ list (option expr) × (expr ⊕ ℕ)) : tactic unit := do
  h ← intro1,
  i ← induction h,
  focus ((s.zip i).enum.map $ λ⟨p, (shape, t), _, vars, _⟩, do
    let si := (shape.zip vars).filter_map (λ⟨c, v⟩, c >>= λ _, some v),
    select p (s.length - 1),
    match t with
    | sum.inl e := do
      si.init.mmap' existsi,
      some v ← return $ vars.nth (shape.length - 1),
      exact v
    | sum.inr n := do
      si.mmap' existsi,
      iterate_exactly (n - 1) (split >> constructor >> skip) >> constructor >> skip
    end,
    done),
  done

private def list_option_merge {α : Type*} {β : Type*} : list (option α) → list β → list (option β)
| [] _ := []
| (none :: xs) ys := none :: list_option_merge xs ys
| (some a :: xs) (y :: ys) := some y :: list_option_merge xs ys
| (some a :: xs) [] := []

private meta def to_inductive
  (cs : list name) (gs : list expr) (s : list (list (option expr) × (expr ⊕ ℕ))) (h : expr) :
  tactic unit :=
match s.length with
| 0       := induction h >> skip
| (n + 1) := do
  r ← elim_gen_sum n h,
  focus ((cs.zip (r.zip s)).map $ λ⟨constr_name, h, bs, e⟩, do
    let n := (bs.filter_map id).length,
    match e with
    | sum.inl e := elim_gen_prod (n - 1) h [] >> skip
    | sum.inr 0 := do
      (hs, h) ← elim_gen_prod n h [],
      clear h
    | sum.inr (e + 1) := do
      (hs, h) ← elim_gen_prod n h [],
      (es, eq) ← elim_gen_prod e h [],
      let es := es ++ [eq],
      /- `es.mmap' subst`: fails when we have dependent equalities (heq). `subst will change the
        dependent hypotheses, so that the uniq local names in `es` are wrong afterwards. Instead
        we revert them and pull them out one by one -/
      revert_lst es,
      es.mmap' (λ_, intro1 >>= subst)
    end,
    ctxt ← local_context,
    let gs := ctxt.take gs.length,
    let hs := (ctxt.reverse.take n).reverse,
    let m := gs.map some ++ list_option_merge bs hs,
    args ← m.mmap (λa, match a with some v := return v | none := mk_mvar end),
    c ← mk_const constr_name,
    exact (c.mk_app args),
    done),
  done
end

/-- `mk_iff_of_inductive_prop i r` makes a iff rule for the inductively defined proposition `i`.
  The new rule `r` has the shape `∀ps is, i as ↔ ⋁_j, ∃cs, is = cs`, where `ps` are the type
  parameters, `is` are the indices, `j` ranges over all possible constructors, the `cs` are the
  parameters for each constructors, the equalities `is = cs` are the instantiations for each
  constructor for each of the indices to the inductive type `i`.

  In each case, we remove constructor parameters (i.e. `cs`) when the corresponding equality would
  be just `c = i` for some index `i`.

  For example: `mk_iff_of_inductive_prop` on `list.chain` produces:

    ∀{α : Type*} (R : α → α → Prop) (a : α) (l : list α),
      chain R a l ↔ l = [] ∨ ∃{b : α} {l' : list α}, R a b ∧ chain R b l ∧ l = b :: l'

-/
meta def mk_iff_of_inductive_prop (i : name) (r : name) : tactic unit := do
  e ← get_env,
  guard (e.is_inductive i),
  let constrs := e.constructors_of i,
  let params := e.inductive_num_params i,
  let indices := e.inductive_num_indices i,
  let rec := match e.recursor_of i with some rec := rec | none := i.append `rec end,
  decl ← get_decl i,
  let type := decl.type,

  let univ_names := decl.univ_params,
  let univs := univ_names.map level.param,
    /- we use these names for our universe parameters, maybe we should construct a copy of them using uniq_name -/

  (g, `(Prop)) ← mk_local_pis type | fail "Inductive type is not a proposition",
  let lhs := (const i univs).mk_app g,
  shape_rhss ← constrs.mmap (constr_to_prop univs (g.take params) (g.drop params)),
  let shape := shape_rhss.map prod.fst,
  let rhss := shape_rhss.map prod.snd,
  add_theorem_by r univ_names ((mk_iff lhs (mk_or_lst rhss)).pis g) (do
    gs ← intro_lst (g.map local_pp_name),
    split,
    focus [to_cases shape, intro1 >>= to_inductive constrs (gs.take params) shape]),
  skip

end tactic
