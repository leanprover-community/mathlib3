import tactic
import data.real.basic
import algebra.order.field
import algebra.order.ring
-- import algebra.linear_recurrence
import data.nat.basic
import order.lattice
import algebra.algebra.basic

universe u

#check algebra_rat
#check algebra.id
-- variables (R : Type*) [linear_order R]

-- lemma a :
--   @lattice.to_semilattice_inf _ (@lattice_of_linear_order (with_top R) with_top.linear_order) =
--   @semilattice_inf_top.to_semilattice_inf (with_top R) with_top.semilattice_inf :=
-- rfl
-- local attribute [-instance] semilattice_inf_top.to_semilattice_inf
-- local attribute [-instance] with_top.lattice
-- lemma b :
--   @semilattice_inf_top.to_semilattice_inf (with_top R) with_top.semilattice_inf =
--   @lattice.to_semilattice_inf _ (@lattice_of_linear_order (with_top R) with_top.linear_order) =
--   (by apply_instance) := by refl

set_option pp.all true
lemma ok :
  nat.decidable_eq = @decidable_eq_of_decidable_le ℕ (by apply_instance) (by apply_instance) :=
begin
  refl,
  -- ext a b,
  -- dsimp,
  -- delta nat.decidable_eq,
  -- delta decidable_eq_of_decidable_le,
  -- dsimp,
  -- congr,
end

open tactic
meta
def anno : macro_def := match (``(@nat)) with
| (expr.macro m l) := m
| _ := anno
end

meta def tt : tactic unit := (do
-- let tgt_name : name := ``decidable_eq,

-- insts ← attribute.get_instances `instance,
--   insts_tys ← insts.mmap $ λ i, (λ n, (n, i)) <$> expr.pi_codomain <$> declaration.type <$> get_decl i,
-- let target_insts := insts_tys.filter (λ i, i.1.app_fn.const_name = tgt_name),
--   trace target_insts,
-- let inhabited_tys := inhabited_insts.map (λ i, i.app_arg.get_app_fn.const_name),
      -- do { ls ← attribute.get_instances `instance,
      --     ls.mfilter $ λ l,
      --     do { (_,t) ← mk_const l >>= infer_type >>= open_pis,
      --     return $ t.is_app_of `can_lift } },
  -- u ← mk_meta_univ,
  -- let u := expr.mvar `u `u (`(Type) : expr),
  let nae := ``nat.decidable_eq,
  let naf := ``decidable_eq_of_decidable_le,
  let nae := ``real.has_neg,
  let naf := ``sub_neg_monoid.to_has_neg,
  let nae := ``algebra_rat,
  let naf := ``algebra.id,
  let ne := expr.macro anno [(expr.const nae [] : expr ff)],
  -- ``(@nat.decidable_eq),
  -- let nf := ``(@decidable_eq_of_subsingleton),
  let nf := --``(@decidable_eq_of_decidable_le),
    expr.macro anno [(expr.const naf [] : expr ff)],
  nue ← expr.pi_arity <$> declaration.type <$> get_decl nae,
  lse ← mk_mvar_list nue,
  trace lse,
  nuf ← expr.pi_arity <$> declaration.type <$> get_decl nf.erase_annotations.const_name,
  lsf ← mk_mvar_list nuf,
  trace lsf,
  -- let nf := ``(@decidable_eq_of_decidable_le),
  -- e ← to_expr (``(nat.decidable_eq) : expr ff),
  -- t ← mk_app `decidable_eq_of_decidable_le [l,ll,lll],
  let ee := lse.foldl (λ o l, ``(%%o %%l)) ne,
  let fe := lsf.foldl (λ o l, ``(%%o %%l)) nf,
  e ← to_expr ee,
  trace e,
  f ← to_expr fe,
  trace f,
--   m ← mk_mapp `decidable_eq_of_decidable_le [u,
--  expr.mvar `v `v (partial_order %%u) : expr),none],
  -- trace m,
  t1 ← infer_type e,
  t2 ← infer_type f,
  unify t1 t2,-- transparency.semireducible tt,
  trace t1,
  trace e,
  trace f,
  -- has to be this order
  lse.mmap (λ l, try $ do
    o ← (infer_type l >>= mk_instance),
    unify o l),-- transparency.semireducible tt,
  lsf.mmap (λ l, try $ do
    o ← (infer_type l >>= mk_instance),
    unify o l),-- transparency.semireducible tt,
  -- o ← (infer_type ls.tail.tail.head >>= mk_instance),
  -- unify o ls.tail.tail.head,-- transparency.semireducible tt,
  trace e,
  trace f,
  e ← instantiate_mvars e,
  f ← instantiate_mvars f,
  is_def_eq e f,
  -- unify (`(nat.decidable_eq) : expr) f transparency.semireducible tt,
  -- mk_instance,


  trace "hi",
  skip
)

meta def find_diamonds (nae naf : name) : tactic unit :=
do
  trace (nae, naf),
  lock_tactic_state (do
  let ne := expr.macro anno [(expr.const nae [] : expr ff)],
  -- ``(@nat.decidable_eq),
  -- let nf := ``(@decidable_eq_of_subsingleton),
  let nf := --``(@decidable_eq_of_decidable_le),
    expr.macro anno [(expr.const naf [] : expr ff)],
  nue ← expr.pi_arity <$> declaration.type <$> get_decl nae,
  lse ← mk_mvar_list nue,
  nuf ← expr.pi_arity <$> declaration.type <$> get_decl naf,
  lsf ← mk_mvar_list nuf,
  -- let nf := ``(@decidable_eq_of_decidable_le),
  -- e ← to_expr (``(nat.decidable_eq) : expr ff),
  -- t ← mk_app `decidable_eq_of_decidable_le [l,ll,lll],
  let ee := lse.foldl (λ o l, ``(%%o %%l)) ne,
  let fe := lsf.foldl (λ o l, ``(%%o %%l)) nf,
  e ← to_expr ee,
  f ← to_expr fe,
--   m ← mk_mapp `decidable_eq_of_decidable_le [u,
--  expr.mvar `v `v (partial_order %%u) : expr),none],
  -- trace m,
  t1 ← infer_type e,
  t2 ← infer_type f,
  l ← succeeds $ unify t1 t2,
  if ¬ l then return () else do
  -- has to be this order
  lse.mmap (λ l, try $ do
    o ← (infer_type l >>= mk_instance),
    unify o l),-- transparency.semireducible tt,

  lsf.mmap (λ l, try $ do
    o ← (infer_type l >>= mk_instance),
    unify o l),-- transparency.semireducible tt,
  -- o ← (infer_type ls.tail.tail.head >>= mk_instance),
  -- unify o ls.tail.tail.head,-- transparency.semireducible tt,
  e ← instantiate_mvars e,
  f ← instantiate_mvars f,
  trace e,
  trace f,
  -- assign_local_to_unassigned_mvar,
  -- has_unassigned_mvars,
  gs ← get_goals,
  trace $ (lse ++ lsf).mfilter (λ g, bnot <$> is_assigned g),
  -- ff ← is_assigned mv | pure none,
  is_def_eq e f,-- transparency.semireducible tt,
  -- unify (`(nat.decidable_eq) : expr) f transparency.semireducible tt,
  -- mk_instance,


  skip)
run_cmd find_diamonds ``algebra_rat ``algebra.id
run_cmd tt
#check prod.algebra
#check algebra_nat


meta def find_library_diamonds : tactic unit :=
do
  -- let library_classes : list name := [``decidable_eq],
  library_classes ← attribute.get_instances `class,
  (library_classes.take 1).mmap' (λ tgt_name, do
    insts ← attribute.get_instances `instance,
    insts_tys ← insts.mmap $ λ i, (λ n, (n, i)) <$> expr.pi_codomain <$> declaration.type <$> get_decl i,
    let target_insts := insts_tys.filter (λ i, i.1.get_app_fn.const_name = tgt_name),
    trace tgt_name,
    -- trace target_insts,
    target_insts.mmap'_diag (λ n m, do
      if n ≠ m then (trace_error "fail" --capture
        (find_diamonds n.snd m.snd) >> skip) <|> skip
      else skip)

    -- TODO get library instances together more efficiently

    -- TODO efficiently decompose into equivalence classes
  ),
  skip
  -- let nae := ``nat.decidable_eq,
  -- let naf := ``decidable_eq_of_decidable_le,
  -- let nae := ``real.has_neg,
  -- let naf := ``sub_neg_monoid.to_has_neg,
  -- let nae := ``algebra_rat,
  -- let naf := ``algebra.id,
  -- find_diamonds nae naf


run_cmd find_library_diamonds

#print ok
lemma ok2 :
@sub_neg_monoid.to_has_neg ℝ (
@add_group.to_sub_neg_monoid ℝ (
@add_comm_group.to_add_group ℝ (
(@ordered_add_comm_group.to_add_comm_group ℝ (
@ordered_ring.to_ordered_add_comm_group ℝ (--to_add_group.to_sub_neg_monoid.to_has_neg
@linear_ordered_ring.to_ordered_ring ℝ
real.linear_ordered_ring))))))
= real.has_neg
:= by refl

local attribute [-instance] nat.decidable_eq
local attribute [-instance] nat.linear_order
local attribute [-instance] nat.canonically_linear_ordered_add_monoid
local attribute [-instance] nat.linear_ordered_comm_monoid_with_zero
-- local attribute [-instance] nat.linear_ordered_semiring
-- local attribute [-instance] linear_ordered_cancel_add_comm_monoid.to_linear_ordered_add_comm_monoid
local attribute [-instance] nat.linear_ordered_cancel_add_comm_monoid
local attribute [-instance] linear_ordered_add_comm_monoid.to_linear_order
local attribute [-instance] linear_ordered_comm_monoid.to_linear_order
example :
  nat.decidable_eq = @decidable_eq_of_decidable_le ℕ (by apply_instance) (by apply_instance) :=
by refl --fails

-- how to make this a linter?

open tactic
