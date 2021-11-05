/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import tactic.rcases
/-!
# lift tactic

This file defines the `lift` tactic, allowing the user to lift elements from one type to another
under a specified condition.

## Tags

lift, tactic
-/

/-- A class specifying that you can lift elements from `α` to `β` assuming `cond` is true.
  Used by the tactic `lift`. -/
class can_lift (α β : Sort*) :=
(coe : β → α)
(cond : α → Prop)
(prf : ∀(x : α), cond x → ∃(y : β), coe y = x)


open tactic

/--
A user attribute used internally by the `lift` tactic.
This should not be applied by hand.
-/
@[user_attribute]
meta def can_lift_attr : user_attribute (list name) :=
{ name := "_can_lift",
  descr := "internal attribute used by the lift tactic",
  parser := failed,
  cache_cfg := {
    mk_cache := λ _,
      do { ls ← attribute.get_instances `instance,
          ls.mfilter $ λ l,
          do { (_,t) ← mk_const l >>= infer_type >>= open_pis,
          return $ t.is_app_of `can_lift } },
    dependencies := [`instance] } }

instance : can_lift ℤ ℕ :=
⟨coe, λ n, 0 ≤ n, λ n hn, ⟨n.nat_abs, int.nat_abs_of_nonneg hn⟩⟩

/-- Enable automatic handling of pi types in `can_lift`. -/
instance pi.can_lift (ι : Type*) (α : Π i : ι, Type*) (β : Π i : ι, Type*)
  [Π i : ι, can_lift (α i) (β i)] :
  can_lift (Π i : ι, α i) (Π i : ι, β i) :=
{ coe := λ f i, can_lift.coe (f i),
  cond := λ f, ∀ i, can_lift.cond (β i) (f i),
  prf := λ f hf, ⟨λ i, classical.some (can_lift.prf (f i) (hf i)), funext $ λ i,
    classical.some_spec (can_lift.prf (f i) (hf i))⟩ }

instance pi_subtype.can_lift (ι : Type*) (α : Π i : ι, Type*) [ne : Π i, nonempty (α i)]
  (p : ι → Prop) :
  can_lift (Π i : subtype p, α i) (Π i, α i) :=
{ coe := λ f i, f i,
  cond := λ _, true,
  prf :=
    begin
      classical,
      refine λ f _, ⟨λ i, if hi : p i then f ⟨i, hi⟩ else classical.choice (ne i), funext _⟩,
      rintro ⟨i, hi⟩,
      exact dif_pos hi
    end }

instance pi_subtype.can_lift' (ι : Type*) (α : Type*) [ne : nonempty α] (p : ι → Prop) :
  can_lift (subtype p → α) (ι → α) :=
pi_subtype.can_lift ι (λ _, α) p

namespace tactic

/--
Construct the proof of `cond x` in the lift tactic.
*  `e` is the expression being lifted and `h` is the specified proof of `can_lift.cond e`.
*  `old_tp` and `new_tp` are the arguments to `can_lift` and `inst` is the `can_lift`-instance.
*  `s` and `to_unfold` contain the information of the simp set used to simplify.

If the proof was specified, we check whether it has the correct type.
If it doesn't have the correct type, we display an error message
(but first call dsimp on the expression in the message).

If the proof was not specified, we create assert it as a local constant.
(The name of this local constant doesn't matter, since `lift` will remove it from the context.)
-/
meta def get_lift_prf (h : option pexpr) (old_tp new_tp inst e : expr)
  (s : simp_lemmas) (to_unfold : list name) : tactic expr := do
  expected_prf_ty ← mk_app `can_lift.cond [old_tp, new_tp, inst, e],
  expected_prf_ty ← s.dsimplify to_unfold expected_prf_ty,
  if h_some : h.is_some then
    decorate_error "lift tactic failed." $ i_to_expr ``((%%(option.get h_some) : %%expected_prf_ty))
  else do
    prf_nm ← get_unused_name,
    prf ← assert prf_nm expected_prf_ty,
    swap,
    return prf

/-- Lift the expression `p` to the type `t`, with proof obligation given by `h`.
  The list `n` is used for the two newly generated names, and to specify whether `h` should
  remain in the local context. See the doc string of `tactic.interactive.lift` for more information.
  -/
meta def lift (p : pexpr) (t : pexpr) (h : option pexpr) (n : list name) : tactic unit :=
do
  propositional_goal <|>
    fail "lift tactic failed. Tactic is only applicable when the target is a proposition.",
  e ← i_to_expr p,
  old_tp ← infer_type e,
  new_tp ← i_to_expr ``(%%t : Sort*),
  inst_type ← mk_app ``can_lift [old_tp, new_tp],
  inst ← mk_instance inst_type <|>
    pformat!"Failed to find a lift from {old_tp} to {new_tp}. Provide an instance of\n  {inst_type}"
    >>= fail,
  /- make the simp set to get rid of `can_lift` projections -/
  can_lift_instances ← can_lift_attr.get_cache >>= λ l, l.mmap resolve_name,
  (s, to_unfold) ← mk_simp_set tt [] $ can_lift_instances.map simp_arg_type.expr,
  prf_cond ← get_lift_prf h old_tp new_tp inst e s to_unfold,
  let prf_nm := if prf_cond.is_local_constant then some prf_cond.local_pp_name else none,
  /- We use mk_mapp to apply `can_lift.prf` to all but one argument, and then just use expr.app
  for the last argument. For some reason we get an error when applying mk_mapp it to all
  arguments. -/
  prf_ex0 ← mk_mapp `can_lift.prf [old_tp, new_tp, inst, e],
  let prf_ex := prf_ex0 prf_cond,
  /- Find the name of the new variable -/
  new_nm ← if n ≠ [] then return n.head
    else if e.is_local_constant then return e.local_pp_name
    else get_unused_name,
  /- Find the name of the proof of the equation -/
  eq_nm ← if hn : 1 < n.length then return (n.nth_le 1 hn)
    else if e.is_local_constant then return `rfl
    else get_unused_name `h,
  /- We add the proof of the existential statement to the context and then apply
  `dsimp` to it, unfolding all `can_lift` instances. -/
  temp_nm ← get_unused_name,
  temp_e ← note temp_nm none prf_ex,
  dsimp_hyp temp_e s to_unfold {},
  /- We case on the existential. We use `rcases` because `eq_nm` could be `rfl`. -/
  rcases none (pexpr.of_expr temp_e) $ rcases_patt.tuple ([new_nm, eq_nm].map rcases_patt.one),
  /- If the lifted variable is not a local constant,
    try to rewrite it away using the new equality. -/
  when (¬ e.is_local_constant) (get_local eq_nm >>=
    λ e, interactive.rw ⟨[⟨⟨0, 0⟩, tt, (pexpr.of_expr e)⟩], none⟩ interactive.loc.wildcard),
  /- If the proof `prf_cond` is a local constant, remove it from the context,
    unless `n` specifies to keep it. -/
  if h_prf_nm : prf_nm.is_some ∧ n.nth 2 ≠ prf_nm then
    get_local (option.get h_prf_nm.1) >>= clear else skip

setup_tactic_parser

/-- Parses an optional token "using" followed by a trailing `pexpr`. -/
meta def using_texpr := (tk "using" *> texpr)?

/-- Parses a token "to" followed by a trailing `pexpr`. -/
meta def to_texpr := (tk "to" *> texpr)

namespace interactive

/--
Lift an expression to another type.
* Usage: `'lift' expr 'to' expr ('using' expr)? ('with' id (id id?)?)?`.
* If `n : ℤ` and `hn : n ≥ 0` then the tactic `lift n to ℕ using hn` creates a new
  constant of type `ℕ`, also named `n` and replaces all occurrences of the old variable `(n : ℤ)`
  with `↑n` (where `n` in the new variable). It will remove `n` and `hn` from the context.
  + So for example the tactic `lift n to ℕ using hn` transforms the goal
    `n : ℤ, hn : n ≥ 0, h : P n ⊢ n = 3` to `n : ℕ, h : P ↑n ⊢ ↑n = 3`
    (here `P` is some term of type `ℤ → Prop`).
* The argument `using hn` is optional, the tactic `lift n to ℕ` does the same, but also creates a
  new subgoal that `n ≥ 0` (where `n` is the old variable).
  + So for example the tactic `lift n to ℕ` transforms the goal
    `n : ℤ, h : P n ⊢ n = 3` to two goals
    `n : ℕ, h : P ↑n ⊢ ↑n = 3` and `n : ℤ, h : P n ⊢ n ≥ 0`.
* You can also use `lift n to ℕ using e` where `e` is any expression of type `n ≥ 0`.
* Use `lift n to ℕ with k` to specify the name of the new variable.
* Use `lift n to ℕ with k hk` to also specify the name of the equality `↑k = n`. In this case, `n`
  will remain in the context. You can use `rfl` for the name of `hk` to substitute `n` away
  (i.e. the default behavior).
* You can also use `lift e to ℕ with k hk` where `e` is any expression of type `ℤ`.
  In this case, the `hk` will always stay in the context, but it will be used to rewrite `e` in
  all hypotheses and the target.
  + So for example the tactic `lift n + 3 to ℕ using hn with k hk` transforms the goal
    `n : ℤ, hn : n + 3 ≥ 0, h : P (n + 3) ⊢ n + 3 = 2 * n` to the goal
    `n : ℤ, k : ℕ, hk : ↑k = n + 3, h : P ↑k ⊢ ↑k = 2 * n`.
* The tactic `lift n to ℕ using h` will remove `h` from the context. If you want to keep it,
  specify it again as the third argument to `with`, like this: `lift n to ℕ using h with n rfl h`.
* More generally, this can lift an expression from `α` to `β` assuming that there is an instance
  of `can_lift α β`. In this case the proof obligation is specified by `can_lift.cond`.
* Given an instance `can_lift β γ`, it can also lift `α → β` to `α → γ`; more generally, given
  `β : Π a : α, Type*`, `γ : Π a : α, Type*`, and `[Π a : α, can_lift (β a) (γ a)]`, it
  automatically generates an instance `can_lift (Π a, β a) (Π a, γ a)`.

`lift` is in some sense dual to the `zify` tactic. `lift (z : ℤ) to ℕ` will change the type of an
integer `z` (in the supertype) to `ℕ` (the subtype), given a proof that `z ≥ 0`;
propositions concerning `z` will still be over `ℤ`. `zify` changes propositions about `ℕ` (the
subtype) to propositions about `ℤ` (the supertype), without changing the type of any variable.
-/
meta def lift (p : parse texpr) (t : parse to_texpr) (h : parse using_texpr)
  (n : parse with_ident_list) : tactic unit :=
tactic.lift p t h n

add_tactic_doc
{ name       := "lift",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.lift],
  tags       := ["coercions"] }

end interactive
end tactic
