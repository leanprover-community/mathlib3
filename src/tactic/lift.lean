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
class can_lift (α β : Sort*) (coe : out_param $ β → α) (cond : out_param $ α → Prop) :=
(prf : ∀(x : α), cond x → ∃(y : β), coe y = x)

instance : can_lift ℤ ℕ coe ((≤) 0) :=
⟨λ n hn, ⟨n.nat_abs, int.nat_abs_of_nonneg hn⟩⟩

/-- Enable automatic handling of pi types in `can_lift`. -/
instance pi.can_lift (ι : Sort*) (α β : ι → Sort*)
  (coe : Π i, β i → α i) (P : Π i, α i → Prop)
  [Π i : ι, can_lift (α i) (β i) (coe i) (P i)] :
  can_lift (Π i : ι, α i) (Π i : ι, β i) (λ f i, coe i (f i)) (λ f, ∀ i, P i (f i)) :=
{ prf := λ f hf, ⟨λ i, classical.some (can_lift.prf (f i) (hf i)), funext $ λ i,
    classical.some_spec (can_lift.prf (f i) (hf i))⟩ }

lemma subtype.exists_pi_extension {ι : Sort*} {α : ι → Sort*} [ne : Π i, nonempty (α i)]
  {p : ι → Prop} (f : Π i : subtype p, α i) :
  ∃ g : Π i : ι, α i, (λ i : subtype p, g i) = f :=
begin
  tactic.classical,
  refine ⟨λ i, if hi : p i then f ⟨i, hi⟩ else classical.choice (ne i), funext _⟩,
  rintro ⟨i, hi⟩,
  exact dif_pos hi
end

instance pi_subtype.can_lift (ι : Sort*) (α : ι → Sort*) [ne : Π i, nonempty (α i)]
  (p : ι → Prop) :
  can_lift (Π i : subtype p, α i) (Π i, α i) (λ f i, f i) (λ _, true) :=
{ prf := λ f _, subtype.exists_pi_extension f }

instance pi_subtype.can_lift' (ι : Sort*) (α : Sort*) [ne : nonempty α] (p : ι → Prop) :
  can_lift (subtype p → α) (ι → α) (λ f i, f i) (λ _, true) :=
pi_subtype.can_lift ι (λ _, α) p

instance subtype.can_lift {α : Sort*} (p : α → Prop) : can_lift α {x // p x} coe p :=
{ prf := λ a ha, ⟨⟨a, ha⟩, rfl⟩ }

open tactic

namespace tactic

/--
Construct the proof of `cond x` in the lift tactic.
*  `e` is the expression being lifted and `h` is the specified proof of `can_lift.cond e`.
*  `old_tp` and `new_tp` are the arguments to `can_lift` and `inst` is the `can_lift`-instance.
*  `s` and `to_unfold` contain the information of the simp set used to simplify.

If the proof was specified, we check whether it has the correct type.
If it doesn't have the correct type, we display an error message.

If the proof was not specified, we create assert it as a local constant.
(The name of this local constant doesn't matter, since `lift` will remove it from the context.)
-/
meta def get_lift_prf (h : option pexpr) (e P : expr) : tactic (expr × bool) := do
  let expected_prf_ty := P.app e,
  expected_prf_ty ← simp_lemmas.mk.dsimplify [] expected_prf_ty {fail_if_unchanged := ff},
  match h with
  | some h := do
      e ← decorate_error "lift tactic failed." (i_to_expr ``((%%h : %%expected_prf_ty))),
      return (e, tt)
  | none   := do
      prf_nm ← get_unused_name,
      prf ← assert prf_nm expected_prf_ty,
      swap,
      return (prf, ff)
  end

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
  coe ← i_to_expr (``(%%new_tp → %%old_tp)) >>= mk_meta_var,
  P ← i_to_expr (``(%%old_tp → Prop)) >>= mk_meta_var,
  inst_type ← mk_app ``can_lift [old_tp, new_tp, coe, P],
  inst ← mk_instance inst_type <|>
    pformat!"Failed to find a lift from {old_tp} to {new_tp}. Provide an instance of\n  {inst_type}"
    >>= fail,
  inst ← instantiate_mvars inst,
  coe ← instantiate_mvars coe,
  P ← instantiate_mvars P,
  (prf_cond, b) ← get_lift_prf h e P,
  let prf_nm := if prf_cond.is_local_constant then some prf_cond.local_pp_name else none,
  /- We use mk_mapp to apply `can_lift.prf` to all but one argument, and then just use expr.app
  for the last argument. For some reason we get an error when applying mk_mapp it to all
  arguments. -/
  prf_ex0 ← mk_mapp `can_lift.prf [old_tp, new_tp, coe, P, inst, e],
  let prf_ex := prf_ex0 prf_cond,
  /- Find the name of the new variable -/
  new_nm ← if n ≠ [] then return n.head
    else if e.is_local_constant then return e.local_pp_name
    else get_unused_name,
  /- Find the name of the proof of the equation -/
  eq_nm ← if hn : 1 < n.length then return (n.nth_le 1 hn)
    else if e.is_local_constant then return `rfl
    else get_unused_name `h,
  /- We add the proof of the existential statement to the context -/
  temp_nm ← get_unused_name,
  temp_e ← note temp_nm none prf_ex,
  dsimp_hyp temp_e none [] { fail_if_unchanged := ff },
  /- We case on the existential. We use `rcases` because `eq_nm` could be `rfl`. -/
  rcases none (pexpr.of_expr temp_e) $ rcases_patt.tuple ([new_nm, eq_nm].map rcases_patt.one),
  /- If the lifted variable is not a local constant,
    try to rewrite it away using the new equality. -/
  when (¬ e.is_local_constant) (get_local eq_nm >>=
    λ e, interactive.rw ⟨[⟨⟨0, 0⟩, tt, (pexpr.of_expr e)⟩], none⟩ interactive.loc.wildcard),
  /- If the proof `prf_cond` is a local constant, remove it from the context,
    unless `n` specifies to keep it. -/
  if h_prf_nm : prf_nm.is_some ∧ n.nth 2 ≠ prf_nm then
    get_local (option.get h_prf_nm.1) >>= clear else skip,
  if b then skip else swap

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
  This subgoal will be placed at the top of the goal list.
  + So for example the tactic `lift n to ℕ` transforms the goal
    `n : ℤ, h : P n ⊢ n = 3` to two goals
    `n : ℤ, h : P n ⊢ n ≥ 0` and `n : ℕ, h : P ↑n ⊢ ↑n = 3`.
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
