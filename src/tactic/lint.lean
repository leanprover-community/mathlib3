/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis
-/
import tactic.core
/-!
# lint commands

This file defines the following user commands to spot common mistakes in the code.
* `#lint`: check all declarations in the current file
* `#lint_mathlib`: check all declarations in mathlib (so excluding core or other projects,
  and also excluding the current file)
* `#lint_all`: check all declarations in the environment (the current file and all
  imported files)

For a list of default / non-default linters, see the "Linting Commands" user command doc entry.

The command `#list_linters` prints a list of the names of all available linters.

You can append a `*` to any command (e.g. `#lint_mathlib*`) to omit the slow tests (4).

You can append a `-` to any command (e.g. `#lint_mathlib-`) to run a silent lint
that suppresses the output of passing checks.
A silent lint will fail if any test fails.

You can append a sequence of linter names to any command to run extra tests, in addition to the
default ones. e.g. `#lint doc_blame_thm` will run all default tests and `doc_blame_thm`.

You can append `only name1 name2 ...` to any command to run a subset of linters, e.g.
`#lint only unused_arguments`

You can add custom linters by defining a term of type `linter` in the `linter` namespace.
A linter defined with the name `linter.my_new_check` can be run with `#lint my_new_check`
or `lint only my_new_check`.
If you add the attribute `@[linter]` to `linter.my_new_check` it will run by default.

Adding the attribute `@[nolint doc_blame unused_arguments]` to a declaration
omits it from only the specified linter checks.

## Tags

sanity check, lint, cleanup, command, tactic
-/

universe variable u
open expr tactic native

reserve notation `#lint`
reserve notation `#lint_mathlib`
reserve notation `#lint_all`
reserve notation `#list_linters`

setup_tactic_parser

-- Manual constant subexpression elimination for performance.
private meta def linter_ns := `linter
private meta def nolint_infix := `_nolint

/--
Computes the declaration name used to store the nolint attribute data.

Retrieving the parameters for user attributes is *extremely* slow.
Hence we store the parameters of the nolint attribute as declarations
in the environment.  E.g. for `@[nolint foo] def bar := _` we add the
following declaration:

```lean
meta def bar._nolint.foo : unit := ()
```
-/
private meta def mk_nolint_decl_name (decl : name) (linter : name) : name :=
(decl ++ nolint_infix) ++ linter

/-- Defines the user attribute `nolint` for skipping `#lint` -/
@[user_attribute]
meta def nolint_attr : user_attribute _ (list name) :=
{ name := "nolint",
  descr := "Do not report this declaration in any of the tests of `#lint`",
  after_set := some $ λ n _ _, (do
    ls@(_::_) ← nolint_attr.get_param n
      | fail "you need to specify at least one linter to disable",
    ls.mmap' $ λ l, do
      get_decl (linter_ns ++ l) <|> fail ("unknown linter: " ++ to_string l),
      try $ add_decl $ declaration.defn (mk_nolint_decl_name n l) []
        `(unit) `(unit.star) (default _) ff),
  parser := ident* }

add_tactic_doc
{ name                     := "nolint",
  category                 := doc_category.attr,
  decl_names               := [`nolint_attr],
  tags                     := ["linting"] }

/--
A linting test for the `#lint` command.

`test` defines a test to perform on every declaration. It should never fail. Returning `none`
signifies a passing test. Returning `some msg` reports a failing test with error `msg`.

`no_errors_found` is the message printed when all tests are negative, and `errors_found` is printed
when at least one test is positive.

If `is_fast` is false, this test will be omitted from `#lint-`.

If `auto_decls` is true, this test will also be executed on automatically generated declarations.
-/
meta structure linter :=
(test : declaration → tactic (option string))
(no_errors_found : string)
(errors_found : string)
(is_fast : bool := tt)
(auto_decls : bool := ff)

/-- Takes a list of names that resolve to declarations of type `linter`,
and produces a list of linters. -/
meta def get_linters (l : list name) : tactic (list (name × linter)) :=
l.mmap (λ n, prod.mk n.last <$> (mk_const n >>= eval_expr linter)
  <|> fail format!"invalid linter: {n}")

/-- Defines the user attribute `linter` for adding a linter to the default set.
Linters should be defined in the `linter` namespace.
A linter `linter.my_new_linter` is referred to as `my_new_linter` (without the `linter` namespace)
when used in `#lint`.
-/
@[user_attribute]
meta def linter_attr : user_attribute unit unit :=
{ name := "linter",
  descr := "Use this declaration as a linting test in #lint",
  after_set := some $ λ nm _ _,
                mk_const nm >>= infer_type >>= unify `(linter) }

add_tactic_doc
{ name                     := "linter",
  category                 := doc_category.attr,
  decl_names               := [`linter_attr],
  tags                     := ["linting"] }

/-- Pretty prints a list of arguments of a declaration. Assumes `l` is a list of argument positions
and binders (or any other element that can be pretty printed).
`l` can be obtained e.g. by applying `list.indexes_values` to a list obtained by
`get_pi_binders`. -/
meta def print_arguments {α} [has_to_tactic_format α] (l : list (ℕ × α)) : tactic string := do
  fs ← l.mmap (λ ⟨n, b⟩, (λ s, to_fmt "argument " ++ to_fmt (n+1) ++ ": " ++ s) <$> pp b),
  return $ fs.to_string_aux tt

/-! ### Implementation of the linters -/

/-- Auxilliary definition for `check_unused_arguments` -/
meta def check_unused_arguments_aux : list ℕ → ℕ → ℕ → expr → list ℕ | l n n_max e :=
if n > n_max then l else
if ¬ is_lambda e ∧ ¬ is_pi e then l else
  let b := e.binding_body in
  let l' := if b.has_var_idx 0 then l else n :: l in check_unused_arguments_aux l' (n+1) n_max b

/-- Check which arguments of a declaration are not used.
Prints a list of natural numbers corresponding to which arguments are not used (e.g.
  this outputs [1, 4] if the first and fourth arguments are unused).
Checks both the type and the value of `d` for whether the argument is used
(in rare cases an argument is used in the type but not in the value).
We return [] if the declaration was automatically generated.
We print arguments that are larger than the arity of the type of the declaration
(without unfolding definitions). -/
meta def check_unused_arguments (d : declaration) : option (list ℕ) :=
let l := check_unused_arguments_aux [] 1 d.type.pi_arity d.value in
if l = [] then none else
let l2 := check_unused_arguments_aux [] 1 d.type.pi_arity d.type in
(l.filter $ λ n, n ∈ l2).reverse

/-- Check for unused arguments, and print them with their position, variable name, type and whether
the argument is a duplicate.
See also `check_unused_arguments`.
This tactic additionally filters out all unused arguments of type `parse _`. -/
meta def unused_arguments (d : declaration) : tactic (option string) := do
  let ns := check_unused_arguments d,
  if ¬ ns.is_some then return none else do
  let ns := ns.iget,
  (ds, _) ← get_pi_binders d.type,
  let ns := ns.map (λ n, (n, (ds.nth $ n - 1).iget)),
  let ns := ns.filter (λ x, x.2.type.get_app_fn ≠ const `interactive.parse []),
  if ns = [] then return none else do
  ds' ← ds.mmap pp,
  ns ← ns.mmap (λ ⟨n, b⟩, (λ s, to_fmt "argument " ++ to_fmt n ++ ": " ++ s ++
    (if ds.countp (λ b', b.type = b'.type) ≥ 2 then " (duplicate)" else "")) <$> pp b),
  return $ some $ ns.to_string_aux tt

/-- A linter object for checking for unused arguments. This is in the default linter set. -/
@[linter, priority 1500] meta def linter.unused_arguments : linter :=
{ test := unused_arguments,
  no_errors_found := "No unused arguments",
  errors_found := "UNUSED ARGUMENTS" }

/-- Checks whether the correct declaration constructor (definition or theorem) by comparing it
  to its sort. Instances will not be printed. -/
/- This test is not very quick: maybe we can speed-up testing that something is a proposition?
  This takes almost all of the execution time. -/
meta def incorrect_def_lemma (d : declaration) : tactic (option string) :=
  if d.is_constant ∨ d.is_axiom
  then return none else do
    is_instance_d ← is_instance d.to_name,
    if is_instance_d then return none else do
      -- the following seems to be a little quicker than `is_prop d.type`.
      expr.sort n ← infer_type d.type, return $
      if d.is_theorem ↔ n = level.zero then none
      else if (d.is_definition : bool) then "is a def, should be a lemma/theorem"
      else "is a lemma/theorem, should be a def"

/-- A linter for checking whether the correct declaration constructor (definition or theorem)
has been used. -/
@[linter, priority 1490] meta def linter.def_lemma : linter :=
{ test := incorrect_def_lemma,
  no_errors_found := "All declarations correctly marked as def/lemma",
  errors_found := "INCORRECT DEF/LEMMA" }

/-- Checks whether a declaration has a namespace twice consecutively in its name -/
meta def dup_namespace (d : declaration) : tactic (option string) :=
is_instance d.to_name >>= λ is_inst,
return $ let nm := d.to_name.components in if nm.chain' (≠) ∨ is_inst then none
  else let s := (nm.find $ λ n, nm.count n ≥ 2).iget.to_string in
  some $ "The namespace `" ++ s ++ "` is duplicated in the name"

/-- A linter for checking whether a declaration has a namespace twice consecutively in its name. -/
@[linter, priority 1480] meta def linter.dup_namespace : linter :=
{ test := dup_namespace,
  no_errors_found := "No declarations have a duplicate namespace",
  errors_found := "DUPLICATED NAMESPACES IN NAME" }

/-- Checks whether a `>`/`≥` is used in the statement of `d`.
Currently it checks only the conclusion of the declaration, to eliminate false positive from
binders such as `∀ ε > 0, ...` -/
meta def ge_or_gt_in_statement (d : declaration) : tactic (option string) :=
return $ let illegal := [`gt, `ge] in if d.type.pi_codomain.contains_constant (λ n, n ∈ illegal)
  then some "the type contains ≥/>. Use ≤/< instead."
  else none

-- TODO: the commented out code also checks for classicality in statements, but needs fixing
-- TODO: this probably needs to also check whether the argument is a variable or @eq <var> _ _
-- meta def illegal_constants_in_statement (d : declaration) : tactic (option string) :=
-- return $ if d.type.contains_constant (λ n, (n.get_prefix = `classical ∧
--   n.last ∈ ["prop_decidable", "dec", "dec_rel", "dec_eq"]) ∨ n ∈ [`gt, `ge])
-- then
--   let illegal1 := [`classical.prop_decidable, `classical.dec, `classical.dec_rel, `classical.dec_eq],
--       illegal2 := [`gt, `ge],
--       occur1 := illegal1.filter (λ n, d.type.contains_constant (eq n)),
--       occur2 := illegal2.filter (λ n, d.type.contains_constant (eq n)) in
--   some $ sformat!"the type contains the following declarations: {occur1 ++ occur2}." ++
--     (if occur1 = [] then "" else " Add decidability type-class arguments instead.") ++
--     (if occur2 = [] then "" else " Use ≤/< instead.")
-- else none

/-- A linter for checking whether illegal constants (≥, >) appear in a declaration's type. -/
@[linter, priority 1470] meta def linter.ge_or_gt : linter :=
{ test := ge_or_gt_in_statement,
  no_errors_found := "Not using ≥/> in declarations",
  errors_found := "USING ≥/> IN DECLARATIONS",
  is_fast := ff }

library_note "nolint_ge" "Currently, the linter forbids the use of `>` and `≥` in definitions and
statements, as they cause problems in rewrites. However, we still allow them in some contexts,
for instance when expressing properties of the operator (as in `cobounded (≥)`), or in quantifiers
such as `∀ ε > 0`. Such statements should be marked with the attribute `nolint` to avoid linter
failures."

/-- checks whether an instance that always applies has priority ≥ 1000. -/
meta def instance_priority (d : declaration) : tactic (option string) := do
  let nm := d.to_name,
  b ← is_instance nm,
  /- return `none` if `d` is not an instance -/
  if ¬ b then return none else do
  (is_persistent, prio) ← has_attribute `instance nm,
  /- return `none` if `d` is has low priority -/
  if prio < 1000 then return none else do
  let (fn, args) := d.type.pi_codomain.get_app_fn_args,
  cls ← get_decl fn.const_name,
  let (pi_args, _) := cls.type.pi_binders,
  guard (args.length = pi_args.length),
  /- List all the arguments of the class that block type-class inference from firing
    (if they are metavariables). These are all the arguments except instance-arguments and
    out-params. -/
  let relevant_args := (args.zip pi_args).filter_map $ λ⟨e, ⟨_, info, tp⟩⟩,
    if info = binder_info.inst_implicit ∨ tp.get_app_fn.is_constant_of `out_param
    then none else some e,
  let always_applies := relevant_args.all expr.is_var ∧ relevant_args.nodup,
  if always_applies then return $ some "set priority below 1000" else return none

library_note "lower instance priority"
"Certain instances always apply during type-class resolution. For example, the instance
`add_comm_group.to_add_group {α} [add_comm_group α] : add_group α` applies to all type-class
resolution problems of the form `add_group _`, and type-class inference will then do an
exhaustive search to find a commutative group. These instances take a long time to fail.
Other instances will only apply if the goal has a certain shape. For example
`int.add_group : add_group ℤ` or
`add_group.prod {α β} [add_group α] [add_group β] : add_group (α × β)`. Usually these instances
will fail quickly, and when they apply, they are almost the desired instance.
For this reason, we want the instances of the second type (that only apply in specific cases) to
always have higher priority than the instances of the first type (that always apply).
See also #1561.

Therefore, if we create an instance that always applies, we set the priority of these instances to
100 (or something similar, which is below the default value of 1000)."

library_note "default priority"
"Instances that always apply should be applied after instances that only apply in specific cases,
see note [lower instance priority] above.

Classes that use the `extends` keyword automatically generate instances that always apply.
Therefore, we set the priority of these instances to 100 (or something similar, which is below the
default value of 1000) using `set_option default_priority 100`.
We have to put this option inside a section, so that the default priority is the default
1000 outside the section."

/-- A linter object for checking instance priorities of instances that always apply.
This is in the default linter set. -/
@[linter, priority 1460] meta def linter.instance_priority : linter :=
{ test := instance_priority,
  no_errors_found := "All instance priorities are good",
  errors_found := "DANGEROUS INSTANCE PRIORITIES.
The following instances always apply, and therefore should have a priority < 1000.
If you don't know what priority to choose, use priority 100.

If this is an automatically generated instance (using the keywords `class` and `extends`),
see note [lower instance priority] and see note [default priority] for instructions to change the priority",
  auto_decls := tt }

/-- Reports definitions and constants that are missing doc strings -/
meta def doc_blame_report_defn : declaration → tactic (option string)
| (declaration.defn n _ _ _ _ _) := doc_string n >> return none <|> return "def missing doc string"
| (declaration.cnst n _ _ _) := doc_string n >> return none <|> return "constant missing doc string"
| _ := return none

/-- Reports definitions and constants that are missing doc strings -/
meta def doc_blame_report_thm : declaration → tactic (option string)
| (declaration.thm n _ _ _) := doc_string n >> return none <|> return "theorem missing doc string"
| _ := return none

/-- A linter for checking definition doc strings -/
@[linter, priority 1450] meta def linter.doc_blame : linter :=
{ test := λ d, mcond (bnot <$> has_attribute' `instance d.to_name)
    (doc_blame_report_defn d) (return none),
  no_errors_found := "No definitions are missing documentation.",
  errors_found := "DEFINITIONS ARE MISSING DOCUMENTATION STRINGS" }

/-- A linter for checking theorem doc strings. This is not in the default linter set. -/
meta def linter.doc_blame_thm : linter :=
{ test := doc_blame_report_thm,
  no_errors_found := "No theorems are missing documentation.",
  errors_found := "THEOREMS ARE MISSING DOCUMENTATION STRINGS",
  is_fast := ff }

/-- Reports declarations of types that do not have an associated `inhabited` instance. -/
meta def has_inhabited_instance (d : declaration) : tactic (option string) := do
tt ← pure d.is_trusted | pure none,
ff ← has_attribute' `reducible d.to_name | pure none,
ff ← has_attribute' `class d.to_name | pure none,
(_, ty) ← mk_local_pis d.type,
ty ← whnf ty,
if ty = `(Prop) then pure none else do
`(Sort _) ← whnf ty | pure none,
insts ← attribute.get_instances `instance,
insts_tys ← insts.mmap $ λ i, expr.pi_codomain <$> declaration.type <$> get_decl i,
let inhabited_insts := insts_tys.filter (λ i,
  i.app_fn.const_name = ``inhabited ∨ i.app_fn.const_name = `unique),
let inhabited_tys := inhabited_insts.map (λ i, i.app_arg.get_app_fn.const_name),
if d.to_name ∈ inhabited_tys then
  pure none
else
  pure "inhabited instance missing"

/-- A linter for missing `inhabited` instances. -/
@[linter, priority 1440]
meta def linter.has_inhabited_instance : linter :=
{ test := has_inhabited_instance,
  no_errors_found := "No types have missing inhabited instances",
  errors_found := "TYPES ARE MISSING INHABITED INSTANCES",
  is_fast := ff }

/-- Checks whether an instance can never be applied. -/
meta def impossible_instance (d : declaration) : tactic (option string) := do
  tt ← is_instance d.to_name | return none,
  (binders, _) ← get_pi_binders_dep d.type,
  let bad_arguments := binders.filter $ λ nb, nb.2.info ≠ binder_info.inst_implicit,
  _ :: _ ← return bad_arguments | return none,
  (λ s, some $ "Impossible to infer " ++ s) <$> print_arguments bad_arguments

/-- A linter object for `impossible_instance`. -/
@[linter, priority 1430] meta def linter.impossible_instance : linter :=
{ test := impossible_instance,
  no_errors_found := "All instances are applicable",
  errors_found := "IMPOSSIBLE INSTANCES FOUND.
These instances have an argument that cannot be found during type-class resolution, and therefore can never succeed. Either mark the arguments with square brackets (if it is a class), or don't make it an instance" }

/-- Checks whether an instance can never be applied. -/
meta def incorrect_type_class_argument (d : declaration) : tactic (option string) := do
  (binders, _) ← get_pi_binders d.type,
  let instance_arguments := binders.indexes_values $
    λ b : binder, b.info = binder_info.inst_implicit,
  /- the head of the type should either unfold to a class, or be a local constant.
  A local constant is allowed, because that could be a class when applied to the
  proper arguments. -/
  bad_arguments ← instance_arguments.mfilter (λ ⟨_, b⟩, do
    (_, head) ← mk_local_pis b.type,
    if head.get_app_fn.is_local_constant then return ff else do
    bnot <$> is_class head),
  _ :: _ ← return bad_arguments | return none,
  (λ s, some $ "These are not classes. " ++ s) <$> print_arguments bad_arguments

/-- A linter object for `incorrect_type_class_argument`. -/
@[linter, priority 1420] meta def linter.incorrect_type_class_argument : linter :=
{ test := incorrect_type_class_argument,
  no_errors_found := "All declarations have correct type-class arguments",
  errors_found := "INCORRECT TYPE-CLASS ARGUMENTS.
Some declarations have non-classes between [square brackets]" }

/-- Checks whether an instance is dangerous: it creates a new type-class problem with metavariable
arguments. -/
meta def dangerous_instance (d : declaration) : tactic (option string) := do
  tt ← is_instance d.to_name | return none,
  (local_constants, target) ← mk_local_pis d.type,
  let instance_arguments := local_constants.indexes_values $
    λ e : expr, e.local_binding_info = binder_info.inst_implicit,
  let bad_arguments := local_constants.indexes_values $ λ x,
      !target.has_local_constant x &&
      (x.local_binding_info ≠ binder_info.inst_implicit) &&
      instance_arguments.any (λ nb, nb.2.local_type.has_local_constant x),
  let bad_arguments : list (ℕ × binder) := bad_arguments.map $ λ ⟨n, e⟩, ⟨n, e.to_binder⟩,
  _ :: _ ← return bad_arguments | return none,
  (λ s, some $ "The following arguments become metavariables. " ++ s) <$> print_arguments bad_arguments

/-- A linter object for `dangerous_instance`. -/
@[linter, priority 1410] meta def linter.dangerous_instance : linter :=
{ test := dangerous_instance,
  no_errors_found := "No dangerous instances",
  errors_found := "DANGEROUS INSTANCES FOUND.\nThese instances are recursive, and create a new type-class problem which will have metavariables.
  Possible solution: remove the instance attribute or make it a local instance instead.

  Currently this linter does not check whether the metavariables only occur in arguments marked with `out_param`, in which case this linter gives a false positive.",
  auto_decls := tt }

/-- Applies expression `e` to local constants, but lifts all the arguments that are `Sort`-valued to
  `Type`-valued sorts. -/
meta def apply_to_fresh_variables (e : expr) : tactic expr := do
t ← infer_type e,
(xs, b) ← mk_local_pis t,
xs.mmap' $ λ x, try $ do {
  u ← mk_meta_univ,
  tx ← infer_type x,
  ttx ← infer_type tx,
  unify ttx (expr.sort u.succ) },
return $ e.app_of_list xs

/-- Tests whether type-class inference search for a class will end quickly when applied to
  variables. This tactic succeeds if `mk_instance` succeeds quickly or fails quickly with the error
  message that it cannot find an instance. It fails if the tactic takes too long, or if any other
  error message is raised.
  We make sure that we apply the tactic to variables living in `Type u` instead of `Sort u`,
  because many instances only apply in that special case, and we do want to catch those loops. -/
meta def fails_quickly (max_steps : ℕ) (d : declaration) : tactic (option string) := do
  e ← mk_const d.to_name,
  tt ← is_class e | return none,
  e' ← apply_to_fresh_variables e,
  sum.inr msg ← retrieve_or_report_error $ tactic.try_for max_steps $
    succeeds_or_fails_with_msg (mk_instance e')
      $ λ s, "tactic.mk_instance failed to generate instance for".is_prefix_of s | return none,
  return $ some $
    if msg = "try_for tactic failed, timeout" then "type-class inference timed out" else msg

/-- A linter object for `fails_quickly`. If we want to increase the maximum number of steps
  type-class inference is allowed to take, we can increase the number `3000` in the definition.
  As of 5 Mar 2020 the longest trace (for `is_add_hom`) takes 2900-3000 "heartbeats". -/
@[linter, priority 1408] meta def linter.fails_quickly : linter :=
{ test := fails_quickly 3000,
  no_errors_found := "No time-class searches timed out",
  errors_found := "TYPE CLASS SEARCHES TIMED OUT.
For the following classes, there is an instance that causes a loop, or an excessively long search.",
  is_fast := ff }

/-- Tests whether there is no instance of type `has_coe α t` where `α` is a variable.
See note [use has_coe_t]. -/
meta def has_coe_variable (d : declaration) : tactic (option string) := do
  tt ← is_instance d.to_name | return none,
  `(has_coe %%a _) ← return d.type.pi_codomain | return none,
  tt ← return a.is_var | return none,
  return $ some $ "illegal instance"

/-- A linter object for `has_coe_variable`. -/
@[linter, priority 1405] meta def linter.has_coe_variable : linter :=
{ test := has_coe_variable,
  no_errors_found := "No invalid `has_coe` instances",
  errors_found := "INVALID `has_coe` INSTANCES.
Make the following declarations instances of the class `has_coe_t` instead of `has_coe`." }

/-- Checks whether a declaration is prop-valued and takes an `inhabited _` argument that is unused
elsewhere in the type. In this case, that argument can be replaced with `nonempty _`. -/
meta def inhabited_nonempty (d : declaration) : tactic (option string) :=
do tt ← is_prop d.type | return none,
   (binders, _) ← get_pi_binders_dep d.type,
   let inhd_binders := binders.filter $ λ pr, pr.2.type.is_app_of `inhabited,
   if inhd_binders.length = 0 then return none
   else (λ s, some $ "The following `inhabited` instances should be `nonempty`. " ++ s) <$>
      print_arguments inhd_binders

/-- A linter object for `inhabited_nonempty`. -/
@[linter, priority 1400] meta def linter.inhabited_nonempty : linter :=
{ test := inhabited_nonempty,
  no_errors_found := "No uses of `inhabited` arguments should be replaced with `nonempty`",
  errors_found := "USES OF `inhabited` SHOULD BE REPLACED WITH `nonempty`." }

/-- `simp_lhs_rhs ty` returns the left-hand and right-hand side of a simp lemma with type `ty`. -/
private meta def simp_lhs_rhs : expr → tactic (expr × expr) | ty := do
ty ← whnf ty transparency.reducible,
-- We only detect a fixed set of simp relations here.
-- This is somewhat justified since for a custom simp relation R,
-- the simp lemma `R a b` is implicitly converted to `R a b ↔ true` as well.
match ty with
| `(¬ %%lhs) := pure (lhs, `(false))
| `(%%lhs = %%rhs) := pure (lhs, rhs)
| `(%%lhs ↔ %%rhs) := pure (lhs, rhs)
| (expr.pi n bi a b) := do
  l ← mk_local' n bi a,
  simp_lhs_rhs (b.instantiate_var l)
| ty := pure (ty, `(true))
end

/-- `simp_lhs ty` returns the left-hand side of a simp lemma with type `ty`. -/
private meta def simp_lhs (ty : expr): tactic expr :=
prod.fst <$> simp_lhs_rhs ty

/-- `simp_is_conditional ty` returns true iff the simp lemma with type `ty` is conditional. -/
private meta def simp_is_conditional : expr → tactic bool | ty := do
ty ← whnf ty transparency.semireducible,
match ty with
| `(¬ %%lhs) := pure ff
| `(%%lhs = _) := pure ff
| `(%%lhs ↔ _) := pure ff
| (expr.pi n bi a b) :=
  if bi ≠ binder_info.inst_implicit ∧ ¬ b.has_var then
    pure tt
  else do
    l ← mk_local' n bi a,
    simp_is_conditional (b.instantiate_var l)
| ty := pure ff
end

private meta def heuristic_simp_lemma_extraction (prf : expr) : tactic (list name) :=
prf.list_constant.to_list.mfilter is_simp_lemma

/-- Reports declarations that are simp lemmas whose left-hand side is not in simp-normal form. -/
meta def simp_nf_linter (timeout := 200000) (d : declaration) : tactic (option string) := do
tt ← is_simp_lemma d.to_name | pure none,
-- Sometimes, a definition is tagged @[simp] to add the equational lemmas to the simp set.
-- In this case, ignore the declaration if it is not a valid simp lemma by itself.
tt ← is_valid_simp_lemma_cnst d.to_name | pure none,
(λ tac, tactic.try_for timeout tac <|> pure (some "timeout")) $ -- last resort
(λ tac : tactic _, tac <|> pure none) $ -- tc resolution depth
retrieve $ do
reset_instance_cache,
g ← mk_meta_var d.type,
set_goals [g],
intros,
(lhs, rhs) ← target >>= simp_lhs_rhs,
sls ← simp_lemmas.mk_default,
let sls' := sls.erase [d.to_name],
-- TODO: should we do something special about rfl-lemmas?
(lhs', prf1) ← simplify sls [] lhs {fail_if_unchanged := ff},
prf1_lems ← heuristic_simp_lemma_extraction prf1,
if d.to_name ∈ prf1_lems then pure none else do
(rhs', prf2) ← simplify sls [] rhs {fail_if_unchanged := ff},
lhs'_eq_rhs' ← succeeds (is_def_eq lhs' rhs' transparency.reducible),
lhs_in_nf ← succeeds (is_def_eq lhs' lhs transparency.reducible),
if lhs'_eq_rhs' ∧ lhs'.get_app_fn.const_name = rhs'.get_app_fn.const_name then do
  used_lemmas ← heuristic_simp_lemma_extraction (prf1 prf2),
  pure $ pure $ "simp can prove this:\n"
    ++ "  by simp only " ++ to_string used_lemmas ++ "\n"
    ++ "One of the lemmas above could be a duplicate.\n"
    ++ "If that's not the case try reordering lemmas or adding @[priority].\n"
else if ¬ lhs_in_nf then do
  lhs ← pp lhs,
  lhs' ← pp lhs',
  pure $ format.to_string $
    to_fmt "Left-hand side simplifies from"
      ++ lhs.group.indent 2 ++ format.line
      ++ "to" ++ lhs'.group.indent 2 ++ format.line
      ++ "using " ++ (to_fmt prf1_lems).group.indent 2 ++ format.line
      ++ "Try to change the left-hand side to the simplified term!\n"
else
  pure none

/-- A linter for simp lemmas whose lhs is not in simp-normal form, and which hence never fire. -/
@[linter, priority 1390] meta def linter.simp_nf : linter :=
{ test := simp_nf_linter,
  no_errors_found := "All left-hand sides of simp lemmas are in simp-normal form",
  errors_found := "SOME SIMP LEMMAS ARE REDUNDANT.
That is, their left-hand side is not in simp-normal form.
These lemmas are hence never used by the simplifier.

This linter gives you a list of other simp lemmas, look at them!

Here are some guidelines to get you started:

  1. 'the left-hand side reduces to XYZ':
     you should probably use XYZ as the left-hand side.

  2. 'simp can prove this':
     This typically means that lemma is a duplicate, or is shadowed by another lemma:

     2a. Always put more general lemmas after specific ones:

      @[simp] lemma zero_add_zero : 0 + 0 = 0 := rfl
      @[simp] lemma add_zero : x + 0 = x := rfl

      And not the other way around!  The simplifier always picks the last matching lemma.

     2b. You can also use @[priority] instead of moving simp-lemmas around in the file.

      Tip: the default priority is 1000.
      Use `@[priority 1100]` instead of moving a lemma down,
      and `@[priority 900]` instead of moving a lemma up.

     2c. Conditional simp lemmas are tried last, if they are shadowed
         just remove the simp attribute.

     2d. If two lemmas are duplicates, the linter will complain about the first one.
         Try to fix the second one instead!
         (You can find it among the other simp lemmas the linter prints out!)
" }

private meta def simp_var_head (d : declaration) : tactic (option string) := do
tt ← is_simp_lemma d.to_name | pure none,
-- Sometimes, a definition is tagged @[simp] to add the equational lemmas to the simp set.
-- In this case, ignore the declaration if it is not a valid simp lemma by itself.
tt ← is_valid_simp_lemma_cnst d.to_name | pure none,
lhs ← simp_lhs d.type,
head_sym@(expr.local_const _ _ _ _) ← pure lhs.get_app_fn | pure none,
head_sym ← pp head_sym,
pure $ format.to_string $ "Left-hand side has variable as head symbol: " ++ head_sym

/--
A linter for simp lemmas whose lhs has a variable as head symbol,
and which hence never fire.
-/
@[linter, priority 1389] meta def linter.simp_var_head : linter :=
{ test := simp_var_head,
  no_errors_found :=
    "No left-hand sides of a simp lemma has a variable as head symbol",
  errors_found := "LEFT-HAND SIDE HAS VARIABLE AS HEAD SYMBOL.\n" ++
    "Some simp lemmas have a variable as head symbol of the left-hand side" }

private meta def simp_comm (d : declaration) : tactic (option string) := do
tt ← is_simp_lemma d.to_name | pure none,
-- Sometimes, a definition is tagged @[simp] to add the equational lemmas to the simp set.
-- In this case, ignore the declaration if it is not a valid simp lemma by itself.
tt ← is_valid_simp_lemma_cnst d.to_name | pure none,
(lhs, rhs) ← simp_lhs_rhs d.type,
if lhs.get_app_fn.const_name ≠ rhs.get_app_fn.const_name then pure none else do
(lhs', rhs') ← (prod.snd <$> mk_meta_pis d.type) >>= simp_lhs_rhs,
tt ← succeeds $ unify rhs' lhs transparency.reducible | pure none,
tt ← succeeds $ is_def_eq rhs lhs' transparency.reducible | pure none,
-- ensure that the second application makes progress:
ff ← succeeds $ is_def_eq lhs' rhs' transparency.reducible | pure none,
pure $ "should not be marked simp"

/-- A linter for commutativity lemmas that are marked simp. -/
@[linter, priority 1385] meta def linter.simp_comm : linter :=
{ test := simp_comm,
  no_errors_found := "No commutativity lemma is marked simp",
  errors_found := "COMMUTATIVITY LEMMA IS SIMP.\n" ++
    "Some commutativity lemmas are simp lemmas" }

/-! ### Implementation of the frontend -/

/-- `get_checks slow extra use_only` produces a list of linters.
`extras` is a list of names that should resolve to declarations with type `linter`.
If `use_only` is true, it only uses the linters in `extra`.
Otherwise, it uses all linters in the environment tagged with `@[linter]`.
If `slow` is false, it only uses the fast default tests. -/
meta def get_checks (slow : bool) (extra : list name) (use_only : bool) :
  tactic (list (name × linter)) := do
  default ← if use_only then return [] else attribute.get_instances `linter >>= get_linters,
  let default := if slow then default else default.filter (λ l, l.2.is_fast),
  list.append default <$> get_linters extra

/-- `should_be_linted linter decl` returns true if `decl` should be checked
using `linter`, i.e., if there is no `nolint` attribute. -/
meta def should_be_linted (linter : name) (decl : name) : tactic bool := do
e ← get_env,
pure $ ¬ e.contains (mk_nolint_decl_name decl linter)

/--
`lint_core all_decls non_auto_decls checks` applies the linters `checks` to the list of declarations.
If `auto_decls` is false for a linter (default) the linter is applied to `non_auto_decls`.
If `auto_decls` is true, then it is applied to `all_decls`.
The resulting list has one element for each linter, containing the linter as
well as a map from declaration name to warning.
-/
meta def lint_core (all_decls non_auto_decls : list declaration) (checks : list (name × linter)) :
  tactic (list (name × linter × rb_map name string)) := do
checks.mmap $ λ ⟨linter_name, linter⟩, do
  let test_decls := if linter.auto_decls then all_decls else non_auto_decls,
  results ← test_decls.mfoldl (λ (results : rb_map name string) decl, do
    tt ← should_be_linted linter_name decl.to_name | pure results,
    some linter_warning ← linter.test decl | pure results,
    pure $ results.insert decl.to_name linter_warning) mk_rb_map,
  pure (linter_name, linter, results)

/-- Sorts a map with declaration keys as names by line number. -/
meta def sort_results {α} (results : rb_map name α) : tactic (list (name × α)) := do
e ← get_env,
pure $ list.reverse $ rb_lmap.values $ rb_lmap.of_list $
  results.fold [] $ λ decl linter_warning results,
    (((e.decl_pos decl).get_or_else ⟨0,0⟩).line, (decl, linter_warning)) :: results

/-- Formats a linter warning as `#print` command with comment. -/
meta def print_warning (decl_name : name) (warning : string) : format :=
"#print " ++ to_fmt decl_name ++ " /- " ++ warning ++ " -/"

/-- Formats a map of linter warnings using `print_warning`, sorted by line number. -/
meta def print_warnings (results : rb_map name string) : tactic format := do
results ← sort_results results,
pure $ format.intercalate format.line $ results.map $
  λ ⟨decl_name, warning⟩, print_warning decl_name warning

/--
Formats a map of linter warnings grouped by filename with `-- filename` comments.
The first `drop_fn_chars` characters are stripped from the filename.
-/
meta def grouped_by_filename (results : rb_map name string) (drop_fn_chars := 0)
  (formatter: rb_map name string → tactic format) : tactic format := do
e ← get_env,
let results := results.fold (rb_map.mk string (rb_map name string)) $
  λ decl_name linter_warning results,
    let fn := (e.decl_olean decl_name).get_or_else "" in
    results.insert fn (((results.find fn).get_or_else mk_rb_map).insert
      decl_name linter_warning),
l ← results.to_list.reverse.mmap (λ ⟨fn, results⟩, do
  formatted ← formatter results,
  pure ("-- " ++ fn.popn drop_fn_chars ++ "\n" ++ formatted : format)),
return $ format.intercalate "\n\n" l ++ "\n"

/-- The common denominator of `#lint[|mathlib|all]`.
The different commands have different configurations for `l`,
`group_by_filename` and `where_desc`.
If `slow` is false, doesn't do the checks that take a lot of time.
If `verbose` is false, it will suppress messages from passing checks.
By setting `checks` you can customize which checks are performed.

Returns a `name_set` containing the names of all declarations that fail any check in `check`,
and a `format` object describing the failures. -/
meta def lint_aux (decls : list declaration) (group_by_filename : option nat)
    (where_desc : string) (slow verbose : bool) (checks : list (name × linter)) :
  tactic (name_set × format) := do
e ← get_env,
let non_auto_decls := decls.filter (λ d, ¬ d.to_name.is_internal ∧ ¬ d.is_auto_generated e),
results ← lint_core decls non_auto_decls checks,
formatted_results ← results.mmap $ λ ⟨linter_name, linter, results⟩,
  let report_str : format := to_fmt "/- The `" ++ to_fmt linter_name ++ "` linter reports: -/\n" in
  if ¬ results.empty then do
    warnings ← match group_by_filename with
      | none := print_warnings results
      | some dropped := grouped_by_filename results dropped print_warnings
      end,
      pure $ report_str ++ "/- " ++ linter.errors_found ++ ": -/\n" ++ warnings ++ "\n"
  else
    pure $ if verbose then "/- OK: " ++ linter.no_errors_found ++ ". -/" else format.nil,
let s := format.intercalate "\n" (formatted_results.filter (λ f, ¬ f.is_nil)),
let s := if ¬ verbose then s else
  format!"/- Checking {non_auto_decls.length} declarations (plus {decls.length - non_auto_decls.length} automatically generated ones) {where_desc} -/\n\n" ++ s,
let s := if slow then s else s ++ "/- (slow tests skipped) -/\n",
let ns := name_set.of_list (do (_,_,rs) ← results, rs.keys),
pure (ns, s)

/-- Return the message printed by `#lint` and a `name_set` containing all declarations that fail. -/
meta def lint (slow : bool := tt) (verbose : bool := tt) (extra : list name := [])
  (use_only : bool := ff) : tactic (name_set × format) := do
  checks ← get_checks slow extra use_only,
  e ← get_env,
  let l := e.filter (λ d, e.in_current_file' d.to_name),
  lint_aux l none "in the current file" slow verbose checks

/-- Returns the declarations considered by the mathlib linter. -/
meta def lint_mathlib_decls : tactic (list declaration) := do
e ← get_env,
ml ← get_mathlib_dir,
pure $ e.filter $ λ d, e.is_prefix_of_file ml d.to_name

/-- Return the message printed by `#lint_mathlib` and a `name_set` containing all declarations
that fail. -/
meta def lint_mathlib (slow : bool := tt) (verbose : bool := tt) (extra : list name := [])
  (use_only : bool := ff) : tactic (name_set × format) := do
checks ← get_checks slow extra use_only,
decls ← lint_mathlib_decls,
mathlib_path_len ← string.length <$> get_mathlib_dir,
lint_aux decls mathlib_path_len "in mathlib (only in imported files)" slow verbose checks

/-- Return the message printed by `#lint_all` and a `name_set` containing all declarations
that fail. -/
meta def lint_all (slow : bool := tt) (verbose : bool := tt) (extra : list name := [])
  (use_only : bool := ff) : tactic (name_set × format) := do
  checks ← get_checks slow extra use_only,
  e ← get_env,
  let l := e.get_decls,
  lint_aux l (some 0) "in all imported files (including this one)" slow verbose checks

/-- Parses an optional `only`, followed by a sequence of zero or more identifiers.
Prepends `linter.` to each of these identifiers. -/
private meta def parse_lint_additions : parser (bool × list name) :=
prod.mk <$> only_flag <*> (list.map (name.append `linter) <$> ident_*)

/-- The common denominator of `lint_cmd`, `lint_mathlib_cmd`, `lint_all_cmd` -/
private meta def lint_cmd_aux (scope : bool → bool → list name → bool → tactic (name_set × format)) :
  parser unit :=
do silent ← optional (tk "-"),
   fast_only ← optional (tk "*"),
   silent ← if silent.is_some then return silent else optional (tk "-"), -- allow either order of *-
   (use_only, extra) ← parse_lint_additions,
   (failed, s) ← scope fast_only.is_none silent.is_none extra use_only,
   when (¬ s.is_nil) $ trace s,
   when (silent.is_some ∧ ¬ failed.empty) $
    fail "Linting did not succeed"

/-- The command `#lint` at the bottom of a file will warn you about some common mistakes
in that file. Usage: `#lint`, `#lint linter_1 linter_2`, `#lint only linter_1 linter_2`.
`#lint-` will suppress the output of passing checks.
Use the command `#list_linters` to see all available linters. -/
@[user_command] meta def lint_cmd (_ : parse $ tk "#lint") : parser unit :=
lint_cmd_aux @lint

/-- The command `#lint_mathlib` checks all of mathlib for certain mistakes.
Usage: `#lint_mathlib`, `#lint_mathlib linter_1 linter_2`, `#lint_mathlib only linter_1 linter_2`.
`#lint_mathlib-` will suppress the output of passing checks.
Use the command `#list_linters` to see all available linters. -/
@[user_command] meta def lint_mathlib_cmd (_ : parse $ tk "#lint_mathlib") : parser unit :=
lint_cmd_aux @lint_mathlib

/-- The default linters used in mathlib CI. -/
meta def mathlib_linters : list name := by do
ls ← get_checks tt [] ff,
let ls := ls.map (λ ⟨n, _⟩, `linter ++ n),
exact (reflect ls)

/-- `lint_mathlib_ci` runs the linters for the CI. -/
meta def lint_mathlib_ci : tactic unit := do
(failed, s) ← lint_mathlib tt tt mathlib_linters tt,
trace s,
when (¬ failed.empty) $ fail "Linting did not succeed"

/-- The command `#lint_all` checks all imported files for certain mistakes.
Usage: `#lint_all`, `#lint_all linter_1 linter_2`, `#lint_all only linter_1 linter_2`.
`#lint_all-` will suppress the output of passing checks.
Use the command `#list_linters` to see all available linters. -/
@[user_command] meta def lint_all_cmd (_ : parse $ tk "#lint_all") : parser unit :=
lint_cmd_aux @lint_all

/-- The command `#list_linters` prints a list of all available linters. -/
@[user_command] meta def list_linters (_ : parse $ tk "#list_linters") : parser unit :=
do env ← get_env,
let ns := env.decl_filter_map $ λ dcl,
    if (dcl.to_name.get_prefix = `linter) && (dcl.type = `(linter)) then some dcl.to_name else none,
   trace "Available linters:\n  linters marked with (*) are in the default lint set\n",
   ns.mmap' $ λ n, do
     b ← has_attribute' `linter n,
     trace $ n.pop_prefix.to_string ++ if b then " (*)" else ""

/-- Tries to apply the `nolint` attribute to a list of declarations. Always succeeds, even if some
of the declarations don't exist. -/
meta def apply_nolint_tac (decl : name) (linters : list name) : tactic unit :=
try $ nolint_attr.set decl linters tt

/-- `apply_nolint decl linter1 linter2 ...` tries to apply
the `nolint linter1 linter2 ...` attribute to `decl`, ...
It will always succeed, even if some of the declarations do not exist. -/
@[user_command] meta def apply_nolint_cmd (_ : parse $ tk "apply_nolint") : parser unit := do
decl_name ← ident,
linter_names ← ident*,
apply_nolint_tac decl_name linter_names

add_tactic_doc
{ name                     := "linting commands",
  category                 := doc_category.cmd,
  decl_names               := [`lint_cmd, `lint_mathlib_cmd, `lint_all_cmd, `list_linters,
                               `apply_nolint_cmd],
  tags                     := ["linting"],
  description              :=
"User commands to spot common mistakes in the code

* `#lint`: check all declarations in the current file
* `#lint_mathlib`: check all declarations in mathlib (so excluding core or other projects,
  and also excluding the current file)
* `#lint_all`: check all declarations in the environment (the current file and all
  imported files)

The following linters are run by default:
1. `unused_arguments` checks for unused arguments in declarations.
2. `def_lemma` checks whether a declaration is incorrectly marked as a def/lemma.
3. `dup_namespce` checks whether a namespace is duplicated in the name of a declaration.
4. `ge_or_gt` checks whether ≥/> is used in the declaration.
5. `instance_priority` checks that instances that always apply have priority below default.
6. `doc_blame` checks for missing doc strings on definitions and constants.
7.  `has_inhabited_instance` checks whether every type has an associated `inhabited` instance.
8.  `impossible_instance` checks for instances that can never fire.
9.  `incorrect_type_class_argument` checks for arguments in [square brackets] that are not classes.
10. `dangerous_instance` checks for instances that generate type-class problems with metavariables.
11. `fails_quickly` tests that type-class inference ends (relatively) quickly when applied to variables.
12. `has_coe_variable` tests that there are no instances of type `has_coe α t` for a variable `α`.
13. `inhabited_nonempty` checks for `inhabited` instance arguments that should be changed to `nonempty`.
14. `simp_nf` checks that the left-hand side of simp lemmas is in simp-normal form.
15. `simp_var_head` checks that there are no variables as head symbol of left-hand sides of simp lemmas.
16. `simp_comm` checks that no commutativity lemmas (such as `add_comm`) are marked simp.

Another linter, `doc_blame_thm`, checks for missing doc strings on lemmas and theorems.
This is not run by default.

The command `#list_linters` prints a list of the names of all available linters.

You can append a `*` to any command (e.g. `#lint_mathlib*`) to omit the slow tests (4).

You can append a `-` to any command (e.g. `#lint_mathlib-`) to run a silent lint
that suppresses the output of passing checks.
A silent lint will fail if any test fails.

You can append a sequence of linter names to any command to run extra tests, in addition to the
default ones. e.g. `#lint doc_blame_thm` will run all default tests and `doc_blame_thm`.

You can append `only name1 name2 ...` to any command to run a subset of linters, e.g.
`#lint only unused_arguments`

You can add custom linters by defining a term of type `linter` in the `linter` namespace.
A linter defined with the name `linter.my_new_check` can be run with `#lint my_new_check`
or `lint only my_new_check`.
If you add the attribute `@[linter]` to `linter.my_new_check` it will run by default.

Adding the attribute `@[nolint doc_blame unused_arguments]` to a declaration
omits it from only the specified linter checks." }

attribute [nolint unused_arguments] imp_intro
attribute [nolint def_lemma] classical.dec classical.dec_pred classical.dec_rel classical.dec_eq
attribute [nolint has_inhabited_instance] pempty

/--
Invoking the hole command `lint` ("Find common mistakes in current file") will print text that
indicates mistakes made in the file above the command. It is equivalent to copying and pasting the
output of `#lint`. On large files, it may take some time before the output appears.
-/
@[hole_command] meta def lint_hole_cmd : hole_command :=
{ name := "Lint",
  descr := "Lint: Find common mistakes in current file.",
  action := λ es, do (_, s) ← lint, return [(s.to_string,"")] }

add_tactic_doc
{ name                     := "Lint",
  category                 := doc_category.hole_cmd,
  decl_names               := [`lint_hole_cmd],
  tags                     := ["linting"] }
