/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis
-/
import tactic.core
/-!
# lint command
This file defines the following user commands to spot common mistakes in the code.
* `#lint`: check all declarations in the current file
* `#lint_mathlib`: check all declarations in mathlib (so excluding core or other projects,
  and also excluding the current file)
* `#lint_all`: check all declarations in the environment (the current file and all
  imported files)

The following linters are run by default:
1.  `unused_arguments` checks for unused arguments in declarations.
2.  `def_lemma` checks whether a declaration is incorrectly marked as a def/lemma.
3.  `dup_namespce` checks whether a namespace is duplicated in the name of a declaration.
4.  `ge_or_gt` checks whether ≥/> is used in the declaration.
5.  `instance_priority` checks that instances that always apply have priority below default.
6.  `doc_blame` checks for missing doc strings on definitions and constants.
7.  `has_inhabited_instance` checks whether every type has an associated `inhabited` instance.
8.  `impossible_instance` checks for instances that can never fire.
9.  `incorrect_type_class_argument` checks for arguments in [square brackets] that are not classes.
10. `dangerous_instance` checks for instances that generate type-class problems with metavariables.

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

Adding the attribute `@[nolint]` to a declaration omits it from all linter checks.

## Tags
sanity check, lint, cleanup, command, tactic
-/

universe variable u
open expr tactic native

reserve notation `#lint`
reserve notation `#lint_mathlib`
reserve notation `#lint_all`
reserve notation `#list_linters`

run_cmd tactic.skip -- apparently doc strings can't come directly after `reserve notation`

/-- Defines the user attribute `nolint` for skipping `#lint` -/
@[user_attribute]
meta def nolint_attr : user_attribute :=
{ name := "nolint",
  descr := "Do not report this declaration in any of the tests of `#lint`" }

attribute [nolint] imp_intro
  classical.dec classical.dec_pred classical.dec_rel classical.dec_eq
  pempty -- has no inhabited instance

/--
A linting test for the `#lint` command.

`test` defines a test to perform on every declaration. It should never fail. Returning `none`
signifies a passing test. Returning `some msg` reports a failing test with error `msg`.

`no_errors_found` is the message printed when all tests are negative, and `errors_found` is printed
when at least one test is positive.

If `is_fast` is false, this test will be omitted from `#lint-`.
-/
meta structure linter :=
(test : declaration → tactic (option string))
(no_errors_found : string)
(errors_found : string)
(is_fast : bool := tt)

/-- Takes a list of names that resolve to declarations of type `linter`,
and produces a list of linters. -/
meta def get_linters (l : list name) : tactic (list linter) :=
l.mmap (λ n, mk_const n >>= eval_expr linter <|> fail format!"invalid linter: {n}")

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

setup_tactic_parser
universe variable v

/-- Find all declarations in `l` where tac returns `some x` and list them. -/
meta def fold_over_with_cond {α} (l : list declaration) (tac : declaration → tactic (option α)) :
  tactic (list (declaration × α)) :=
l.mmap_filter $ λ d, option.map (λ x, (d, x)) <$> tac d

/-- Find all declarations in `l` where tac returns `some x` and sort the resulting list by file name. -/
meta def fold_over_with_cond_sorted {α} (l : list declaration)
  (tac : declaration → tactic (option α)) : tactic (list (string × list (declaration × α))) := do
  e ← get_env,
  ds ← fold_over_with_cond l tac,
  let ds₂ := rb_lmap.of_list (ds.map (λ x, ((e.decl_olean x.1.to_name).iget, x))),
  return $ ds₂.to_list

/-- Make the output of `fold_over_with_cond` printable, in the following form:
      `#print <name> <open multiline comment> <elt of α> <close multiline comment>` -/
meta def print_decls {α} [has_to_format α] (ds : list (declaration × α)) : format :=
ds.foldl
  (λ f x, f ++ "\n" ++ to_fmt "#print " ++ to_fmt x.1.to_name ++ " /- " ++ to_fmt x.2 ++ " -/")
  format.nil

/-- Make the output of `fold_over_with_cond_sorted` printable, with the file path + name inserted.-/
meta def print_decls_sorted {α} [has_to_format α] (ds : list (string × list (declaration × α))) :
  format :=
ds.foldl
  (λ f x, f ++ "\n\n" ++ to_fmt "-- " ++ to_fmt x.1 ++ print_decls x.2)
  format.nil

/-- Same as `print_decls_sorted`, but removing the first `n` characters from the string.
  Useful for omitting the mathlib directory from the output. -/
meta def print_decls_sorted_mathlib {α} [has_to_format α] (n : ℕ)
  (ds : list (string × list (declaration × α))) : format :=
ds.foldl
  (λ f x, f ++ "\n\n" ++ to_fmt "-- " ++ to_fmt (x.1.popn n) ++ print_decls x.2)
  format.nil

/-- Pretty prints a list of arguments of a declaration. Assumes `l` is a list of argument positions
  and binders (or any other element that can be pretty printed).
  `l` can be obtained e.g. by applying `list.indexes_values` to a list obtained by
  `get_pi_binders`. -/
meta def print_arguments {α} [has_to_tactic_format α] (l : list (ℕ × α)) : tactic string := do
  fs ← l.mmap (λ ⟨n, b⟩, (λ s, to_fmt "argument " ++ to_fmt (n+1) ++ ": " ++ s) <$> pp b),
  return $ fs.to_string_aux tt

/- Implementation of the linters -/

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
  This tactic additionally filters out all unused arguments of type `parse _` -/
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
-- TODO: instance_priority should also be tested on automatically-generated declarations
meta def instance_priority (d : declaration) : tactic (option string) := do
  let nm := d.to_name,
  b ← is_instance nm,
  /- return `none` if `d` is not an instance -/
  if ¬ b then return none else do
  prio ← has_attribute `instance nm,
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
  errors_found := "DANGEROUS INSTANCE PRIORITIES.\nThe following instances always apply, and therefore should have a priority < 1000.\nIf you don't know what priority to choose, use priority 100." }

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
{ test := λ d, mcond (bnot <$> has_attribute' `instance d.to_name) (doc_blame_report_defn d) (return none),
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
  no_errors_found := "No types have missing inhabited instances.",
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
  errors_found := "IMPOSSIBLE INSTANCES FOUND.\nThese instances have an argument that cannot be found during type-class resolution, and therefore can never succeed. Either mark the arguments with square brackets (if it is a class), or don't make it an instance" }

/-- Checks whether the definition `nm` unfolds to a class. -/
/- Note: Caching the result of `unfolds_to_class` by giving it an attribute
(so that e.g. `vector_space` or `decidable_eq` would not be repeatedly unfold to check whether it is
a class), did not speed up this tactic when executed on all of mathlib (and instead significantly
slowed it down) -/
meta def unfolds_to_class : name → tactic bool | nm :=
if nm = `has_reflect then return tt else
succeeds $ has_attribute `class nm <|> do
  d ← get_decl nm,
  tt ← unfolds_to_class d.value.lambda_body.pi_codomain.get_app_fn.const_name,
  return 0 -- We do anything that succeeds here. We return a `ℕ` because of `has_attribute`.

/-- Checks whether an instance can never be applied. -/
meta def incorrect_type_class_argument (d : declaration) : tactic (option string) := do
  (binders, _) ← get_pi_binders d.type,
  let instance_arguments := binders.indexes_values $
    λ b : binder, b.info = binder_info.inst_implicit,
  /- the head of the type should either unfold to a class, or be a local constant.
  A local constant is allowed, because that could be a class when applied to the proper arguments. -/
  bad_arguments ← instance_arguments.mfilter $
    λ⟨_, b⟩, let head := b.type.erase_annotations.pi_codomain.get_app_fn in
      if head.is_local_constant then return ff else bnot <$> unfolds_to_class head.const_name,
  _ :: _ ← return bad_arguments | return none,
  (λ s, some $ "These are not classes. " ++ s) <$> print_arguments bad_arguments

/-- A linter object for `impossible_instance`. -/
@[linter, priority 1420] meta def linter.incorrect_type_class_argument : linter :=
{ test := incorrect_type_class_argument,
  no_errors_found := "All declarations have correct type-class arguments",
  errors_found := "INCORRECT TYPE-CLASS ARGUMENTS.\nSome declarations have non-classes between [square brackets]" }

/-- Checks whether an instance is dangerous: it creates a new type-class problem with metavariable arguments. -/
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
  errors_found := "DANGEROUS INSTANCES FOUND.\nThese instances are recursive, and create a new type-class problem which will have metavariables. Currently this linter does not check whether the metavariables only occur in arguments marked with `out_param`, in which case this linter gives a false positive." }

/-- Checks whether a declaration is prop-valued and takes an `inhabited _` argument that is unused
    elsewhere in the type. In this case, that argument can be replaced with `nonempty _`. -/
meta def inhabited_nonempty (d : declaration) : tactic (option string) :=
do tt ← is_prop d.type | return none,
   (binders, _) ← get_pi_binders_dep d.type,
   let inhd_binders := binders.filter $ λ pr, pr.2.type.is_app_of `inhabited,
   if inhd_binders.length = 0 then return none
   else (λ s, some $ "The following `inhabited` instances should be `nonempty`. " ++ s) <$> print_arguments inhd_binders

/-- A linter object for `inhabited_nonempty`. -/
@[linter, priority 1400] meta def linter.inhabited_nonempty : linter :=
{ test := inhabited_nonempty,
  no_errors_found := "No uses of `inhabited` arguments should be replaced with `nonempty`",
  errors_found := "USES OF `inhabited` SHOULD BE REPLACED WITH `nonempty`." }

/- Implementation of the frontend. -/

/-- `get_checks slow extra use_only` produces a list of linters.
`extras` is a list of names that should resolve to declarations with type `linter`.
If `use_only` is true, it only uses the linters in `extra`.
Otherwise, it uses all linters in the environment tagged with `@[linter]`.
If `slow` is false, it only uses the fast default tests. -/
meta def get_checks (slow : bool) (extra : list name) (use_only : bool) :
  tactic (list linter) := do
  default ← if use_only then return [] else attribute.get_instances `linter >>= get_linters,
  let default := if slow then default else default.filter (λ l, l.is_fast),
  list.append default <$> get_linters extra

/-- If `verbose` is true, return `old ++ new`, else return `old`. -/
private meta def append_when (verbose : bool) (old new : format) : format :=
cond verbose (old ++ new) old

private meta def check_fold (printer : (declaration → tactic (option string)) → tactic (name_set × format))
(verbose : bool) : name_set × format → linter → tactic (name_set × format)
| (ns, s) ⟨tac, ok_string, warning_string, _⟩ :=
do (new_ns, f) ← printer tac,
   if f.is_nil then return $ (ns, append_when verbose s format!"/- OK: {ok_string}. -/\n")
  else return $ (ns.union new_ns, s ++ format!"/- {warning_string}: -/" ++ f ++ "\n\n")

/-- The common denominator of `#lint[|mathlib|all]`.
  The different commands have different configurations for `l`, `printer` and `where_desc`.
  If `slow` is false, doesn't do the checks that take a lot of time.
  If `verbose` is false, it will suppress messages from passing checks.
  By setting `checks` you can customize which checks are performed.

  Returns a `name_set` containing the names of all declarations that fail any check in `check`,
  and a `format` object describing the failures. -/
meta def lint_aux (l : list declaration)
  (printer : (declaration → tactic (option string)) → tactic (name_set × format))
  (where_desc : string) (slow verbose : bool) (checks : list linter) : tactic (name_set × format) := do
  let s : format := append_when verbose format.nil "/- Note: This command is still in development. -/\n",
  let s := append_when verbose s format!"/- Checking {l.length} declarations {where_desc} -/\n\n",
  (ns, s) ← checks.mfoldl (check_fold printer verbose) (mk_name_set, s),
  return $ (ns, if slow then s else append_when verbose s "/- (slow tests skipped) -/\n")

/-- Return the message printed by `#lint` and a `name_set` containing all declarations that fail. -/
meta def lint (slow : bool := tt) (verbose : bool := tt) (extra : list name := [])
  (use_only : bool := ff) : tactic (name_set × format) := do
  checks ← get_checks slow extra use_only,
  e ← get_env,
  l ← e.mfilter (λ d,
    if e.in_current_file' d.to_name ∧ ¬ d.to_name.is_internal ∧ ¬ d.is_auto_generated e
    then bnot <$> has_attribute' `nolint d.to_name else return ff),
  lint_aux l (λ t, do lst ← fold_over_with_cond l t, return
                      (name_set.of_list (lst.map (declaration.to_name ∘ prod.fst)), print_decls lst))
    "in the current file" slow verbose checks

private meta def name_list_of_decl_lists (l : list (string × list (declaration × string))) :
  name_set :=
name_set.of_list $ list.join $ l.map $ λ ⟨_, l'⟩, l'.map $ declaration.to_name ∘ prod.fst

/-- Return the message printed by `#lint_mathlib` and a `name_set` containing all declarations that fail. -/
meta def lint_mathlib (slow : bool := tt) (verbose : bool := tt) (extra : list name := [])
  (use_only : bool := ff) : tactic (name_set × format) := do
  checks ← get_checks slow extra use_only,
  e ← get_env,
  ml ← get_mathlib_dir,
  /- note: we don't separate out some of these tests in `lint_aux` because that causes a
    performance hit. That is also the reason for the current formulation using if then else. -/
  l ← e.mfilter (λ d,
    if e.is_prefix_of_file ml d.to_name ∧ ¬ d.to_name.is_internal ∧ ¬ d.is_auto_generated e
    then bnot <$> has_attribute' `nolint d.to_name else return ff),
  let ml' := ml.length,
  lint_aux l (λ t, do lst ← fold_over_with_cond_sorted l t,
     return (name_list_of_decl_lists lst, print_decls_sorted_mathlib ml' lst))
    "in mathlib (only in imported files)" slow verbose checks

/-- Return the message printed by `#lint_all` and a `name_set` containing all declarations that fail. -/
meta def lint_all (slow : bool := tt) (verbose : bool := tt) (extra : list name := [])
  (use_only : bool := ff) : tactic (name_set × format) := do
  checks ← get_checks slow extra use_only,
  e ← get_env,
  l ← e.mfilter (λ d, if ¬ d.to_name.is_internal ∧ ¬ d.is_auto_generated e
    then bnot <$> has_attribute' `nolint d.to_name else return ff),
  lint_aux l (λ t, do lst ← fold_over_with_cond_sorted l t,
    return (name_list_of_decl_lists lst, print_decls_sorted lst))
    "in all imported files (including this one)" slow verbose checks

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
   (_, s) ← scope fast_only.is_none silent.is_none extra use_only,
   when (¬ s.is_nil) $ do
     trace s,
     when silent.is_some $ fail "Linting did not succeed"

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

/-- Use `lint` as a hole command. Note: In a large file, there might be some delay between
  choosing the option and the information appearing -/
@[hole_command] meta def lint_hole_cmd : hole_command :=
{ name := "Lint",
  descr := "Lint: Find common mistakes in current file.",
  action := λ es, do (_, s) ← lint, return [(s.to_string,"")] }

/-- Tries to apply the `nolint` attribute to a list of declarations. Always succeeds, even if some
of the declarations don't exist. -/
meta def apply_nolint_tac (decls : list name) : tactic unit :=
decls.mmap' (λ d, try (nolint_attr.set d () tt))

/-- `apply_nolint id1 id2 ...` tries to apply the `nolint` attribute to `id1`, `id2`, ...
It will always succeed, even if some of the declarations do not exist. -/
@[user_command] meta def apply_nolint_cmd (_ : parse $ tk "apply_nolint") : parser unit :=
ident_* >>= ↑apply_nolint_tac
