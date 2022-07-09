import data.json
import data.int.basic

open exceptional

open tactic expr

@[derive_handler, priority 2000] meta def non_null_json_serializable_handler : derive_handler :=
instance_derive_handler ``non_null_json_serializable $ do
  intros,
  `(non_null_json_serializable %%e) ← target >>= whnf,
  (const I ls, args) ← pure (get_app_fn_args e),
  env ← get_env,
  some fields ← pure (env.structure_fields I),
  refine ``(@non_null_json_serializable.mk %%e ⟨λ x, json.object _,
    λ j, field_starter j >>= (λ l, _)
  ⟩),
  -- the forward direction
  x ← get_local `x,
  (e : list (option expr)) ← fields.mmap (λ f, do
    d ← get_decl (I ++ f),
    let a := @expr.const tt (I ++ f) $ d.univ_params.map level.param,
    t ← infer_type a,
    s ← infer_type t,
    `(Prop) ← pure s | pure (none : option expr),
    let x_e := a.mk_app (args ++ [x]),
    j ← tactic.mk_app `json_serializable.to_json [x_e],
    tactic.trace j,
    pure (some `((%%`(f.to_string), %%j) : string × json))
  ),
  let e := e.reduce_option,
  tactic.exact (e.to_expr `(string × json)),
  -- the reverse direction

  trace_state,
  s ←tactic.mk_sorry,
  tactic.exact s,
  tactic.trace fields

set_option pp.all true

@[derive decidable_eq]
structure my_type :=
(x : int)
(y : bool)

-- attribute [derive non_null_json_serializable] my_type

-- TODO: how can we generate this?
meta instance : non_null_json_serializable my_type :=
{ to_json := λ x, json.object [("x", x.x), ("y", x.y)],
  of_json := λ j, do
    p ← json_serializable.field_starter j,
    (f_x, p) ← json_serializable.field_extractor p "x" int,
    (f_y, p) ← json_serializable.field_extractor p "y" bool,
    json_serializable.field_terminator p,
    my_type.mk <$> f_x <*> f_y }

run_cmd
  guard (to_json (my_type.mk 37 tt) = json.object [("x", json.of_int 37), ("y", json.of_bool tt)])

run_cmd do
  some j ← pure (json.parse "{\"x\":37,\"y\":true}"),
  x ← of_json my_type j,
  guard (x = ⟨37, tt⟩)
