/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import tactic.core

/-!
# Json serialization typeclass

This file provides helpers for serializing primitive types to json.

## Main definitions

* `json_serializable`: a typeclass for objects which serialize to json
* `json_serializable.to_json x`: convert `x` to json
* `json_serializable.of_json α j`: read `j` in as an `α`
-/


open exceptional

meta instance : has_orelse exceptional :=
{ orelse := λ α f g, match f with
  | success x := success x
  | exception msg := g
  end }

meta instance : decidable_eq json :=
begin
  intros j₁ j₂,
  letI := json.decidable_eq,
  cases j₁; cases j₂; simp; apply_instance,
end

meta class json_serializable (α : Type*) :=
(to_json : α → json)
(of_json [] : json → exceptional α)

/-- A class for types which never serialize to null -/
meta class non_null_json_serializable (α : Type*) extends json_serializable α

export json_serializable (to_json of_json)

/-- Describe the type of a json value -/
meta def json.typename : json → string
| (json.of_string _) := "string"
| (json.of_int _) := "number"
| (json.of_float _) := "number"
| (json.of_bool _) := "bool"
| json.null := "null"
| (json.object _) := "object"
| (json.array _) := "array"

/-! ### Primitive types -/

meta instance : non_null_json_serializable string :=
{ to_json := json.of_string,
  of_json := λ j, do
    json.of_string s ← success j | exception (λ _, format!"string expected, got {j.typename}"),
    pure s }

meta instance : non_null_json_serializable ℤ :=
{ to_json := λ z, json.of_int z,
  of_json := λ j, do
    json.of_int z ← success j | exception (λ _, format!"number expected, got {j.typename}"),
    pure z }

meta instance : non_null_json_serializable native.float :=
{ to_json := λ f, json.of_float f,
  of_json := λ j, do
    json.of_int z ← success j | do
    { json.of_float f ← success j | exception (λ _, format!"number expected, got {j.typename}"),
      pure f },
    pure z }

meta instance : non_null_json_serializable bool :=
{ to_json := λ b, json.of_bool b,
  of_json := λ j, do
    json.of_bool b ← success j | exception (λ _, format!"boolean expected, got {j.typename}"),
    pure b }

meta instance : json_serializable punit :=
{ to_json := λ u, json.null,
  of_json := λ j, do
    json.null ← success j | exception (λ _, format!"null expected, got {j.typename}"),
    pure () }

meta instance {α} [json_serializable α] : non_null_json_serializable (list α) :=
{ to_json := λ l, json.array (l.map to_json),
  of_json := λ j, do
    json.array l ← success j | exception (λ _, format!"array expected, got {j.typename}"),
    l.mmap (of_json α) }

meta instance {α} [json_serializable α] : json_serializable (rbmap string α) :=
{ to_json := λ m, json.object (m.to_list.map $ λ x, (x.1, to_json x.2)),
  of_json := λ j, do
    json.object l ← success j | exception (λ _, format!"object expected, got {j.typename}"),
    l ← l.mmap (λ x : string × json, do x2 ← of_json α x.2, pure (x.1, x2)),
    l.mfoldl (λ m x, do
      none ← pure (m.find x.1) | exception (λ _, format!"duplicate key {x.1}"),
      pure (m.insert x.1 x.2)) (mk_rbmap _ _) }

/-! ### Basic coercions -/

meta instance : non_null_json_serializable ℕ :=
{ to_json := λ n, json.of_int n,
  of_json := λ j, do
    json.of_int z ← success j | exception (λ _, format!"number expected, got {j.typename}"),
    int.of_nat n ← success z | exception (λ _, format!"must be non-negative"),
    pure n }

/-- Note this only makes sense on types which do not themselves serialize to `null` -/
meta instance {α} [non_null_json_serializable α] : json_serializable (option α) :=
{ to_json := option.elim json.null to_json,
  of_json := λ j, do (of_json punit j >> pure none) <|> (some <$> of_json α j)}

open tactic expr

meta def list.to_pexpr : ∀ l : list pexpr, pexpr
| [] := ``([])
| (x :: xs) := ``(%%x :: %%xs.to_pexpr)

meta def extract_field (l : list (string × json)) (s : string) :
  exceptional (json × list (string × json)) :=
let (p, n) := l.partition (λ x, prod.fst x = s) in
match p with
| [] := exception (λ _, format!"no {s} field , {l}")
| [x] := pure (x.2, n)
| x :: xs := exception (λ _, format!"duplicate {s} field")
end

@[derive_handler, priority 2000] meta def non_null_json_serializable_handler : derive_handler :=
instance_derive_handler ``non_null_json_serializable $ do
  intros,
  `(non_null_json_serializable %%e) ← target >>= whnf,
  (const I ls, args) ← pure (get_app_fn_args e),
  env ← get_env,
  some fields ← pure (env.structure_fields_full I),
  refine ``(@non_null_json_serializable.mk _ ⟨λ x, json.object _, λ j, sorry⟩),
  x ← mk_local_def `x e,

  (e : list (option pexpr)) ← fields.mmap (λ f, do
    d ← get_decl (I ++ f),
    let a := @expr.const tt (I ++ f) $ d.univ_params.map level.param,
    t ← infer_type a,
    s ← infer_type t,
    `(Prop) ← pure s | pure (none : option pexpr),
    -- let field := a.mk_app [```(x)],
    sorry
  ),

  trace_state,
  tactic.trace fields
