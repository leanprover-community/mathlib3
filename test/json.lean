import data.json
import data.int.basic

@[derive [decidable_eq, non_null_json_serializable]]
structure my_type (yval : bool) :=
(x : nat)
(f : fin x)
(y : bool)
(h : y = yval)

run_cmd do
  let actual := to_json (my_type.mk 37 2 tt rfl),
  let expected := json.object [("x", json.of_int 37), ("f", json.of_int 2), ("y", json.of_bool tt)],
  guard (actual = expected)

run_cmd do
  some j ← pure (json.parse "{\"x\":37,\"f\":2,\"y\":true}"),
  x ← of_json (my_type tt) j,
  guard (x = ⟨37, 2, tt, rfl⟩)

-- this probably needs https://github.com/leanprover-community/lean/pull/739
/-
@[derive [decidable_eq, non_null_json_serializable]]
structure no_fields (n : ℕ) : Type

run_cmd do
  let actual := to_json (@no_fields.mk 37),
  let expected := json.object [],
  guard (actual = expected)

run_cmd do
  some j ← pure (json.parse "{}"),
  of_json (@no_fields 37) j
-/

@[derive [decidable_eq, non_null_json_serializable]]
structure has_default : Type :=
(x : ℕ := 2)
(y : fin x.succ := 3 * fin.of_nat x)
(z : ℕ := 3)

run_cmd do
  e ← of_json has_default (json.object []),
  guard (e = {})

run_cmd do
  let actual := to_json (has_default.mk 2 1 3),
  let expected := json.object [("x", json.of_int 2), ("y", json.of_int 1), ("z", json.of_int 3)],
  guard (actual = expected)

run_cmd do
  some j ← pure (json.parse "{\"x\":1,\"z\":3}"),
  of_json has_default j
