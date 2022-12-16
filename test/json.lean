import data.json

run_cmd do
  let j := json.of_int 2,
  z ← of_json native.float j,
  guard (z = 2)

run_cmd do
  j ← json.parse "2.0",
  tactic.success_if_fail_with_msg (of_json ℤ j) "number must be integral"

run_cmd do
  let j := json.of_int (-1),
  tactic.success_if_fail_with_msg (of_json ℕ j) "must be non-negative"

run_cmd do
  let j := json.of_int 1,
  v ← of_json {x // x ≠ some 2} j,
  guard (v = ⟨some 1, dec_trivial⟩),
  v ← of_json (option {x // x ≠ 2}) j,
  guard (v = some ⟨1, dec_trivial⟩)

run_cmd do
  let j := json.null,
  v ← of_json {x // x ≠ some 2} j,
  guard (v = ⟨none, dec_trivial⟩),
  v ← of_json (option {x // x ≠ 2}) j,
  guard (v = none)

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

run_cmd do
  some j ← pure (json.parse "{\"x\":37,\"f\":2,\"y\":true,\"z\":true}"),
  tactic.success_if_fail_with_msg (of_json (my_type tt) j) "unexpected fields [z]"

run_cmd do
  some j ← pure (json.parse "{\"x\":37}"),
  tactic.success_if_fail_with_msg (of_json (my_type tt) j) "field f is required"

run_cmd do
  let j := json.object [("x", to_json 37), ("x", to_json 37)],
  tactic.success_if_fail_with_msg (of_json (my_type tt) j) "duplicate x field"

run_cmd do
  let j := json.null,
  tactic.success_if_fail_with_msg (of_json (my_type tt) j) "object expected, got null"

run_cmd do
  some j ← pure (json.parse "{\"x\":37,\"f\":2,\"y\":false}"),
  tactic.success_if_fail_with_msg (of_json (my_type tt) j) "condition does not hold"

@[derive [decidable_eq, non_null_json_serializable]]
structure no_fields (n : ℕ) : Type

run_cmd do
  let actual := to_json (@no_fields.mk 37),
  let expected := json.object [],
  guard (actual = expected)

run_cmd do
  some j ← pure (json.parse "{}"),
  of_json (@no_fields 37) j

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

run_cmd do
  some j ← pure (json.parse "{\"y\":2}"),
  v ← of_json has_default j,
  guard (v = {y := 2})
