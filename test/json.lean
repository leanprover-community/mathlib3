import data.json
import data.int.basic

@[derive [decidable_eq, non_null_json_serializable]]
structure my_type :=
(x : nat)
(f : fin x)
(y : bool)

run_cmd do
  let actual := to_json (my_type.mk 37 2 tt),
  let expected := json.object [("x", json.of_int 37), ("f", json.of_int 2), ("y", json.of_bool tt)],
  guard (actual = expected)

run_cmd do
  some j ← pure (json.parse "{\"x\":37,\"f\":2,\"y\":true}"),
  x ← of_json my_type j,
  guard (x = ⟨37, 2, tt⟩)
