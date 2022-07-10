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

@[derive [decidable_eq, non_null_json_serializable]]
structure no_fields (n : ℕ) : Type

run_cmd do
  let actual := to_json (@no_fields.mk 37),
  let expected := json.object [],
  guard (actual = expected)

run_cmd do
  some j ← pure (json.parse "{}"),
  of_json (@no_fields 37) j

-- @[derive [decidable_eq, non_null_json_serializable]]
structure has_default : Type :=
(x : ℕ := 2)
(y : fin x.succ := 3 * fin.of_nat x)
(z : ℕ := 3)

open exceptional

-- This is what we need to generate
meta def has_default.of_json (j : json) : exceptional (has_default) :=
do
  p ← json_serializable.field_starter j,
  (f_y, p) ← json_serializable.field_get p "y",
  (f_z, p) ← json_serializable.field_get p "z",
  f_y.mmap (of_json _) >>= option.elim
    (f_z.mmap (of_json _) >>= option.elim
      (pure {has_default.})
      (λ z, pure {has_default. z := z})
    )
    (λ y, f_z.mmap (of_json _) >>= option.elim
        (pure {has_default.})
        (λ z, pure {has_default. y := y, z := z})
    )

run_cmd do
  e ← has_default.of_json (json.object []),
  tactic.trace e.z


run_cmd do
  expr.macro m [e, l] ← pure ``({x := 10, z := 30} : has_default),
  expr.macro m [x, z] ← pure l,
  tactic.trace (x)

run_cmd do
  let actual := to_json (has_default.mk 1 2 3),
  let expected := json.object [("x", json.of_int 1), ("y", json.of_int 2), ("z", json.of_int 3)],
  guard (actual = expected)

run_cmd do
  some j ← pure (json.parse "{\"x\":1,\"z\":3}"),
  of_json has_default j

#check tactic.interactive.refine_struct
