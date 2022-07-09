import data.json
import data.int.basic

open exceptional

@[derive decidable_eq]
structure my_type :=
(x : int)
(y : bool)

-- TODO: how can we generate this?
meta instance : non_null_json_serializable my_type :=
{ to_json := λ x, json.object [("x", x.x), ("y", x.y)],
  of_json := λ j, do
    json.object p ← pure j | exception (λ _, format!"object expected, got {j.typename}"),
    (f_x, p) ← extract_field p "x",
    (f_y, p) ← extract_field p "y",
    [] ← pure p | exception (λ _, format!"unexpected fields {p.map prod.fst}"),
    f_x ← of_json int f_x,
    f_y ← of_json bool f_y,
    pure (my_type.mk f_x f_y) }

run_cmd
  guard (to_json (my_type.mk 37 tt) = json.object [("x", json.of_int 37), ("y", json.of_bool tt)])

run_cmd do
  some j ← pure (json.parse "{\"x\":37,\"y\":true}"),
  x ← of_json my_type j,
  guard (x = ⟨37, tt⟩)
