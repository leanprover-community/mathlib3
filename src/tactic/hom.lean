import algebra.ring
import algebra.group_power
import tactic.chain

open tactic

-- -- this instance can go once the hom-mul PR is merged
-- instance is_mul_hom_of_is_monoid_hom {X Y : Type*} [monoid X] [monoid Y]
--   (f : X → Y) [I : is_monoid_hom f] : is_mul_hom f :=
-- {..I}

meta def rw_map (map_lemma : name) (f : expr) :=
do c ← mk_const map_lemma,
   to_expr ``(%%c %%f) >>= rewrite_target

meta def lookup_homs (n : name) : tactic (list expr) :=
do cn ← mk_const n,
do ctx ← local_context,
   ctx.mfilter (λ e, to_expr ``(%%cn %%e) >>= mk_instance >> pure true <|> pure false)

meta def instance_type : name → name
| `has_mul     := `is_mul_hom
| `has_add     := `is_add_hom
| `monoid      := `is_monoid_hom
| `add_monoid  := `is_add_monoid_hom
| `group       := `is_group_hom
| `add_group   := `is_add_group_hom
| `field       := `is_field_hom
| _ := name.anonymous

/-
TODO:
* Put the map lemmas in the root namespace
  - This also takes care of all the inference of classes like `is_monoid_hom` or `is_add_group_hom`.
  - So we want map lemmas with names _root_.map_mul, _root_.map_smul, etc
* I am afraid that this will not work for `is_field_hom.map_inv`
* Generalise `map_prod` to mul_homs (idem for map_sum)
* Add `is_anti_group_hom.{map_one,map_mul,map_prod}` [these lemmas are in mathlib]
  - This might require some thought.
  - Because `instance_type` currently has type `name → name`,
  - and it maps `group` to `is_group_hom`. Maybe that should become list-valued?
-/
meta def map_types : name → (list name)
| `has_mul     := [`is_mul_hom.map_mul]
| `has_add     := [`is_add_hom.map_add]
| `monoid      := [`is_monoid_hom.map_one, `is_monoid_hom.map_pow]
| `add_monoid  := [`is_add_monoid_hom.map_zero, `is_add_monoid_hom.map_smul]
| `group       := [`is_group_hom.map_inv, `is_group_hom.map_prod]
| `add_group   := [`is_add_group_hom.map_neg, `is_add_group_hom.map_sum]
| `field       := [`is_field_hom.map_div, `is_field_hom.map_inv]
| _ := []

meta def types : list name :=
[`has_mul, `has_add, `monoid, `add_monoid, `group, `add_group, `field]

meta def tactics_of_homs (p : name × tactic (list expr)) : tactic (list (list (tactic unit))) :=
do let map_lemmas := map_types p.1,
   fs ← p.2,
   return $ map_lemmas.map $ λ l, fs.map $ λ f, rw_map l f

-- TODO: Enable `hom at hyp`.
meta def hom : tactic unit :=
do let homs := types.map $ λ t, (t, lookup_homs (instance_type t)),
   tactics ← homs.mmap tactics_of_homs,
   let flat_tactics := list.join $ list.join tactics,
   chain flat_tactics,
   try reflexivity

example (X Y : Type) [ring X] [ring Y] (f : X → Y) [is_monoid_hom f] (n : ℕ)
  (x y : X) : f (x^n * y) = (f x)^n * f y :=
begin
  hom,
end
