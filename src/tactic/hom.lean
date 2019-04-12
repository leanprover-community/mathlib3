import algebra.ring
import algebra.group_power
import algebra.big_operators
import algebra.field_power
import tactic.chain

open tactic

universes v u

meta def lookup_homs (n : name) : tactic (list expr) :=
do ctx ← local_context,
   ctx.mfilter (λ e, mk_app n [e] >>= mk_instance >> pure true <|> pure false)

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
| `add_group   := [`is_add_group_hom.map_neg, `is_add_group_hom.map_sub, `is_add_group_hom.map_gsmul, `is_add_group_hom.map_sum]
| `field       := [`is_field_hom.map_div, `is_field_hom.map_inv]
| _ := []

meta def algebraic_types : list name :=
[`has_mul, `has_add, `monoid, `add_monoid, `group, `add_group, `field]

meta def tactics_of_homs (p : name × list expr) : tactic (list (list expr)) :=
let map_lemmas := map_types p.1 in
map_lemmas.mmap $ λ l, p.2.mmap $ λ f,
  do mk_mapp l [none, none, none, none, some f, none]

-- TODO: Enable `hom at hyp`.
meta def hom : tactic unit :=
do homs ← algebraic_types.mmap $ λ t, (do h ← lookup_homs (instance_type t), return (t, h)),
   tactics ← homs.mmap tactics_of_homs,
   let flat_tactics := list.join $ list.join tactics,
   lemmas ← flat_tactics.mfoldl simp_lemmas.add simp_lemmas.mk,
   simp_target lemmas,
   try reflexivity

set_option profiler true

example (X : Type 4) (Y : Type v) [ring X] [ring Y] (f : X → Y) [is_monoid_hom f] (n : ℕ)
  (x y : X) : f (x * y) = f x * f y :=
by hom

example (X : Type u) (Y : Type v) [add_group X] [add_group Y]
  (f : X → Y) [is_add_group_hom f]
  (a b : X) :
  f (a + b) = f a + f b :=
by hom

set_option class.instance_max_depth 50

example (X Y Z W : Type u) [add_group X] [discrete_field Y] [ring Z] [discrete_field W]
  (f : X → Y) [is_add_group_hom f] (g : Y → W) [is_field_hom g]
  (h : X → Z) [is_add_group_hom h] (i : Z → W) [is_ring_hom i]
  (k l m : ℕ) (a b : X) (c d : Y) (e : Z) :
  g (f (a + gsmul k b) * c⁻¹ / d) + i (e^l + ((h (b - a))^m)) =
  (g (f a) + gsmul k (g (f b))) * (g c)⁻¹ / (g d) + ((i e)^l + (i (h b) - i (h a))^m) :=
by hom
