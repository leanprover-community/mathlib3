import algebra.ring
import algebra.group_power
import tactic.chain

open tactic

-- this instance can go once the hom-mul PR is merged
instance is_mul_hom_of_is_monoid_hom {X Y : Type*} [monoid X] [monoid Y]
  (f : X → Y) [I : is_monoid_hom f] : is_mul_hom f :=
{..I}

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

meta def map_types : name → (list name)
| `has_mul     := [`is_mul_hom.map_mul]
| `has_add     := [`is_add_hom.map_add]
| `monoid      := [`is_monoid_hom.map_one, `is_monoid_hom.map_pow]
| `add_monoid  := [`is_add_monoid_hom.map_zero, `is_add_monoid_hom.map_smul]
| `group       := [`is_group_hom.map_inv]
| `add_group   := [`is_add_group_hom.map_neg]
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
