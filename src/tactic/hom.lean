import algebra.ring
import algebra.group_power
import tactic.chain

open tactic

instance is_mul_hom_of_is_monoid_hom {X Y : Type*} [monoid X] [monoid Y]
  (f : X → Y) [I : is_monoid_hom f] : is_mul_hom f :=
{..I}

meta def rw_map (ht : name) (f : expr) :=
do cht ← mk_const ht,
   to_expr ``(%%cht %%f) >>= rewrite_target

-- meta def map_mul (f : expr) : tactic unit :=
-- rw_map `is_mul_hom.map_mul f
-- meta def map_one (f : expr) : tactic unit :=
-- do to_expr ``(is_monoid_hom.map_one %%f) >>= rewrite_target
-- meta def map_pow (f : expr) : tactic unit :=
-- do to_expr ``(is_monoid_hom.map_pow %%f) >>= rewrite_target
-- meta def map_inv (f : expr) : tactic unit :=
-- do to_expr ``(is_group_hom.map_inv %%f) >>= rewrite_target

meta def lookup_homs (n : name) : tactic (list expr) :=
do cn ← mk_const n,
do ctx ← local_context,
   ctx.mfilter (λ e, to_expr ``(%%cn %%e) >>= mk_instance >> pure true <|> pure false)

-- meta def mul_homs : tactic (list expr) :=
-- do lookup_homs `is_mul_hom
-- meta def monoid_homs : tactic (list expr) :=
-- do lookup_homs `is_monoid_hom
-- meta def group_homs : tactic (list expr) :=
-- do lookup_homs `is_group_hom

-- meta def push_monoid_hom (f : expr) : tactic unit :=
-- do mul ← to_expr ``(is_monoid_hom.map_mul %%f),
--    one ← to_expr ``(is_monoid_hom.map_one %%f),
--    chain [rewrite_target one, rewrite_target mul],
--    skip

meta def instance_type : name → name
| `has_mul   := `is_mul_hom
| `monoid    := `is_monoid_hom
| `group     := `is_group_hom
| _ := name.anonymous

meta def map_types : name → (list name)
| `has_mul   := [`is_mul_hom.map_mul]
| `monoid    := [`is_monoid_hom.map_one, `is_monoid_hom.map_pow]
| `group     := [`is_group_hom.map_inv]
| _ := []

meta def types : list name :=
[`has_mul, `monoid, `group]

-- meta def hom : tactic unit :=
-- do mul_homs    ← mul_homs,
--     -- trace mul_homs,
--    let mul_tactics := mul_homs.map map_mul,
--    monoid_homs ← monoid_homs,
--     -- trace monoid_homs,
--    let one_tactics := monoid_homs.map map_one,
--    let pow_tactics := monoid_homs.map map_pow,
--    group_homs ← group_homs,
--     -- trace group_homs,
--    let inv_tactics := group_homs.map map_inv,
--    chain $ mul_tactics ++ one_tactics ++ pow_tactics ++ inv_tactics,
--    try reflexivity

meta def tactics_of_homs (p : name × tactic (list expr)) : tactic (list (list (tactic unit))) :=
do let map_lemmas := map_types p.1,
   fs ← p.2,
   return $ map_lemmas.map $ λ l, fs.map $ λ f, rw_map l f

meta def hom' : tactic unit :=
do let homs := types.map $ λ t, (t, lookup_homs (instance_type t)),
   tactics ← homs.mmap tactics_of_homs,
   let flat_tactics := list.join $ list.join tactics,
   chain flat_tactics,
   try reflexivity

example (X Y : Type) [ring X] [ring Y] (f : X → Y) [is_monoid_hom f] (n : ℕ)
  (x y : X) : f (x^n * y) = (f x)^n * f y :=
begin
  hom',
end
