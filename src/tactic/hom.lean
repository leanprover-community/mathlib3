import algebra.ring
import tactic.chain

open tactic

instance is_mul_hom_of_is_monoid_hom {X Y : Type*} [monoid X] [monoid Y]
  (f : X → Y) [I : is_monoid_hom f] : is_mul_hom f :=
{..I}

meta def map_one (f : expr) : tactic unit :=
do to_expr ``(is_monoid_hom.map_one %%f) >>= rewrite_target
meta def map_mul (f : expr) : tactic unit :=
do to_expr ``(is_mul_hom.map_mul %%f) >>= rewrite_target
meta def map_inv (f : expr) : tactic unit :=
do to_expr ``(is_group_hom.map_inv %%f) >>= rewrite_target

meta def lookup_homs (n : expr) : tactic (list expr) :=
do ctx ← local_context,
   ctx.mfilter (λ e, to_expr ``(%%n %%e) >>= mk_instance >> pure true <|> pure false)

meta def mul_homs : tactic (list expr) :=
do mh ← mk_const `is_mul_hom,
   lookup_homs mh
meta def monoid_homs : tactic (list expr) :=
do mh ← mk_const `is_monoid_hom,
   lookup_homs mh
meta def group_homs : tactic (list expr) :=
do mh ← mk_const `is_group_hom,
   lookup_homs mh

#check rewrite

meta def push_monoid_hom (f : expr) : tactic unit :=
do mul ← to_expr ``(is_monoid_hom.map_mul %%f),
   one ← to_expr ``(is_monoid_hom.map_one %%f),
   chain [rewrite_target one, rewrite_target mul],
   skip

meta def instance_type : name → tactic name
| `has_mul       := pure `is_mul_hom
| `semigroup     := pure `is_semigroup_hom
| `monoid        := pure `is_monoid_hom
| _ := fail "The `hom` tactic only supports ..."

meta def hom : tactic unit :=
do mul_homs    ← mul_homs,
    -- trace mul_homs,
   let mul_tactics := mul_homs.map map_mul,
   monoid_homs ← monoid_homs,
    -- trace monoid_homs,
   let monoid_tactics := monoid_homs.map map_one,
   group_homs ← group_homs,
    -- trace group_homs,
   let group_tactics := group_homs.map map_inv,
   chain $ monoid_tactics ++ mul_tactics ++ group_tactics,
   try reflexivity


example (X Y : Type) [ring X] [ring Y] (f : X → Y) [is_monoid_hom f]
  (x y : X) : f (x * y) = f x * f y :=
begin
  hom
end
