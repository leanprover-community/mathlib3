import algebra.category.Module.algebra
import algebra.monoid_algebra.basic
noncomputable theory
namespace ITP

/-- Let `k` be a commutative ring and `G` a group. Let `V` be an additive commutative group, which
is also a `k`-module and a `k[G]`-module.
Assume the `k`-action is compatible with the `k[G]`-action. -/
variables (k G V : Type*) [comm_ring k] [group G] [add_comm_group V]
  [module k V] [module (monoid_algebra k G) V] [H : is_scalar_tower k (monoid_algebra k G) V]

/-- We "bundle" `V` with its instances, creating a term of `k[G]-Mod`. -/
def bundled : Module (monoid_algebra k G) :=
{ carrier := V,
  is_add_comm_group := by assumption,
  is_module := by assumption }

/-- The natural `k`-module instance on a `k[G]`-module. -/
instance : module k (bundled k G V) :=
restrict_scalars.module k (monoid_algebra k G) _

include H

/-- Now we try and show the above `k`-module instance on bundled `V` agrees with
the original one: -/
example (r : k) (x : bundled k G V) :
  r • x = ((•) : k → V → V) r x := -- `rfl' fails! They aren't definitionally equal.
begin
-- but the statement is still true!
  rw restrict_scalars.smul_def,
  dunfold algebra_map algebra.to_ring_hom,
  dsimp,
  rw [←finsupp.smul_single_one, @smul_assoc _ _ _ _ _ _ H, ←monoid_algebra.one_def,
    one_smul],
  refl,
end

/- The file `algebra.category.Module.algebra` warns of this issue. -/

end ITP
