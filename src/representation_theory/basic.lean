import algebra.module.basic
import data.equiv.module
import algebra.module.linear_map
import algebra.monoid_algebra.basic
import linear_algebra.trace

open monoid_algebra

namespace representation

section
variables (k G V : Type*) [comm_semiring k] [monoid G] [add_comm_monoid V]
variables [module k V] [distrib_mul_action G V] [smul_comm_class G k V]

/--
A k-linear representation of G on V can be thought of as
a multiplicative map from G into the k-linear endomorphisms of V.
-/
def as_monoid_hom : G →* (V →ₗ[k] V) :=
{ to_fun := distrib_mul_action.to_linear_map k V,
  map_one' := by { ext, simp, },
  map_mul' := λ g g', by { ext, simp [mul_smul], }, }

@[simp]
lemma as_monoid_hom_apply_apply (g : G) (v : V) :
  (as_monoid_hom k G V) g v = g • v := rfl

/--
A k-linear representation of G on V can be thought of as
an algebra map from `monoid_algebra k G` into the k-linear endomorphisms of V.
-/
noncomputable def as_algebra_hom : monoid_algebra k G →ₐ[k] (V →ₗ[k] V) :=
  (lift k G _) (as_monoid_hom k G V)

lemma as_algebra_hom_def :
  as_algebra_hom k G V = (lift k G _) (as_monoid_hom k G V) := rfl

@[simp]
lemma as_algebra_hom_of (g : G):
  (as_algebra_hom k G V (of k G g)) = (as_monoid_hom k G V) g :=
by simp [as_algebra_hom_def]

@[simp]
lemma as_algebra_hom_single (g : G):
  (as_algebra_hom k G V (finsupp.single g 1)) = (as_monoid_hom k G V) g :=
by simp [as_algebra_hom_def]

/--
A k-linear representation of G on V can be thought of as
a module over `monoid_algebra k G`.
-/
noncomputable instance as_module : module (monoid_algebra k G) V :=
  module.comp_hom V (as_algebra_hom k G V).to_ring_hom

lemma as_module_apply (a : monoid_algebra k G) (v : V):
  a • v = (as_algebra_hom k G V a) v := rfl

@[simp]
lemma smul_of (g : G) (v : V) : (of k G g) • v =  g • v := by simp [as_module_apply]

instance as_module_scalar_tower : is_scalar_tower k (monoid_algebra k G) V :=
{ smul_assoc := λ r a v, by simp [as_module_apply] }

instance as_module_smul_comm : smul_comm_class k (monoid_algebra k G) V :=
{ smul_comm := λ r a v, by simp [as_module_apply] }

end

section group
variables (k G V : Type*) [comm_semiring k] [group G] [add_comm_monoid V]
variables [module k V] [distrib_mul_action G V] [smul_comm_class G k V]

def as_group_hom : G →* units (V →ₗ[k] V) := monoid_hom.to_hom_units (as_monoid_hom k G V)

end group

end representation

section
variables {k G V : Type*} [comm_semiring k] [monoid G] [add_comm_monoid V] [module k V]
variables (ρ : G →* (V →ₗ[k] V))

/--
A multiplicative map from `G` into the k-linear endomorphisms of V give rise
to a k-linear representation of G
-/
@[derive [add_comm_monoid, module k]] def rep_space (ρ : G →* (V →ₗ[k] V)) : Type* := V

instance distrib_mul_action_of_monoid_hom : distrib_mul_action G (rep_space ρ) :=
{ smul := λ g v, ρ g v,
  one_smul := λ v, by simp,
  mul_smul := λ g h v, by simp,
  smul_add := λ g v w, by simp,
  smul_zero := λ g, by simp }

@[simp]
lemma distrib_mul_action_of_monoid_hom_apply (g : G) (v : rep_space ρ) :
  g • v = ρ g v := rfl

instance smul_comm_class_of_monoid_hom : smul_comm_class G k (rep_space ρ) :=
{ smul_comm := λ r g v, by simp }

/-- `as_monoid_hom` is left inverse to `rep_space` -/
@[simp]
lemma as_monoid_hom_of_rep_space : representation.as_monoid_hom k G (rep_space ρ) = ρ :=
  by {ext v, simp}
end

section
variables (k G V : Type*) [comm_semiring k] [monoid G] [add_comm_monoid V]
variables [module k V] [distrib_mul_action G V] [smul_comm_class G k V]

/-- `as_monoid_hom` is right inverse to `rep_space` -/
@[simp]
lemma rep_space_of_as_monoid_hom (g : G) (v : V) :
 (g • v : rep_space (representation.as_monoid_hom k G V)) =
 g • (v : rep_space (representation.as_monoid_hom k G V)) := rfl

end

section character

open representation

variables (k G V : Type*) [field k] [group G] [add_comm_group V]
variables [module k V] [distrib_mul_action G V] [smul_comm_class G k V]

/--
The character associated to a representation of `G`, which as a map `G → k`
sends each element to the trace of the corresponding linear map
-/
noncomputable def character : G → k :=
  λ g, linear_map.trace k V ((as_group_hom k G V) g)

@[simp]
lemma char_apply (g : G) :
  (character k G V) g = linear_map.trace k V (as_group_hom k G V g) := rfl

/-- The evaluation of the character at the identity is the dimension of the representation -/
theorem char_one : character k G V 1 = finite_dimensional.finrank k V := by simp

/-- The character of a representation is constant on conjugacy classes -/
theorem char_conj (g : G) (h : G) : (character k G V) (h * g * h⁻¹) = (character k G V) g := by simp

end character
