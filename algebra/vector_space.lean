import algebra.ring
import algebra.module

universes u v

class vector_space (α : inout Type u) (β : Type v) [field α] extends module α β

instance field.to_vector_space {K : Type} [field K] :
vector_space K K := ⟨ring.to_module⟩

class subspace (K : Type) (V : Type) [field K] [vector_space K V] (p : set V) :=
(add : ∀ u v, u ∈ p → v ∈ p → u + v ∈ p)
(zero : (0:V) ∈ p)
(neg : ∀ v, v ∈ p → -v ∈ p)
(smul : ∀ c v, v ∈ p → c • v ∈ p)

namespace subspace

variables (K : Type) {V : Type} [field K] [vector_space K V]
variables {p : set V} [subspace K V p]

instance : submodule K V p :=
{ add  := add K,
  zero := zero K p,
  neg  := neg K,
  smul := smul }

instance : vector_space K {x // x ∈ p} := {submodule.module K V p with}

end subspace


namespace linear_map

variables {K V W : Type} [field K] [vector_space K V] [vector_space K W]

namespace ker

instance {A : linear_map K V W} : subspace K V A.ker :=
{ linear_map.ker.submodule K A with }

end ker


namespace im

instance {A : linear_map K V W} : subspace K W A.im :=
{ linear_map.im.submodule K A with }

end im


instance : vector_space K (linear_map K V W) :=
{ linear_map.module K V W with }

end linear_map


namespace vector_space

variables (K V : Type) [field K] [vector_space K V]

def dual := module.dual K V
def general_linear_group := module.general_linear_group K V

end vector_space
