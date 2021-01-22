import linear_algebra.finite_dimensional

variables (K : Type*) [field K] (V : Type*) [add_comm_group V] [vector_space K V]

open vector_space submodule finite_dimensional

def proj := { H : submodule K V // findim K H = 1 }

namespace proj

variables {K V}

instance : has_coe (proj K V) (submodule K V) := ⟨subtype.val⟩
instance : has_mem V (proj K V) := ⟨λ v H, v ∈ (H : submodule K V)⟩

@[simp]
def mk (v : V) (hv : v ≠ 0) : proj K V := ⟨K ∙ v, findim_span_singleton hv⟩

#check submodule.span
lemma mk_eq_iff {v w : V} {hv : v ≠ 0} {hw : w ≠ 0} :
  (mk v hv : proj K V) = mk w hw ↔ ∃ a : K, a • v = w :=
begin
  sorry,
end

end proj
