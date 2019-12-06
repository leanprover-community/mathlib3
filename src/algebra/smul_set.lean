import algebra.pointwise

namespace set

variables {α : Type*} {β : Type*}

def pointwise_smul [has_scalar α β] : has_scalar (set α) (set β) :=
  ⟨λ s t, { x | ∃ a ∈ s, ∃ y ∈ t, x  = a • y }⟩

def smul_set [has_scalar α β] : has_scalar α (set β) :=
  ⟨λ a s, (λ y, a • y) '' s⟩

end set
