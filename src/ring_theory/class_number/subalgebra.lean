import algebra.algebra.subalgebra

section semiring

variables {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]

lemma subalgebra.smul_mk {S : subalgebra R A}
  (a : R) (x : A) (hx : x ∈ S) :
  a • (⟨x, hx⟩ : S) = ⟨a • x, S.smul_mem hx a⟩ :=
by { ext, refl }

@[simp]
lemma subalgebra.mk_eq_zero_iff {S : subalgebra R A}
  (x : A) (hx : x ∈ S) :
  (⟨x, hx⟩ : S) = 0 ↔ x = 0 :=
subtype.ext_iff

end semiring
