import representation_theory.subrepresentation

universes u v w

namespace subrepresentation
variables {k : Type u} {G : Type v} {M : Type w}
variables [semiring k] [monoid G] [add_comm_monoid M]
variables [module k M] [distrib_mul_action G M]
variables [representation k G M] {φ ψ : subrepresentation k G M}

/-- The set `{0}` is the bottom element of the lattice of submodules. -/
instance : has_bot (subrepresentation k G M) :=
⟨{ carrier := {0}, group_smul_mem' := by simp { contextual := tt }, .. (⊥ : submodule k M) }⟩

instance inhabited' : inhabited (subrepresentation k G M) := ⟨⊥⟩

@[simp] lemma bot_coe : ((⊥ : subrepresentation k G M) : set M) = {0} := rfl
@[simp] lemma bot_to_submodule : (⊥ : subrepresentation k G M).to_submodule= ⊥ := rfl

end subrepresentation
