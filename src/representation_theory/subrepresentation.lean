import representation_theory.basic
import ring_theory.simple_module

universes u v w

section subrepresentation
variables (k : Type u) (G : Type v) (M : Type w)
variables [semiring k] [monoid G] [add_comm_monoid M]
variables [module k M] [distrib_mul_action G M]

structure subrepresentation [representation k G M] extends submodule k M :=
(group_smul_mem' : ∀ (c : G) {x : M}, x ∈ carrier → c • x ∈ carrier)

end subrepresentation

namespace subrepresentation

section definitions
variables {k : Type u} {G : Type v} {M : Type w}
variables [semiring k] [monoid G] [add_comm_monoid M]
variables [module k M] [distrib_mul_action G M]

/-- Reinterpret a subrepresentation as a `FG`-submodule. -/
noncomputable def to_monoid_algebra_submodule [representation k G M] (ρ : subrepresentation k G M) :
  submodule (monoid_algebra k G) M :=
{ carrier := ρ.carrier,
  zero_mem' := ρ.zero_mem',
  add_mem' := ρ.add_mem',
  smul_mem' := λ x m hm,
  begin
    simp,
    sorry
  end }

/-- Reinterpret a `FG`-submodule as a subrepresentation. -/
def of_monoid_algebra_submodule [representation k G M] (N : submodule (monoid_algebra k G) M) :
  subrepresentation k G M :=
{ carrier := N.carrier,
  zero_mem' := N.zero_mem,
  add_mem' := N.add_mem',
  smul_mem' := λ r m hm,
  by { sorry },
  group_smul_mem' := λ g m hm,
  begin
    simp only at *,
    sorry
  end }

instance [representation k G M] : set_like (subrepresentation k G M) M :=
{ coe := λ p, p.carrier,
  coe_injective' := λ p q h, by { cases p; cases q; simp only at *, apply set_like.ext', exact h } }

@[simp] lemma mk_coe [representation k G M]
  (S : set M) (h₁ h₂ h₃)
  (h₄ : ∀ (c : G) {x : M}, x ∈ S → c • x ∈ S) :
  ((⟨⟨S, h₁, h₂, h₃⟩, h₄⟩ : subrepresentation k G M) : set M) = S := rfl

@[ext] theorem ext
  [representation k G M] {p q : subrepresentation k G M} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
set_like.ext h

end definitions

section lattice
variables {k : Type u} {G : Type v} {M : Type w}
variables [semiring k] [monoid G] [add_comm_monoid M]
variables [module k M] [distrib_mul_action G M]



end lattice

section reducible
variables (k : Type u) (G : Type v) (M N: Type w)
variables [ring k] [monoid G] [add_comm_group M]
variables [module k M] [distrib_mul_action G M]

abbreviation is_irreducible [representation k G M] := is_simple_module (monoid_algebra k G) M

end reducible

end subrepresentation

section rep_hom
variables (k : Type u) (G : Type v) (M N: Type w)
variables [semiring k] [monoid G] [add_comm_monoid M] [add_comm_monoid N]
variables [module k M] [distrib_mul_action G M] [module k N] [distrib_mul_action G N]

structure rep_hom [representation k G M] [representation k G N] extends linear_map k M N :=
(commutes' : ∀ (g : G) (m : M), to_fun (g • m) = g • to_fun m)

infixr ` →ᵣ `:25 := rep_hom _
notation M ` →ᵣ[`:25 k `, ` G `] ` N := rep_hom k G M N

end rep_hom

namespace rep_hom


end rep_hom
