import group_theory.index
import group_theory.nilpotent

/-!
# Group properties
-/

namespace geometric_group_theory

/-- A property of a group is a `Prop` depending on a group `G`. --/
def group_property := Π (G : Type*) [group G], Prop

/-- In order to transport properties of groups across equivalences, a
`group_property` should include data for facilitating that transport. --/
class mul_equiv_respects (property : group_property) :=
(eq_preserves: Π {G : Type*} [group G], Π {H : Type*} [group H],
(G ≃* H) → (property G) → (property H))

def is_finite (G : Type*) [group G] : Prop := finite G

instance : mul_equiv_respects is_finite :=
⟨λ G _ H _ e hg, begin
  unfold is_finite at hg,
  haveI hg := finite G,
  exact finite.of_equiv G e.to_equiv,
end⟩

def is_trivial (G : Type*) [group G] : Prop := ∀ g : G, g = 1

def is_finitely_generated (G : Type*) [group G] : Prop :=
∃ S : finset G, subgroup.closure (S : set G) = ⊤

/-- A group is virtually P if it contains a subgroup of finite index which has property P. --/
def virtually (property : group_property) (G : Type*) [group G] : Prop :=
∃ (H : subgroup G), H.index ≠ 0 ∧ property H

def is_virtually_nilpotent := virtually group.is_nilpotent

def virtually_p_of_p (p : group_property) [ep : mul_equiv_respects p] (G : Type*) [group G]
  (h : p G) : virtually p G :=
  ⟨⊤, by simp, mul_equiv_respects.eq_preserves subgroup.top_equiv.symm h⟩

-- none of these seem obvious :(
-- worse, I think they're impossible without something like `mul_equiv_respects` ?
example (G : Type*) [group G] : virtually is_finite G → is_finite G :=
begin
  rintro ⟨H, ind, prop⟩,
  letI fintype_quo := subgroup.fintype_of_index_ne_zero ind,
  sorry,
end

example (G : Type*) [group G] : is_trivial G → is_finite G := sorry

example (G : Type*) [group G] : virtually is_trivial G ↔ is_finite G := sorry

example (G : Type*) [group G] : virtually is_finitely_generated G ↔ is_finitely_generated G :=
sorry -- Reidemeister-Schreier theorem

/-- A group `G` is residually P if every non-identity element of `G`
can be detected by a homomorphism to a group satisfying P. --/
def residually (property : group_property) (G : Type*) [group G] : Prop :=
∀ (g : G) (h : g ≠ 1), ∃ (H : Type*) [group H], by exactI property H ∧ ∃ f : G →* H, f g ≠ 1

def is_residually_finite := residually is_finite

def is_residually_nilpotent := residually group.is_nilpotent

/-- A group `G` is locally P if every finitely generated subgroup of `G` is P. --/
def locally (property : group_property) (G : Type*) [group G] : Prop :=
∀ S : set G, S.finite → property (subgroup.closure S)

def is_locally_finite := locally is_finite

def is_locally_nilpotent := locally group.is_nilpotent

end geometric_group_theory
