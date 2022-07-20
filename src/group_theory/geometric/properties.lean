import group_theory.index
import group_theory.nilpotent

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
⟨begin
  intros G _ H _ e hg,
  unfold is_finite at hg,
  haveI hg := finite G,
  apply finite.of_equiv G,
  exact e.to_equiv,
end⟩ 

def is_trivial (G : Type*) [group G] : Prop := ∀ (g : G), g = 1

def is_finitely_generated (G : Type*) [group G] : Prop := ∃ (S : set G), S.finite ∧ subgroup.closure S = ⊤

/-- A group is virtually P if it contains a subgroup of finite index which has property P. --/
def virtually (property : group_property) (G : Type*) [group G] : Prop :=
∃ (H : subgroup G), H.index > 0 ∧ property H

def is_virtually_nilpotent := virtually group.is_nilpotent

def virtually_p_of_p (p : group_property) [ep : mul_equiv_respects p] (G : Type*) [gg : group G] : 
(p G) → ((virtually p) G) :=
begin
  intro h,
  use (⊤ : subgroup G),
  split,
  { simp, },
  -- can this be cleaned up?
  let k := ep.eq_preserves,
  exact @k G gg _ _ subgroup.top_equiv.symm h,
end

-- none of these seem obvious :(
-- worse, I think they're impossible without something like `mul_equiv_respects` ?
example (G : Type*) [group G] : (virtually is_finite) G → is_finite G := begin
  rintros ⟨H,ind,prop⟩,
  let fintype_quo := subgroup.fintype_of_index_ne_zero (ne_of_gt ind),
  sorry,
end

example (G : Type*) [group G] : is_trivial G → is_finite G := sorry

example (G : Type*) [group G] : (virtually is_trivial) G ↔ is_finite G := sorry

example (G : Type*) [group G] : (virtually is_finitely_generated) G → is_finitely_generated G := sorry -- Reidemeister-Schreier theorem

/-- A group `G` is residually P if every non-identity element of `G`
can be detected by a homomorphism to a group satisfying P. --/
def residually (property : group_property) (G : Type*) [group G] : Prop :=
∀ (g : G) (h : g ≠ 1),
∃ (H : Type*) (h : group H),
let one_class := @monoid.to_mul_one_class H (@group.to_monoid H h) in
@property H h ∧
∃ (f : @monoid_hom G H _ one_class),
((@monoid_hom.to_fun G H _ one_class) f) g ≠
(@has_one.one H (@mul_one_class.to_has_one H one_class))

def is_residually_finite := residually is_finite 

def is_residually_nilpotent := residually group.is_nilpotent

/-- A group `G` is locally P if every finitely generated subgroup of `G` is P. --/
def locally (property : group_property) (G : Type*) [group G] : Prop :=
∀ (S : set G), (S.finite → property (subgroup.closure S))

def is_locally_finite := locally is_finite

def is_locally_nilpotent := locally group.is_nilpotent

end geometric_group_theory
