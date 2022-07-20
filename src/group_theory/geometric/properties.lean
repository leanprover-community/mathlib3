import group_theory.index
import group_theory.nilpotent

namespace geometric_group_theory

/-- A property of a group is a `Prop` depending on a group `G` --/
def group_property := Π (G : Type*) [group G], Prop

/-- A group is virtually P if it contains a subgroup of finite index which has property P. --/
def virtually (property : group_property) (G : Type*) [group G] : Prop :=
∃ (H : subgroup G), H.index > 0 ∧ property H

def is_virtually_nilpotent := virtually group.is_nilpotent

def is_finite (G : Type*) [group G] : Prop := nonempty (fintype G)

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

end geometric_group_theory
