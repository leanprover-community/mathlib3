import order.zorn

namespace hypertope

open zorn

universes u v

/-- An incidence system is a set of elements, a set of types,
and a symmetric reflexive incidence relation
which does not relate distinct elements of the same type -/
structure incidence_system (X : Type u) (I : Type v) :=
(type : X → I)
(r : X → X → Prop)
(r_is_symm : is_symm X r)
(r_is_refl : is_refl X r)
(eq_of_r_of_type_eq : ∀ ⦃x y⦄, r x y → type x = type y → x = y)
instance {X I} (H : incidence_system X I) : is_symm X H.r :=
H.r_is_symm

instance {X I} (H : incidence_system X I) : is_refl X H.r :=
H.r_is_refl

def flag {X I} (H : incidence_system X I) (f : set X) :=
chain H.r f ∧ H.type '' f = set.univ

def residue_type {X I} (H : incidence_system X I) (c : set X) :=
{x : X // x ∉ c ∧ ∀ e, e ∈ c → H.r x e}

def residue {X I} (H : incidence_system X I) (c : set X) :
  incidence_system (residue_type H c) (set.compl (H.type '' c)) :=
{ type := λ x, ⟨H.type x.1, λ ⟨y, hy, h⟩, x.2.1 (by rwa H.eq_of_r_of_type_eq (x.2.2 y hy) h.symm)⟩,
  r := subrel H.r _,
  r_is_symm := ⟨λ x y h, by { apply H.r_is_symm.symm, exact h }⟩,
  r_is_refl := ⟨λ x, by apply H.r_is_refl.refl⟩,
  eq_of_r_of_type_eq := λ x y hr ht, subtype.ext_val (H.eq_of_r_of_type_eq hr (subtype.mk.inj ht)) }

structure incidence_geometry (X : Type u) (I : Type v) extends incidence_system X I :=
(chain_subset_flag : ∀ c, chain r c → ∃ f, c ⊆ f ∧ chain r f ∧ type '' f = set.univ)

def thin {X I} (H : incidence_geometry X I) 
(c : set X) (hc : chain H.r c) (hhc : ∃ i, (∀ j, (∃ x, x ∈ c ∧ H.type x = j) ↔ j ≠ i)) :=
∃ (a b : residue_type H.1 c), (a ≠ b) ∧ ∀ (z : residue_type H.1 c), (z.1 = a.1 ∨ z.1 = b.1)

def connected {X I} (H : incidence_system X I) : Prop := 
∀ (fm fn : set X), (flag H fm) → (flag H fn) → 
∃ (m n : ℤ) (path : ℤ → set X),
(path m = fm ∧ path n = fn ∧ ∀ (k : ℤ),
(flag H (path k) ∧ ∀ (w x y z : X), (
(w ∈ path k ∧ y ∈ path (k+1) ∧ w ≠ y ∧ H.type w = H.type y) ∧
(x ∈ path k ∧ z ∈ path (k+1) ∧ x ≠ z ∧ H.type x = H.type z)
)→ w = y))

/- How to refer to incidence system/geometry? -/

structure hypertope (X : Type u) (I : Type v) extends incidence_geometry X I :=
(thin : ∀ (c : set X) (hc : chain r c) (hhc : ∃ i, (∀ j, (∃ x, x ∈ c ∧ type x = j) ↔ j ≠ i)),
∃ (a b : residue_type to_incidence_system c), (a ≠ b) ∧ ∀ (z : residue_type to_incidence_system c), (z.1 = a.1 ∨ z.1 = b.1)) 
(residually_connected : ∀ (c : set X) (hc : chain r c), connected (residue to_incidence_system c))

end hypertope
