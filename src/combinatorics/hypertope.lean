import order.zorn
import combinatorics.simple_graph.basic

namespace hypertope

open zorn
open simple_graph

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

def adj_flags {X I} (H : incidence_system X I) (f g : set X) : Prop :=
(flag H f) ∧ (flag H g) ∧
∀ (w x y z : X), (
(w ∈ f ∧ y ∈ g ∧ w ≠ y ∧ H.type w = H.type y) ∧
(x ∈ f ∧ z ∈ g ∧ x ≠ z ∧ H.type x = H.type z))
→ w = x

def connected {X I} (H : incidence_system X I) : Prop := 
∀ (fm fn : set X) (flag_m : flag H fm) (flag_n : flag H fn),
∃ (m n : ℤ) (path : ℤ → set X),
(path m = fm ∧ path n = fn ∧
∀ (k : ℤ), adj_flags H (path k) (path (k+1)))

structure hypertope (X : Type u) (I : Type v) extends incidence_geometry X I :=
(thin : ∀ (c : set X) (hc : chain r c) (hhc : ∃ i, (∀ j, (∃ x, x ∈ c ∧ type x = j) ↔ j ≠ i)),
∃ (a b : residue_type to_incidence_system c), (a ≠ b) ∧ ∀ (z : residue_type to_incidence_system c), (z.1 = a.1 ∨ z.1 = b.1)) 
(residually_connected : ∀ (c : set X) (hc : chain r c), connected (residue to_incidence_system c))

def adj_graph {X I} (H : incidence_system X I) :=
from_rel (adj_flags H)

theorem choice_of_ne_sets {X} {f g : set X} (ne_fg : f ≠ g) 
: ∃ (x : X), (f x ≠ g x) :=
begin
by_contradiction,
have k := forall_not_of_not_exists h,
apply ne_fg,
apply funext,
intro x,
have x_in_symm_diff := k x,
sorry,
end

def ne_adj_flags_type {X I} (H : incidence_system X I) 
(f g : set X) (adj_fg : adj_flags H f g) (ne_fg : f ≠ g) : I :=
begin
sorry,
end

end hypertope
