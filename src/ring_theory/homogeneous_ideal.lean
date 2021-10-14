import algebra.direct_sum.ring
import ring_theory.ideal.basic
import ring_theory.ideal.operations

noncomputable theory

open_locale direct_sum classical
open set direct_sum

variables {ι : Type*} [add_comm_monoid ι] (A : ι → Type*) [Π i, comm_ring (A i)] [gcomm_semiring A]

def is_homogeneous_element (x : ⨁ i, A i) := ∃ i (y : A i), x = of A i y

def is_homogeneous_ideal (I : ideal (⨁ i, A i)) :=
  I.carrier = ⋃ (i : ι), I.carrier ∩ (set.image (of A i) univ)


def is_homogeneous_ideal' (I : ideal (⨁ i, A i)) :=
  ∃ S, (∀ s ∈ S, is_homogeneous_element A s) ∧ I = ideal.span S

-- def is_homogeneous_ideal_iff_eq_span_homogeneous_elements
--   (I : ideal (⨁ i, A i)) : is_homogeneous_ideal A I ↔ is_homogeneous_ideal' A I :=
-- ⟨λ HI, begin
--   sorry
-- end, λ ⟨S, ⟨homogeneous_S, I_eq_span⟩⟩, begin
--   rw I_eq_span, ext, sorry
-- end⟩

lemma prod_hom (I J : ideal (⨁ i, A i)) (HI : is_homogeneous_ideal' A I) (HJ : is_homogeneous_ideal' A J) :
  is_homogeneous_ideal' A (I * J) :=
begin
  rcases HI with ⟨SI, ⟨SI_hom, I_eq_span_SI⟩⟩,
  rcases HJ with ⟨SJ, ⟨SJ_hom, J_eq_span_SJ⟩⟩,

  use ⋃ (s₁ ∈ SI) (s₂ ∈ SJ), {s₁ * s₂}, split,
  { intros x Hx, simp only [exists_prop, mem_Union, mem_singleton_iff] at Hx ⊢,
    rcases Hx with ⟨s₁, hs₁, s₂, hs₂, hx⟩,
    specialize SI_hom s₁ hs₁,
    specialize SJ_hom s₂ hs₂,
    rcases SI_hom with ⟨i, y₁, hy₁⟩,
    rcases SJ_hom with ⟨j, y₂, hy₂⟩,
    use (i+j), use (graded_monoid.ghas_mul.mul y₁ y₂), rw [hx, hy₁, hy₂, ←mul_hom_of_of], refl, },
  { ext, split,
    { intro hx, rw [←ideal.span_mul_span, ←I_eq_span_SI, ←J_eq_span_SJ], exact hx, },
    { intro hx, rw [←ideal.span_mul_span, ←I_eq_span_SI, ←J_eq_span_SJ] at hx, exact hx, } }
end
