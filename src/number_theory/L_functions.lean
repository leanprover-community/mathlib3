import measure_theory.integration
import algebra.group.hom
import ring_theory.int.basic
import data.padics.padic_integers
import set_theory.zfc

variables {A : Type*} [integral_domain A] [algebra ℚ A]

def dirichlet_char_space (f : ℤ) : monoid { χ : mul_hom ℤ ℂ // ∀ a : ℤ, gcd a f ≠ 1 ↔ χ a = 0 } :=
{
  mul := begin
        rintros a b, sorry,
        end,
  one := begin sorry end,
  one_mul := begin sorry end,
  mul_one := begin sorry end,
  mul_assoc := begin sorry end,
}

instance dir_char (f : ℤ) : group { χ : mul_hom ℤ ℂ // ∀ a : ℤ, gcd a f ≠ 1 ↔ χ a = 0 } := sorry

variables (p : ℕ) [fact p.prime]

instance topo : topological_space (units ℤ_[p]) := sorry

instance topo' : topological_space (units A) := sorry

/-- A-valued points of weight space -/ --shouldn't this be a category theory statement?
def weight_space : group ({ χ : mul_hom (units ℤ_[p]) (units A) // continuous χ }) := sorry

structure dir_sys ( α : Type* ) :=
(h : ℕ → finset α )
(sys : ∀ (i j : ℕ), (hji : j ≤ i), (h i : set α) → (h j : set α))
(hsys : function.surjective (sys i j hji) )
(maps : ∀ i j k (h1 : k ≤ j) (h2 : j ≤ i), sys j k h1 ∘ sys i j h2  = sys i k (trans h1 h2) )

variables {G : Type*} [comm_group G] {α : Type*} [ϕ : dir_sys α]

open_locale big_operators
--set_option trace.class_instances
structure distribution :=
( φ : ↑(ϕ.h) → G )
(sum : ∀ (i j : ℕ) (hi : j ≤ i) (x : ϕ.h j), φ j x = tsum (λ (y : (ϕ.lam i j hi)⁻¹ x), φ i y) )

structure system {X : Type*} [set X] :=
( h : ℕ → finset X )
( projlim : X = Prop ) --inverse limit
