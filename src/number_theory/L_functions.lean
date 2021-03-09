import measure_theory.integration
import algebra.group.hom
import ring_theory.int.basic
import data.padics.padic_integers
import set_theory.zfc
import topology.category.Profinite
import topology.locally_constant.algebra
import topology.algebra.continuous_functions

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

instance compact : compact_space (units ℤ_[p]) := sorry

instance t2 : t2_space (units ℤ_[p]) := sorry

instance td : totally_disconnected_space (units ℤ_[p]) := sorry

--instance cat : (units ℤ_[p]) ∈ category_theory.Cat.objects Profinite :=

instance topo' : topological_space (units A) := sorry

/-- A-valued points of weight space -/ --shouldn't this be a category theory statement?
def weight_space : group ({ χ : mul_hom (units ℤ_[p]) (units A) // continuous χ }) := sorry

variables (X : Profinite)

def clopen_sets := {s : set X // is_clopen s}

instance union : semilattice_inf_bot (clopen_sets X) := sorry

instance has_union' : has_union (clopen_sets X) :=
begin
constructor,
sorry
end

open_locale big_operators

--variables {R : Type*} [ring R] [topological_space R]
--variables {R : Type*} [ring R] [topological_space R] [topological_ring R]
structure  distribution {R : Type*} [add_monoid R] :=
(phi : clopen_sets X → R)
(count_add ⦃f : ℕ → clopen_sets X⦄ :
  (∀ i j, pairwise (disjoint on f) →
  phi((f i) ∪ (f j)) = phi (f i) + phi (f j)))

instance semi {R : Type*} [semiring R] : semimodule R (locally_constant X R) := sorry

structure distribution' {R : Type*} [semiring R] [topological_space R] :=
(phi : (locally_constant X R) →ₗ[R] R)

variables {R : Type*} [ring R] {Γ₀   : Type*}  [linear_ordered_comm_group_with_zero Γ₀] (v : valuation R Γ₀)

def measures := {φ : distribution X // ∀ S : clopen_sets X, ∃ K : Γ₀, v (φ.phi S) ≤ K }

def measures' [topological_space R] := {φ : @distribution' X R _ _ // ∀ f : (locally_constant X R), ∃ K : Γ₀, v (φ.phi f) ≤ K }

instance uniform [topological_space R] : uniform_space C(X, R) := sorry

instance completeness [topological_space R] : complete_space C(X, R) := sorry

--topo ring assumption not really needed
def inclusion [topological_space R] [topological_ring R] : locally_constant X R → C(X,R) := sorry

lemma sub [topological_space R] [topological_ring R] : function.injective (@inclusion X R _ _ _) := sorry

instance topo_space :  topological_space (locally_constant ↥X R) := sorry

noncomputable def integral [topological_space R] [topological_ring R] (φ : measures' X v) : C(X, R) →ₗ[R] R :=
begin
  have f : @dense (C(X,R)) _ (set.range (inclusion X)),
  sorry,
  split,
  swap 3,
  {  apply dense_inducing.extend _ (φ.1).phi,
    sorry,
    sorry,
    sorry, },
  sorry, sorry,
end

lemma cont [topological_space R] [topological_ring R] (φ : measures' X v) : continuous (integral X v φ) := sorry

/-structure dir_sys ( α : Type* ) :=
(h : ℕ → finset α )
(sys : ∀ (i j : ℕ) (hji : j ≤ i), (h i : set α) → (h j : set α))
(hsys : ∀ (i j : ℕ) (hji : j ≤ i), function.surjective (sys i j hji) )
(maps : ∀ i j k (h1 : k ≤ j) (h2 : j ≤ i), sys j k h1 ∘ sys i j h2  = sys i k (trans h1 h2) )

variables {G : Type*} [comm_group G] {α : Type*} [ϕ : dir_sys α]

open_locale big_operators
--set_option trace.class_instances
structure distribution :=
( φ : ↑(ϕ.h) → G )
(sum : ∀ (i j : ℕ) (hi : j ≤ i) (x : ϕ.h j), φ j x = tsum (λ (y : (ϕ.lam i j hi)⁻¹ x), φ i y) ) -/

structure system {X : Type*} [set X] :=
( h : ℕ → finset X )
( projlim : X = Prop ) --inverse limit
