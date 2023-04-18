import algebraic_geometry.Scheme
import ring_theory.tensor_product
import data.polynomial.laurent

noncomputable theory

open algebraic_geometry
open_locale tensor_product

local notation R`[T;T⁻¹]`:9000 := laurent_polynomial R
variables (R : Type*) [comm_ring R] (x : (R[T;T⁻¹] ⊗[R] R[T;T⁻¹])ˣ)

def comultiplication :
  R[T;T⁻¹] →+* R[T;T⁻¹] ⊗[R] R[T;T⁻¹] :=
@is_localization.lift (polynomial R) _ _ _ _ _ _ _ laurent_polynomial.is_localization
(polynomial.eval₂_ring_hom (algebra_map R (R[T;T⁻¹] ⊗[R] R[T;T⁻¹])) x) sorry
#exit
#check Scheme.Spec_map (CommRing.of_hom $ comultiplication R x)
