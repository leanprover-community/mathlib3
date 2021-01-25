import algebra.homology.chain_complex
import algebra.category.Module.basic
import linear_algebra.tensor_product
import linear_algebra.direct_sum_module

universes u
variables (R : Type u) [comm_ring R]

def smul_cx_X : ℤ → Module.{u u} R
| 0 := Module.of R R
| 1 := Module.of R R
| (int.of_nat n) := Module.of R punit
| -[1+ n] := Module.of R punit

variables {R}

def smul_cx_d (x : R) : Π i : ℤ, smul_cx_X R i ⟶ smul_cx_X R (i + 1)
| 0 := linear_map.lsmul R R x
| (int.of_nat n) := 0
| -[1+ n] := 0

theorem smul_cx_d_squared (x : R) (i : ℤ) :
  smul_cx_d x i ≫ smul_cx_d x (i + 1) = 0 :=
int.rec_on i (λ j, linear_map.zero_comp _) (λ j, linear_map.comp_zero _)

variables (R)

def smul_cx (x : R) : cochain_complex.{u u+1} (Module.{u u} R) :=
{ X := smul_cx_X R,
  d := smul_cx_d x,
  d_squared' := by ext1 i; exact smul_cx_d_squared x i }

def hom_aux (x : fin 2 → R) :=
@direct_sum.to_module R _ ({ i : ℤ × ℤ // i.1 + i.2 = 0}) _
  (λ i, tensor_product R ((smul_cx R (x 1)).X i.1.1) ((smul_cx R (x 0)).X i.1.2)) _ _
     (Module.of R R) _ _ $ λ i,
    subtype.cases_on i $ λ i', prod.cases_on i' $ λ i j hij,
    int.cases_on i (λ a, nat.rec_on a (int.cases_on j
      (λ b, nat.rec_on b ((tensor_product.rid R R).to_linear_map)
      (λ c, 0)) (λ b, 0)) (λ b, 0)) (λ a, 0)


