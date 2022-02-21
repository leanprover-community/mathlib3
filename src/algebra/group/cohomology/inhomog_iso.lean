import algebra.group.cohomology.std_resn
import algebra.group.cohomology.inhomog
import algebra.group.cohomology.ext
import linear_algebra.tensor_product
universes v u
noncomputable theory

variables (G : Type u) [group G] (M : Type u) [add_comm_group M]
  [distrib_mul_action G M] (n : ℕ)
open_locale tensor_product

namespace group_ring

def to_tensor_aux (x : fin (n + 1) → G) : group_ring G ⊗[ℤ] ((fin n → G) →₀ ℤ) :=
tensor_product.tmul _ (group_ring.of G (x 0))
  (finsupp.single ((x 0)⁻¹ • fin.tail x) 1)

def to_tensor_add_hom : group_ring (fin (n + 1) → G) →+ group_ring G
  ⊗[ℤ] ((fin n → G) →₀ ℤ) :=
{ to_fun := finsupp.lift_add_hom (λ x,
  { to_fun := zmultiples_hom _ (to_tensor_aux G n x),
    map_zero' := by simp only [zmultiples_hom_apply, zero_smul],
    map_add' := λ f g, by { dsimp, rw add_smul } }),
  map_zero' := by { simp only [finsupp.lift_add_hom_apply, finsupp.sum_zero_index], },
  map_add' := λ f g, by {simp only [finsupp.sum_add_index', finsupp.lift_add_hom_apply]} }

def to_tensor : group_ring (fin (n + 1) → G) →ₗ[group_ring G] group_ring G
  ⊗[ℤ] ((fin n → G) →₀ ℤ) :=
group_ring.mk_linear (to_tensor_add_hom G n) $ λ g x,
begin
  refine x.induction_on _ _ _,
  { intro y,
    unfold to_tensor_add_hom to_tensor_aux,
    dsimp,
    simp only [zmultiples_hom_apply, zero_smul, one_zsmul, finsupp.sum_single_index,
      group_ring.single_smul_single, one_mul],
    dsimp, simp only [mul_inv_rev],
    congr' 1,
    { dsimp, rw monoid_algebra.single_mul_single, rw mul_one},
    { dsimp,
    congr' 1,
    ext, simp only [smul_eq_mul, pi.smul_apply, fin.tail_def],
    assoc_rw inv_mul_cancel_left} },
  { intros y z hy hz,
    simp only [smul_add, add_monoid_hom.map_add, hy, hz] },
  { intros r y hy,
    rw smul_comm,
    rw add_monoid_hom.map_zsmul,
    rw hy,
    rw add_monoid_hom.map_zsmul,
    rw smul_comm,
      }
end

def of_tensor_add_hom :
  group_ring G ⊗[ℤ] ((fin n → G) →₀ ℤ) →+ group_ring (fin (n + 1) → G) :=
(tensor_product.lift (finsupp.lift _ _ _ $ λ g, finsupp.lift _ _ _
  (λ f, group_ring.of (fin (n + 1) → G) (fin.cons g (g • f))))).to_add_monoid_hom

def of_tensor : group_ring G ⊗[ℤ] ((fin n → G) →₀ ℤ)
  →ₗ[group_ring G] group_ring (fin (n + 1) → G) :=
group_ring.mk_linear (of_tensor_add_hom G n) $
λ g x,
begin
  unfold of_tensor_add_hom,
  refine tensor_product.induction_on x _ _ _,
  { simp only [smul_zero, map_zero], },
  { intros y z,
    refine y.induction_on _ _ _,
    { intro w,
      dsimp,
      rw tensor_product.smul_tmul',
      rw smul_eq_mul,
      rw monoid_algebra.single_mul_single,
      rw one_mul,
      rw tensor_product.lift.tmul,
      rw tensor_product.lift.tmul,
      dsimp,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      simp only [one_smul],
      dsimp,
      refine z.induction_linear _ _ _,
      { simp only [finsupp.sum_zero_index, smul_zero] },
      { intros v u hv hu,
        rw finsupp.sum_add_index,
        rw finsupp.sum_add_index,
        simp only [smul_add, hu, hv],
        { intros, simp only [zero_mul, finsupp.smul_single', finsupp.single_zero]},
        { intros, rw add_smul},
        { intros, simp only [zero_mul, finsupp.smul_single', finsupp.single_zero], },
        { intros, rw add_smul}
        },
      { intros,
        rw finsupp.sum_single_index,
        rw finsupp.sum_single_index,
        rw smul_comm,
        rw group_ring.single_smul_single,
        rw one_mul,
        congr,
        ext, simp only [smul_eq_mul, pi.smul_apply],
        sorry,
        sorry,
        sorry },
      sorry,
      sorry },
      sorry,
      sorry
      }, sorry,
end

example : 1+1= 2 := rfl

def equiv_tensor : group_ring (fin (n + 1) → G) ≃ₗ[group_ring G] group_ring G
  ⊗[ℤ] ((fin n → G) →₀ ℤ) :=
{ inv_fun := of_tensor G n,
  left_inv := λ x, by {
    refine x.induction_on _ _ _,
    { intro g,
      unfold to_tensor of_tensor of_tensor_add_hom to_tensor_add_hom,
      dsimp,
      rw finsupp.sum_single_index,
      rw zmultiples_hom_apply,
      rw one_smul,
      unfold to_tensor_aux,
      dsimp,
      rw tensor_product.lift.tmul,
      dsimp,
      rw finsupp.sum_single_index,
      rw one_smul,
      dsimp,
      rw finsupp.sum_single_index,
      sorry,
     all_goals {sorry} },
    sorry, sorry
  },
  right_inv := λ x, by
  { refine tensor_product.induction_on x _ _ _,
    sorry,
    { intros y z,
      unfold to_tensor of_tensor of_tensor_add_hom to_tensor_add_hom,
      dsimp,
      rw tensor_product.lift.tmul, sorry,
      }, sorry, sorry }, ..to_tensor G n }


end group_ring
