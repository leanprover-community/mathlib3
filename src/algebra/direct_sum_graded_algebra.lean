import algebra.direct_sum_graded
import linear_algebra.direct_sum_module

namespace direct_sum
open_locale direct_sum

variables {ι : Type*} (R : Type*) (A : ι → Type*) [decidable_eq ι]

-- instance gmonoid.to_semiring [add_monoid ι] [m : Π i, add_comm_monoid (A i)] [gmonoid A] :
--   semiring (A 0) := {
--     one := ghas_one.one,
--     mul := λ a b, (zero_add 0).rec (ghas_mul.mul a b),
--     ..m 0
--   }

-- def direct_sum.of_scalar [add_monoid ι] [semiring (A 0)] : A 0 →+* (⨁ i, A i) :=
-- { map_one' := begin
--     simp[direct_sum.of],
--     dsimp,
--   end,
--   map_mul' := sorry,
--   ..direct_sum.of A 0,}

variables [comm_semiring R] [Π i, add_comm_monoid (A i)] [Π i, semimodule R (A i)]
variables [add_monoid ι] [gmonoid A]

-- /-- `finsupp.single 0` as a `ring_hom` -/
-- @[simps] def single_zero_ring_hom [semiring k] [add_monoid G] : k →+* add_monoid_algebra k G :=
-- { map_one' := rfl,
--   map_mul' := λ x y, by rw [single_add_hom, single_mul_single, zero_add],
--   ..dfinsupp.single_add_hom 0}
section

local attribute [instance] ghas_one.to_sigma_has_one
local attribute [instance] ghas_mul.to_sigma_has_mul

class galgebra [gmonoid A] :=
(to_fun : R →+ A 0)
(map_one : to_fun 1 = ghas_one.one)
(map_mul : ∀ r s, (⟨_, to_fun (r * s)⟩ : Σ i, A i) = ⟨_, ghas_mul.mul (to_fun r) (to_fun s)⟩)
(commutes : ∀ r x, (⟨_, to_fun (r)⟩ : Σ i, A i) * x = x * ⟨_, to_fun (r)⟩)

end

instance [gmonoid A] [galgebra R A] : algebra R (⨁ i, A i) :=
{ to_fun := (direct_sum.of A 0).comp galgebra.to_fun,
  map_zero' := add_monoid_hom.map_zero _,
  map_add' := add_monoid_hom.map_add _,
  map_one' := (direct_sum.of A 0).congr_arg galgebra.map_one,
  map_mul' := λ a b, begin
    simp only [add_monoid_hom.comp_apply],
    rw of_mul_of,
    apply dfinsupp.single_eq_of_sigma_eq (galgebra.map_mul a b),
  end,
  commutes' := λ r x, begin
    -- simp only [add_monoid_hom.comp_apply],
    -- unfold has_mul.mul distrib.mul semiring.mul,
    -- rw to_add_monoid_of,
    -- simp_rw to_add_monoid_of,
    -- unfold to_add_monoid,
    -- rw dfinsupp.lift_add_hom_apply,
    -- rw dfinsupp.lift_add_hom_apply,
    -- rw add_monoid_hom.dfinsupp_sum_add_hom_apply,
    -- refine add_monoid_hom.congr_fun _ x,
    -- congr' 1, ext i xi : 2,
    -- simp,
    -- apply dfinsupp.single_eq_of_sigma_eq (galgebra.commutes r ⟨i, xi⟩)
    sorry
  end,
  smul_def' := λ r x, begin
    dsimp [has_scalar.smul],
    unfold has_mul.mul distrib.mul semiring.mul,
    simp,
  end
}
