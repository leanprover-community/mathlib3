import algebra.algebra.unitization
import algebra.star.star_alg_hom
import analysis.normed_space.operator_norm
import analysis.normed_space.star.basic
import topology.algebra.algebra

.

/-!
# Minimal unitization of a C⋆-algebra

Given a not necessarily unital normed `𝕜`-algebra `A`, one can equip `unitization 𝕜 A` with a
norm such that `unitization 𝕜 A` becomes a unital normed `𝕜`-algebra for which
`‖(1 : unitization 𝕜 A)‖ = 1`. Moreover, if the norms on `A` and `𝕜` satisfy the C⋆-property, so
does the norm on `unitization 𝕜 A`. In addition, if `A` and `𝕜` are complete spaces, so is
`unitization 𝕜 A`. Thus `unitization 𝕜 A` is the smallest unital C⋆-algebra containing `A`.

Note that the topological structure (and uniform structure?) induced by the norm is propositionally,
but not definitionally, equal to the one which could be inherited by viewing `unitization 𝕜 A`
as the type `𝕜 × A`. This should be addressed later by means of forgetful inheritance.

## TODO

* make the topological and metric structures defeq to those of `prod`. This will require
  work similar to that of `pi_Lp`. For now, we just prove the lemma `unitization.tendsto_iff`
* add a `unitization.star_lift` equivalence between the `non_unital_star_alg_hom`s on `A` and
  the `star_alg_hom`s on `unitization 𝕜 A`. This is the universal property of the unitization and
  follows relatively easily from `unitization.lift`.
-/


section unitization

variables {R A : Type*}

/-
the following instances are currently missing from `algebra/algebra/unitization.lean`
a good first PR (which can happen ASAP if you want!) is to PR these to mathlib.
I have left out *both* the hypotheses necessary (i.e., the bits before the colon) as
well as the proofs. You should have a look in the file I mentioned above and see if you
can figure out what should go there. You will get stuck at a certain point if you don't
fill in these instances.

To create a PR, follow these steps:
1. clone a copy of mathlib to your machine. This can be done in a shell with:
  `leanproject get mathlib`, which is essentially equivalent to the following two lines:
  `git clone https://github.com/leanprover-community/mathlib.git`
  `leanproject get-cache`
2. Create a new branch and switch to it:
  `git switch -c my-new-branch` (please don't call it `my-new-branch`)
3. Open the file in VS Code and make the edits you want. Try to follow the guidelines specified at:
  https://leanprover-community.github.io/contribute/naming.html
  https://leanprover-community.github.io/contribute/style.html
4. Commit your changes (I think you know how to do this)
5. Get on Zulip and ask the maintainers for push access to mathlib. After they grant you access,
  accept the invitation on GitHub (this step is a first time only thing, not necessary for future
  PRs)
6. Push your branch to GitHub
7. Go to https://github.com/leanprover-community/mathlib and make the PR (if you do this right
  after you push there shold be a button saying "Compare and PR"). When you do this, try to follow
  the commit convetions: https://github.com/leanprover-community/lean/blob/master/doc/commit_convention.md
-/

instance [comm_ring R] [non_unital_ring A] [module R A] [is_scalar_tower R A A]
  [smul_comm_class R A A] : ring (unitization R A) :=
{ ..unitization.add_comm_group,
  ..unitization.semiring }

instance [comm_ring R] [non_unital_comm_ring A] [module R A] [is_scalar_tower R A A]
  [smul_comm_class R A A] : comm_ring (unitization R A) :=
{ ..unitization.comm_semiring,
  ..unitization.ring }


/- these things are also missing from `algebra/algebra/unitization.lean`. Try to to fill them in
and add them to mathlib. -/
instance {R : Type*} {A : Type*} [has_sub R] [has_sub A] : has_sub (unitization R A) :=
prod.has_sub

@[simp]
theorem unitization.fst_sub {R : Type*} {A : Type*} [has_sub R] [has_sub A]
  (x y : unitization R A) : (x - y).fst = x.fst - y.fst := rfl


end unitization

section prereq1

variables {𝕜 A : Type*} [comm_ring 𝕜] [non_unital_semiring A]
[module 𝕜 A] [is_scalar_tower 𝕜 A A] [smul_comm_class 𝕜 A A]

/-
I think this is actually not necessary for what we do below, but it says that, as functions,
lifting the zero non-unital algebra homomorphism to the base field to the unitization of the
algebra is the same as the projection onto the scalar field coordinate of the unitization.
-/

@[simp]
lemma unitization.lift_zero_eq_fst {𝕜 A : Type*} [comm_ring 𝕜] [non_unital_semiring A]
[module 𝕜 A] [is_scalar_tower 𝕜 A A] [smul_comm_class 𝕜 A A]
: (unitization.lift 0 : unitization 𝕜 A → 𝕜) = unitization.fst :=
begin
  ext x,
  simp only [unitization.lift_apply_apply, algebra.id.map_eq_id, ring_hom.id_apply,
    non_unital_alg_hom.coe_zero, pi.zero_apply, add_zero],
end

end prereq1

section lift
-- this is the lifting property, it should go in `algebra/algebra/unitization.lean` also

variables {S R A :Type*}
  [comm_semiring S] [comm_semiring R] [non_unital_semiring A]
  [module R A] [smul_comm_class R A A] [is_scalar_tower R A A]
  {B : Type*} [semiring B] [algebra S B]
  [algebra S R] [distrib_mul_action S A] [is_scalar_tower S R A]
  {C : Type*} [semiring C] [algebra R C]
variables [star_ring R] [star_ring A] [star_ring B] [star_ring C]

/-- coercion from a star algebra into its unitization as a non-unital star algbera homomorphism. -/
@[simps]
def unitization.coe_non_unital_star_alg_hom (R A : Type*) [comm_semiring R] [star_ring R]
  [non_unital_semiring A] [star_ring A] [module R A] :
  A →⋆ₙₐ[R] unitization R A :=
{ to_fun := coe,
  map_smul' := unitization.coe_smul R,
  map_zero' := unitization.coe_zero R,
  map_add' := unitization.coe_add R,
  map_mul' := unitization.coe_mul R,
  map_star' := unitization.coe_star }


lemma unitization.star_alg_hom_ext {φ ψ : unitization R A →⋆ₐ[S] B} (h : ∀ a : A, φ a = ψ a)
  (h' : ∀ r, φ (algebra_map R (unitization R A) r) = ψ (algebra_map R (unitization R A) r)) :
  φ = ψ :=
begin
  have := @unitization.alg_hom_ext _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ.to_alg_hom ψ.to_alg_hom h h',
  ext x,
  apply fun_like.congr_fun this x,
end


/-- See note [partially-applied ext lemmas] -/
@[ext]
lemma unitization.star_alg_hom_ext' {φ ψ : unitization R A →⋆ₐ[R] C}
  (h : (φ : unitization R A →⋆ₙₐ[R] C).comp (unitization.coe_non_unital_star_alg_hom R A) =
    (ψ : unitization R A →⋆ₙₐ[R] C).comp (unitization.coe_non_unital_star_alg_hom R A)) :
  φ = ψ :=
unitization.star_alg_hom_ext (fun_like.congr_fun h) (by simp [alg_hom.commutes])

/-- Non-unital star algebra homomorphisms from `A` into a unital star `R`-algebra `C` lift uniquely
to `unitization R A →⋆ₐ[R] C`. This is the universal property of the unitization. -/
def unitization.star_lift [star_module R C] : (A →⋆ₙₐ[R] C) ≃ (unitization R A →⋆ₐ[R] C) :=
{ to_fun := λ φ,
  { map_star' := λ x,
    begin
      simp only [alg_hom.to_fun_eq_coe, unitization.lift_apply_apply, unitization.fst_star,
        algebra_map_star_comm, unitization.snd_star, star_add, add_right_inj],
      simp only [non_unital_star_alg_hom.coe_to_non_unital_alg_hom, map_star φ],
    end,
    .. unitization.lift φ.to_non_unital_alg_hom },
  inv_fun := λ φ, φ.to_non_unital_star_alg_hom.comp (unitization.coe_non_unital_star_alg_hom R A),
  left_inv := λ φ,
  begin
    ext,
    simp only [alg_hom.to_fun_eq_coe, unitization.lift_apply_apply,
      non_unital_star_alg_hom.coe_to_non_unital_alg_hom, non_unital_star_alg_hom.comp_apply,
      unitization.coe_non_unital_star_alg_hom_apply, star_alg_hom.coe_to_non_unital_star_alg_hom,
      star_alg_hom.coe_mk, unitization.fst_coe, map_zero, unitization.snd_coe, zero_add]
  end,
  right_inv := λ φ, unitization.star_alg_hom_ext' (by {ext, simp}) }


end lift

section algebra

variables (𝕜 A : Type*) [nontrivially_normed_field 𝕜] [non_unital_normed_ring A]
variables [normed_space 𝕜 A] [is_scalar_tower 𝕜 A A] [smul_comm_class 𝕜 A A]

open continuous_linear_map

/-- Multiplication on the left in a non-unital algebra `A` as a non-unital algebra homomorphism
into the algebra of continuous linear maps. This is an upgrade of `continuous_linear_map.mul`. -/
noncomputable def non_unital_alg_hom.Lmul : A →ₙₐ[𝕜] (A →L[𝕜] A) :=
{ to_fun := λ a, continuous_linear_map.mul 𝕜 A a,
  map_mul' := λ a b, ext $ λ x, mul_assoc a b x,
  map_zero' := ext $ λ x, by simp only [map_zero],
  .. continuous_linear_map.mul 𝕜 A }

/- In the above, you should have provided a definition in the `to_fun` field, something like:
`λ a, blah a`. Below, `blah` is what you should put on the right-hand side of the equality
where the first `sorry` is. -/
@[simp] lemma non_unital_alg_hom.coe_Lmul : ⇑(non_unital_alg_hom.Lmul 𝕜 A) = mul 𝕜 A := rfl


/- `lrr` stands for "left regular representation" which is multiplication on the left. So, given
`(k, a) : unitization 𝕜 A`, the second coordinate of `unitization.lrr (k, a)` should be the
representation of `unitization 𝕜 A` on `A →L[𝕜] A`; note that this is not just
`non_unital_alg_hom.Lmul` for a few reasons: (a) that would either be `A` acting on `A`, or
(b) `unitization 𝕜 A` acting on `unitization 𝕜 A`, and (c) that's a `non_unital_alg_hom` but
here we need an `alg_hom`. In addition, the first coordinate of `unitization.lrr (k, a)` should
just be `k`. See `unitization.lrr_apply` also. -/
noncomputable def unitization.lrr :
  unitization 𝕜 A →ₐ[𝕜] (𝕜 × (A →L[𝕜] A)) :=
(unitization.lift 0).prod (unitization.lift $ non_unital_alg_hom.Lmul 𝕜 A)

/- regardless of how exactly you built the algebra homomorphism `unitization.lrr` above, as a
function it should behave in the following way (the proof given here need not be `rfl`). -/
@[simp] lemma unitization.lrr_apply (x : unitization 𝕜 A) :
  (unitization.lrr 𝕜 A) x = (x.fst, algebra_map 𝕜 (A →L[𝕜] A) x.fst + mul 𝕜 A x.snd) :=
show (x.fst + 0, _) = (x.fst, _), by { rw [add_zero], refl }
.

/- this lemma establishes that if `continuous_linear_map.mul 𝕜 A` is injective, then so is
`unitization.lrr 𝕜 A`. When `A` is a C⋆-algebra, then `continuous_linear_map.mul 𝕜 A` is an
isometry (see `mul_isometry`), and is therefore automatically injective. -/
lemma unitization.lrr_injective_of_clm_mul_injective (h : function.injective (mul 𝕜 A)) :
  function.injective (unitization.lrr 𝕜 A) :=
begin
  rw injective_iff_map_eq_zero,
  intros x hx,
  induction x using unitization.ind,
  rw [map_add] at hx,
  simp only [prod.mk_add_mk, add_zero, unitization.fst_inl, unitization.lrr_apply,
    unitization.snd_inl, unitization.snd_coe, prod.mk_eq_zero, zero_add, unitization.fst_coe,
    map_zero, unitization.lrr_apply, add_zero, prod.mk_eq_zero] at hx,
  obtain ⟨rfl, hx⟩ := hx,
  simp only [map_zero, zero_add, unitization.inl_zero] at hx ⊢,
  rw [←map_zero (mul 𝕜 A)] at hx,
  rw [h hx, unitization.coe_zero],
end

.

end algebra

section cstar_unitization_norm

variables (𝕜 A : Type*) [densely_normed_field 𝕜] [non_unital_normed_ring A]
variables [normed_space 𝕜 A] [is_scalar_tower 𝕜 A A] [smul_comm_class 𝕜 A A]
variables [star_ring A] [cstar_ring A]

open continuous_linear_map

/- this specializes `unitization.lrr_injective_of_clm_mul_injective` to the case when `A` is a
C⋆-algebra, because in this cases it is not necessary to assume that left mulitplication is
injective -/
lemma unitization.lrr_injective : function.injective (unitization.lrr 𝕜 A) :=
unitization.lrr_injective_of_clm_mul_injective 𝕜 A (mul_isometry 𝕜 A).injective

/- pull back the normed ring structure from `(A →L[𝕜] A) × 𝕜` to `unitization 𝕜 A` using the
algebra homomorphism `unitization.lrr 𝕜 A`. -/
noncomputable instance : normed_ring (unitization 𝕜 A) :=
normed_ring.induced (unitization 𝕜 A) (𝕜 × (A →L[𝕜] A)) (unitization.lrr 𝕜 A)
  (unitization.lrr_injective 𝕜 A)

/- pull back the normed algebra structure from `(A →L[𝕜] A) × 𝕜` to `unitization 𝕜 A` using the
algebra homomorphism `unitization.lrr 𝕜 A`. -/
noncomputable instance : normed_algebra 𝕜 (unitization 𝕜 A) :=
normed_algebra.induced 𝕜 (unitization 𝕜 A) (𝕜 × (A →L[𝕜] A)) (unitization.lrr 𝕜 A)

.


/- this follows easily from `unitization.lrr_apply` and the definition of the norm on
`unitization 𝕜 A`. -/
lemma unitization.norm_def (x : unitization 𝕜 A) :
  ‖x‖ = ‖x.fst‖ ⊔ ‖algebra_map 𝕜 (A →L[𝕜] A) x.fst + mul 𝕜 A x.snd‖ :=
begin
  unfold norm,
  rw unitization.lrr_apply,
  refl,
end

-- not necessary, but should be in mathlib and I think it's missing
lemma commute.mul_hom_injective {F M N : Type*} [has_mul M] [has_mul N] [mul_hom_class F M N]
  {x y : M} {f : F} (hf : function.injective f) (h : commute (f x) (f y)) : commute x y :=
hf (by simpa only [map_mul] using h.eq)

-- not necessary, but should be in mathlib and I think it's missing
lemma commute.star {M : Type*} [semigroup M] [star_semigroup M] {x y : M} (h : commute x y) :
  commute (star x) (star y) :=
by simpa only [star_mul] using congr_arg star h.eq.symm


section c_star_property

/- this is the key lemma (i.e., the hardest one to prove) on the road to establishing the instance
`cstar_ring (unitization 𝕜 A)` (i.e., proving that the norm on `unitization 𝕜 A` satisfies the
C⋆-property).

Likely, this lemma and many of the ones between here and the `cstar_ring` instance could be
combined (and this is what we should do in mathlib), but for now it's simpler to just separate
them out. -/
lemma norm_lrr_snd_le_sqrt [star_ring 𝕜] [cstar_ring 𝕜] [star_module 𝕜 A] (x : unitization 𝕜 A) :
 ‖(unitization.lrr 𝕜 A x).snd‖ ≤ real.sqrt (‖(unitization.lrr 𝕜 A (star x * x)).snd‖) :=
begin
  simp only [unitization.lrr_apply],
  rw ←Sup_closed_unit_ball_eq_norm,
  refine cSup_le ((metric.nonempty_closed_ball.2 zero_le_one).image _) _,
  rintro _ ⟨b, hb, rfl⟩,
  simp only,
  rw [←real.sqrt_sq (norm_nonneg _), real.sqrt_le_sqrt_iff (norm_nonneg _)],
  rw [sq, ←cstar_ring.norm_star_mul_self],
  rw [continuous_linear_map.add_apply],
  rw [star_add, mul_apply', algebra.algebra_map_eq_smul_one, continuous_linear_map.smul_apply,
    continuous_linear_map.one_apply, star_mul, star_smul],
  rw [add_mul, smul_mul_assoc, ←mul_smul_comm],
  rw [mul_assoc, ←mul_add],
  refine (norm_mul_le _ _).trans _,
  have hb' : ‖star b‖ ≤ 1 := (norm_star b).symm ▸  mem_closed_ball_zero_iff.1 hb,
  refine (mul_le_mul_of_nonneg_right hb' (norm_nonneg _)).trans _,
  rw [one_mul, ←Sup_closed_unit_ball_eq_norm],
  refine le_cSup _ ⟨b, hb, _⟩,
  { refine ⟨‖(star x * x).fst‖ + ‖(star x * x).snd‖, _⟩,
    rintro _ ⟨y, hy, rfl⟩,
    refine (norm_add_le _ _).trans (add_le_add _ _),
    { rw [algebra.algebra_map_eq_smul_one],
      refine (norm_smul _ _).trans_le _,
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (mem_closed_ball_zero_iff.1 hy) (norm_nonneg (star x * x).fst) },
    { exact (unit_le_op_norm _ y $ mem_closed_ball_zero_iff.1 hy).trans
        (op_norm_mul_apply_le _ _ _), } },
  { simp only [continuous_linear_map.add_apply, mul_apply', unitization.snd_star,
      unitization.snd_mul, unitization.fst_mul, unitization.fst_star,
      algebra.algebra_map_eq_smul_one, smul_apply, one_apply, smul_add, mul_add, add_mul],
    simp only [smul_smul, smul_mul_assoc, ←add_assoc, ←mul_assoc, mul_smul_comm] }
end

.

-- follows relatively easily from the previous lemma
lemma norm_lrr_snd_sq [star_ring 𝕜] [cstar_ring 𝕜] [star_module 𝕜 A] (x : unitization 𝕜 A) :
  ‖(unitization.lrr 𝕜 A x).snd‖ ^ 2 ≤ ‖(unitization.lrr 𝕜 A (star x * x)).snd‖ :=
(real.le_sqrt (norm_nonneg _) (norm_nonneg _)).mp $ norm_lrr_snd_le_sqrt _ _ _

/- follows easily because (a) `unitization.lrr` is an algebra homomorphism, (b) multiplication
over `×` is defined pointwise, and (c) `A` is a normed ring. -/
lemma norm_lrr_star_mul_self_snd_le [star_ring 𝕜] [cstar_ring 𝕜] [star_module 𝕜 A]
  (x : unitization 𝕜 A) : ‖(unitization.lrr 𝕜 A (star x * x)).snd‖ ≤
    ‖(unitization.lrr 𝕜 A (star x)).snd‖ * ‖(unitization.lrr 𝕜 A x).snd‖ :=
begin
  rw [map_mul, prod.snd_mul],
  exact norm_mul_le _ _,
end

.

/- it helps to handle the case whenthe left-hand side is zero separately from the case when it is
nonzero. The nonzero case uses the preceding results. -/
lemma norm_lrr_snd_le_star [star_ring 𝕜] [cstar_ring 𝕜] [star_module 𝕜 A] (x : unitization 𝕜 A) :
  ‖(unitization.lrr 𝕜 A x).snd‖ ≤ ‖(unitization.lrr 𝕜 A (star x)).snd‖ :=
begin
  simp only [add_zero, unitization.lrr_apply, unitization.snd_star, unitization.fst_star],
  by_cases h : algebra_map 𝕜 (A →L[𝕜] A) x.fst + mul 𝕜 A x.snd = 0,
  { simp only [h, norm_zero, norm_le_zero_iff],
    exact norm_nonneg _ },
  { have := (norm_lrr_snd_sq 𝕜 A x).trans (norm_lrr_star_mul_self_snd_le 𝕜 A x),
    rw [sq] at this,
    rw [←ne.def, ←norm_pos_iff] at h,
    simp only [add_zero, unitization.lrr_apply, unitization.snd_star,
      unitization.fst_star, star_star] at this,
    exact (mul_le_mul_right h).mp this, }
end

-- use the previous result and the fact that the `star` operation is involutive
lemma norm_lrr_star_snd [star_ring 𝕜] [cstar_ring 𝕜] [star_module 𝕜 A] (x : unitization 𝕜 A) :
  ‖(unitization.lrr 𝕜 A (star x)).snd‖ = ‖(unitization.lrr 𝕜 A x).snd‖ :=
le_antisymm (by simpa only [star_star] using norm_lrr_snd_le_star 𝕜 A (star x))
  (norm_lrr_snd_le_star 𝕜 A x)

-- put everything together
lemma norm_lrr_star_mul_self_snd [star_ring 𝕜] [cstar_ring 𝕜] [star_module 𝕜 A]
  (x : unitization 𝕜 A) :
  ‖(unitization.lrr 𝕜 A (star x * x)).snd‖ = ‖(unitization.lrr 𝕜 A x).snd‖ ^ 2 :=
le_antisymm (by simpa only [norm_lrr_star_snd, sq] using norm_lrr_star_mul_self_snd_le 𝕜 A x)
  (norm_lrr_snd_sq 𝕜 A x)

-- the stuff for the second coordinate is much simpler and follows almost immediately.
lemma norm_lrr_star_mul_self_fst [star_ring 𝕜] [cstar_ring 𝕜] [star_module 𝕜 A]
  (x : unitization 𝕜 A) :
  ‖(unitization.lrr 𝕜 A (star x * x)).fst‖ = ‖(unitization.lrr 𝕜 A x).fst‖ ^ 2 :=
begin
  simp only [unitization.lrr_apply, unitization.fst_mul, unitization.fst_star, add_zero, norm_mul,
    norm_star, sq],
end

/- the norm on `unitization 𝕜 A` satisfies the C⋆-property
use the definition of the norm, and split into cases based on whether the norm in the first
coordinate is bigger or smaller than the norm in the second coordinate. -/
instance [star_ring 𝕜] [cstar_ring 𝕜] [star_module 𝕜 A] : cstar_ring (unitization 𝕜 A) :=
{ norm_star_mul_self := λ x,
  begin
    unfold norm,
    rw [norm_lrr_star_mul_self_snd, norm_lrr_star_mul_self_fst],
    by_cases h : ‖(unitization.lrr 𝕜 A x).fst‖ ≤ ‖(unitization.lrr 𝕜 A x).snd‖,
    { rw [sq, sq, sup_eq_right.mpr h, sup_eq_right.mpr (mul_self_le_mul_self (norm_nonneg _) h)] },
    { replace h := (not_le.mp h).le,
      rw [sq, sq, sup_eq_left.mpr h, sup_eq_left.mpr (mul_self_le_mul_self (norm_nonneg _) h)] }
  end }

end c_star_property

section completeness

lemma unitization.lrr_snd_lipschitz : lipschitz_with 1 (prod.snd ∘ unitization.lrr 𝕜 A) :=
begin
  rw lipschitz_with_iff_norm_sub_le,
  simp only [nnreal.coe_one, one_mul, function.comp_apply, ←prod.snd_sub, ←map_sub],
  exact λ _ _, le_sup_right,
end

lemma unitization.lrr_fst_lipschitz : lipschitz_with 1 (prod.fst ∘ unitization.lrr 𝕜 A) :=
begin
  rw lipschitz_with_iff_norm_sub_le,
  simp only [nnreal.coe_one, one_mul, function.comp_apply, ←prod.fst_sub, ←map_sub],
  exact λ _ _, le_sup_left,
end

/- this wouldn't be necessary if the topological structure on `unitization 𝕜 A` were
*definitionally* equal to `topological_space.prod`, but due to our construction above it instead
inherits the topological structure induced by the norm, so for now we need it.
this is a somewhat nontrivial proof. -/
theorem unitization.tendsto_iff {α : Type*} (seq : α → unitization 𝕜 A) {f : filter α}
  (x : unitization 𝕜 A) :
  filter.tendsto seq f (nhds x) ↔ filter.tendsto (λ (n : α), (seq n).fst) f (nhds x.fst) ∧
    filter.tendsto (λ (n : α), (seq n).snd) f (nhds x.snd) :=
begin
  simp_rw [metric.tendsto_nhds, dist_eq_norm],
  unfold norm,
  simp_rw [sup_lt_iff, filter.eventually_and, imp_and_distrib, forall_and_distrib],
  simp_rw [map_sub, prod.fst_sub, prod.snd_sub],
  simp_rw [←dist_eq_norm, ←metric.tendsto_nhds],
  refine ⟨λ h, _, λ h, _⟩;
  cases h with h1 h2;
  simp only [unitization.lrr_apply, add_zero] at h1 h2 ⊢;
  refine ⟨h1, _⟩,
  { have h3 := h2.sub (((algebra_map_clm 𝕜 (A →L[𝕜] A)).continuous.tendsto x.fst).comp h1),
    simp only [function.comp_app, algebra_map_clm_apply, add_sub_cancel'] at h3,
    rw (mul_isometry 𝕜 A).uniform_inducing.inducing.tendsto_nhds_iff,
    exact h3 },
  { exact (((algebra_map_clm 𝕜 (A →L[𝕜] A)).continuous.tendsto x.fst).comp h1).add
      (((mul 𝕜 A).continuous.tendsto x.snd).comp h2) },
end

-- `unitization 𝕜 A` is complete when both `𝕜` and `A` are.
instance [star_ring 𝕜] [cstar_ring 𝕜] [star_module 𝕜 A] [complete_space A] [complete_space 𝕜] :
  complete_space (unitization 𝕜 A) :=
begin
  refine metric.complete_of_cauchy_seq_tendsto (λ u hu, _),
  obtain ⟨k, hk⟩ := cauchy_seq_tendsto_of_complete
    ((unitization.lrr_fst_lipschitz 𝕜 A).uniform_continuous.comp_cauchy_seq hu),
  have hk' := ((algebra_map_clm 𝕜 (A →L[𝕜] A)).continuous.tendsto k).comp hk,
  have hu_snd := (unitization.lrr_snd_lipschitz 𝕜 A).uniform_continuous.comp_cauchy_seq hu,
  have foo := hu_snd.add hk'.cauchy_seq.neg,
  have bar : cauchy_seq (mul 𝕜 A ∘ unitization.snd ∘ u),
  { convert foo,
    ext n a,
    simp only [function.comp_apply, pi.add_apply, unitization.lrr_apply, add_zero, pi.neg_apply,
      algebra_map_clm_apply, add_neg_cancel_comm], },
  unfold cauchy_seq at bar,
  rw ←filter.map_map at bar,
  rw (mul_isometry 𝕜 A).uniform_inducing.cauchy_map_iff at bar,
  obtain ⟨a, ha⟩ := cauchy_seq_tendsto_of_complete bar,
  refine ⟨⟨k, a⟩, _⟩,
  rw unitization.tendsto_iff,
  split,
  { convert hk,
    ext,
    simp only [add_zero, unitization.lrr_apply, eq_self_iff_true, function.comp_app]},
  { exact ha }
end

end completeness

end cstar_unitization_norm



variables {R : Type*} [non_unital_normed_ring R] [star_ring R]
variables (h : ∀ r : R, ‖r‖ ≤ real.sqrt (‖star r * r‖)) (x : R)

include h

lemma foo₁ : ‖x‖ ^ 2 ≤ ‖star x * x‖ :=
(real.le_sqrt (norm_nonneg _) (norm_nonneg _)).mp $ h _

lemma foo₂ : ‖x‖ ≤ ‖star x‖ :=
or.elim (em (0 = ‖x‖)) (λ hx, hx ▸ norm_nonneg _) $
  λ hx, (mul_le_mul_right $ lt_iff_le_and_ne.mpr ⟨(norm_nonneg _), hx⟩).mp $
  sq (‖x‖) ▸ (foo₁ h x).trans (norm_mul_le (star x) x)

lemma foo₃ : ‖star x‖ = ‖x‖ :=
le_antisymm (by simpa only [star_star] using foo₂ h (star x))
  (foo₂ h x)

lemma foo₄ : ‖star x * x‖ = ‖x‖ * ‖x‖ :=
le_antisymm (by simpa only [foo₃ h x] using norm_mul_le (star x) x) $
  (sq _).symm.trans_le (foo₁ h x)

lemma foo₅ : ‖star x * x‖ = ‖x‖ * ‖x‖ :=
begin
  simp_rw [real.le_sqrt (norm_nonneg _) (norm_nonneg _), sq] at h,
  refine le_antisymm ((norm_mul_le _ _).trans _) (h x),
  have h' : ∀ r : R, ‖r‖ ≤ ‖star r‖, from λ r, or.elim (em (0 = ‖r‖)) (λ hr, hr ▸ norm_nonneg _)
    (λ hr, (mul_le_mul_right $ lt_iff_le_and_ne.mpr ⟨(norm_nonneg _), hr⟩).mp
    ((h r).trans $ norm_mul_le _ _)),
  refine mul_le_mul_of_nonneg_right (by simpa only [star_star] using h' (star x)) (norm_nonneg _),
end
