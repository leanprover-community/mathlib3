import m4r.total_complex tactic.linarith

universes u v

noncomputable def map_mkq_equiv_quotient_comap_subtype_equiv
  {R : Type u} [ring R] {M : Type u} [add_comm_group M] [module R M]
  (p q : submodule R M) :
  q.map p.mkq ≃ₗ[R] (p.comap q.subtype).quotient :=
{ to_fun := λ ⟨x, hx⟩, (p.comap q.subtype).mkq ⟨classical.some hx, (classical.some_spec hx).1⟩,
  map_add' := sorry,
  map_smul' := sorry,
  inv_fun := (p.comap q.subtype).liftq (linear_map.cod_restrict (q.map p.mkq) (p.mkq.comp q.subtype)
    (λ x, submodule.mem_map_of_mem x.2)) (λ x hx, by {rw linear_map.mem_ker, ext, simp only [submodule.subtype_apply, submodule.quotient.mk_eq_zero, submodule.mkq_apply, submodule.coe_zero,
  linear_map.cod_restrict_apply, linear_map.comp_apply], exact hx }),
  left_inv := λ x, by {cases x with x hx, revert hx, refine quotient.induction_on' x (λ y hy, _),
    erw submodule.liftq_apply,
    ext,
    exact (classical.some_spec hy).2,  },
  right_inv := λ x, quotient.induction_on' x $ λ y, by {erw submodule.liftq_apply,
    sorry } }

def is_projective
  (R : Type u) [ring R] (M : Type u) [add_comm_group M] [module R M] :
-- M is the R-module on which `projective` is a predicate
  Prop := -- `projective R M` is a proposition
-- this rather obscure definition says that the map from the free R-module on
-- the set M to M splits as R-module map; it doesn't matter what the
-- actual definition is though, because we're going to make an API.
∃ s : M →ₗ[R] (M →₀ R), ∀ (m : M), finsupp.total M M R id (s m) = m

namespace function

variables {α β : Type u} (f : α → β) (hf : surjective f)

@[simp] lemma surj_inv.apply (b) : f (surj_inv hf b) = b := surj_inv_eq hf b

end function

lemma comm_apply {R : Type u} [ring R] {ι : Type} [has_succ ι] {cov : bool}
  (F G : differential_object.complex_like ι (Module R) cov) (f : F ⟶ G) (n l : ι)
  (x : F.X n) : f.f l (F.d n l x) = G.d n l (f.f n x) :=
linear_map.ext_iff.1 (f.comm _ _) _

namespace chain_complex

def pure (R M : Type u) [ring R] [add_comm_group M] [semimodule R M] :
  chain_complex ℤ (Module R) :=
chain_complex.mk' (λ n, if n = 0 then Module.of R M else Module.of R punit)
  (λ n, 0) (λ i, rfl)

variables {R : Type u} [ring R] {F : chain_complex ℤ (Module R)}(n : ℤ)


-- alt def because `homological_complex.homology` is slow and I'm not sure how to prove
-- things about it. (actually this is the only defn now)
@[reducible] def homology (R : Type u) [ring R] (F : chain_complex ℤ (Module.{u} R))
  (n : ℤ) : Type u :=
submodule.quotient $ (F.d (n + 1) n).range.comap (F.d n (n - 1)).ker.subtype

lemma ker_le_ker {R : Type u} [ring R] {F G : chain_complex ℤ (Module.{u} R)} (f : F ⟶ G)
  (n l : ℤ) : (F.d n l).ker.map (f.f n) ≤ (G.d n l).ker :=
λ x ⟨y, hym, hy⟩, linear_map.mem_ker.2 $
by rw [←hy, ←comm_apply, linear_map.mem_ker.1 hym, linear_map.map_zero]

lemma range_le_range {R : Type u} [ring R] {F G : chain_complex ℤ (Module.{u} R)} (f : F ⟶ G)
  (n l : ℤ) : (F.d n l).range.map (f.f l) ≤ (G.d n l).range :=
λ x ⟨y, ⟨z, hzm, hz⟩, hy⟩, by rw [←hy, ←hz, comm_apply]; exact linear_map.mem_range_self _ _

def ker_equiv_ker {i j k l : ℤ} (hij : i = j) (hkl : k = l) : (F.d i k).ker ≃ₗ[R] (F.d j l).ker :=
linear_equiv.of_submodules (category_theory.eq_to_iso (congr_arg _ hij)).to_linear_equiv _ _
sorry

def range_equiv_range  {i j k l : ℤ} (hij : i = j) (hkl : k = l) : (F.d i k).range ≃ₗ[R] (F.d j l).range :=
linear_equiv.of_submodules (category_theory.eq_to_iso (congr_arg _ hkl)).to_linear_equiv _ _
sorry

def homology_map {R : Type u} [ring R] {F G : chain_complex ℤ (Module.{u} R)} (f : F ⟶ G)
  (n : ℤ) :
  homology R F n →ₗ[R] homology R G n :=
submodule.mapq _ _ (linear_map.cod_restrict _ ((f.f n).comp (submodule.subtype _)) $
λ x, ker_le_ker f n (n - 1) $ submodule.mem_map_of_mem x.2)
(λ x ⟨y, hym, hy⟩,
begin
  have := range_le_range f (n + 1) n (submodule.mem_map_of_mem (linear_map.mem_range_self _ y)),
  rw hy at this,
  rw [submodule.mem_comap, submodule.mem_comap],
  convert this,
end)


noncomputable def homology_of_d_eq_zero {R : Type u} [ring R] (F : chain_complex ℤ (Module R))
  (h : ∀ n m, F.d n m = 0) (n : ℤ) :
  homology R F n ≃ₗ[R] F.X n :=
linear_equiv.of_bijective
(submodule.liftq _ (submodule.subtype _) $ λ x ⟨y, hym, hy⟩, linear_map.mem_ker.2 $ by
  rw h at hy; rw ← hy; refl)
(linear_map.ker_eq_bot'.2 $ λ x, quotient.induction_on' x $ λ y hy,
begin
  erw submodule.liftq_apply at hy,
  rw linear_map.ker_eq_bot'.1 (submodule.ker_subtype _) _ hy,
  refl,
end)
(linear_map.range_eq_top.2 $ λ x,
begin
  use [submodule.mkq _ (⟨x, linear_map.mem_ker.2 (by rw h n _; refl)⟩ : (F.d n _).ker)],
  simp only [submodule.subtype_apply, submodule.liftq_apply, submodule.coe_mk, submodule.mkq_apply],
end)

end chain_complex
namespace cochain_complex

@[reducible] def cohomology (R : Type u) [ring R] (F : cochain_complex ℤ (Module.{u} R))
  (n : ℤ) : Type u :=
submodule.quotient $ (F.d (n - 1) n).range.comap (F.d n (n + 1)).ker.subtype

lemma ker_le_ker {R : Type u} [ring R] {F G : cochain_complex ℤ (Module.{u} R)} (f : F ⟶ G)
  (n l : ℤ) : (F.d n l).ker.map (f.f n) ≤ (G.d n l).ker :=
λ x ⟨y, hym, hy⟩, linear_map.mem_ker.2 $
by rw [←hy, ←comm_apply, linear_map.mem_ker.1 hym, linear_map.map_zero]

lemma range_le_range {R : Type u} [ring R] {F G : cochain_complex ℤ (Module.{u} R)} (f : F ⟶ G)
  (n l : ℤ) : (F.d n l).range.map (f.f l) ≤ (G.d n l).range :=
λ x ⟨y, ⟨z, hzm, hz⟩, hy⟩, by rw [←hy, ←hz, comm_apply]; exact linear_map.mem_range_self _ _

def cohomology_map {R : Type u} [ring R] {F G : cochain_complex ℤ (Module.{u} R)} (f : F ⟶ G)
  (n : ℤ) :
  cohomology R F n →ₗ[R] cohomology R G n :=
submodule.mapq _ _ (linear_map.cod_restrict _ ((f.f n).comp (submodule.subtype _)) $
λ x, ker_le_ker f n (n + 1) $ submodule.mem_map_of_mem x.2)
(λ x ⟨y, hym, hy⟩,
begin
  have := range_le_range f (n - 1) n (submodule.mem_map_of_mem (linear_map.mem_range_self _ y)),
  rw hy at this,
  rw [submodule.mem_comap, submodule.mem_comap],
  convert this,
end)

variables (n : ℤ)

noncomputable def cohomology_of_d_eq_zero {R : Type u} [ring R] (F : cochain_complex ℤ (Module R))
  (h : ∀ n m, F.d n m = 0) (n : ℤ) :
  cohomology R F n ≃ₗ[R] F.X n :=
linear_equiv.of_bijective
(submodule.liftq _ (submodule.subtype _) $ λ x ⟨y, hym, hy⟩, linear_map.mem_ker.2 $ by
  rw h at hy; rw ← hy; refl)
(linear_map.ker_eq_bot'.2 $ λ x, quotient.induction_on' x $ λ y hy,
begin
  erw submodule.liftq_apply at hy,
  rw linear_map.ker_eq_bot'.1 (submodule.ker_subtype _) _ hy,
  refl,
end)
(linear_map.range_eq_top.2 $ λ x,
begin
  use [submodule.mkq _ (⟨x, linear_map.mem_ker.2 (by rw h n _; refl)⟩ : (F.d n _).ker)],
  simp only [submodule.subtype_apply, submodule.liftq_apply, submodule.coe_mk, submodule.mkq_apply],
end)

end cochain_complex

namespace is_projective
open chain_complex
variables {R : Type u} [ring R] {M : Type u} [add_comm_group M] [module R M] (h : is_projective R M)
#check Module
theorem universal_property_of_projective {R A B M : Type u} [ring R] [add_comm_group M] [semimodule R M]
  (h : is_projective R M)
[add_comm_group A] [add_comm_group B]
  [module R A] [module R B] (f : A →ₗ[R] B) (g : M →ₗ[R] B) -- the R-linear maps
(hf : function.surjective f) : ∃ (h : M →ₗ[R] A), f.comp h = g :=
begin
  cases h with s hs, /- let `s' be a section of the natural hom `R^M → M', which exists due to the assumption `h' -/
  let f_inv : M → A := λ m, function.surj_inv hf (g m),
  /- let `f_inv: M → A' be a map sending `g(m) ∈ B' to an element of
  `f⁻¹(g(m))' -/
  let F : (M →₀ R) →ₗ[R] A := finsupp.total _ _ _ f_inv,
  /- let `F: R^M → A' be the hom induced by the universal property of `R^M' applied to `f_inv' -/
  use F.comp s,
  /- we claim `F ∘ s: M → A' satisfies the goal statement; now we need to show `f ∘ F ∘ s = g' -/
  ext m,
  /- suffices to prove (f ∘ F ∘ s)(m) = g(m)' for all `m : M' -/
  dsimp,
  /- simplify definitions: in this case, apply the fact that `(f ∘ F ∘ s)(m)' means `f(F(s(m)))' -/
sorry
  --squeeze_simp [F, finsupp.total_apply, hg2],
end
#check enat.find
theorem is_projective_of_universal_property
  {R M : Type u} [ring R] [add_comm_group M] [semimodule R M]
  (huniv : ∀ {A B : Type u} [add_comm_group A] [add_comm_group B], by exactI ∀
  [module R A] [module R B], by exactI
  ∀ (f : A →ₗ[R] B) (g : M →ₗ[R] B), -- the R-linear maps
  function.surjective f → ∃ (h : M →ₗ[R] A), f.comp h = g) : is_projective R M :=
begin
  -- let f be the universal map (M →₀ R) →ₗ[R] M coming from the identity map
  -- so it's finsupp.sum
  specialize huniv (finsupp.total M M R (id : M → M)) (linear_map.id) _,
    intro m,
    use finsupp.single m 1,
    simp [finsupp.total_single],
  cases huniv with s hs,
  use s,
  rw linear_map.ext_iff at hs,
  exact hs,
end

structure projective_resolution (R : Type u) [ring R] (M : Type u)
  [add_comm_group M] [module R M] :=
(complex : chain_complex ℤ (Module R))  -- `Module R` with a capital M is the type of objects in
-- the category of R-modules.
(bounded : ∀ (n : ℤ), n < 0 → subsingleton (complex.X n)) -- The modules to the right of the
-- zeroth module are trivial.
(projective : ∀ (n : ℤ), is_projective R (complex.X n))
(resolution : ∀ (n : ℤ), homology R complex n ≃ₗ[R] (chain_complex.pure R M).X n)
-- The homology of the complex is isomorphic to `M` at 0 and trivial elsewhere.

lemma range_eq_ker {R : Type u} [ring R] {M : Type u} [add_comm_group M] [module R M]
  (F : projective_resolution R M) (n : ℕ) :
  (F.complex.d (n + 2) (n + 1)).range = (F.complex.d (n + 1) n).ker :=
begin
  let e : submodule.quotient _ ≃ₗ[R] Module.of R punit := F.resolution (n + 1),
  ext,
  split,
  { rintro ⟨y, hym, hy⟩,
    rw [←hy, linear_map.mem_ker],
    exact linear_map.ext_iff.1 (F.complex.d_comp_d _ _ _) _ },
  { intro h,
    have ffs : (F.complex.d (n + 1) n).ker = (F.complex.d (n + 1) (n + 1 - 1)).ker :=
    by rw add_sub_cancel,
    rw ffs at *,
    have : (⟨x, h⟩ : (F.complex.d (n + 1) (n + 1 - 1)).ker) ∈ (submodule.comap (linear_map.ker (F.complex.d (↑n + 1) (↑n + 1 - 1))).subtype
       (linear_map.range (F.complex.d (↑n + 1 + 1) (↑n + 1)))) :=
    (submodule.quotient.mk_eq_zero _).1 (@subsingleton.elim _ (equiv.subsingleton e.to_equiv) _ _),
    rw submodule.mem_comap at this,
    exact this,
        }
end

noncomputable def coker_isom (F : projective_resolution R M) :
  (F.complex.d 1 0).range.quotient ≃ₗ[R] M :=
linear_equiv.symm ((F.resolution 0).symm.trans $ linear_equiv.of_bijective
(submodule.mapq _ _ (submodule.subtype _)
(le_refl _))
(begin
  apply submodule.ker_liftq_eq_bot,
  rw linear_map.ker_comp,
  rw submodule.ker_mkq,
  exact le_refl _,
end)
(begin
  erw submodule.range_liftq,
  rw [linear_map.range_comp, submodule.map_mkq_eq_top, submodule.range_subtype],
  convert sup_top_eq,
  convert linear_map.ker_zero,
  haveI : subsingleton (F.complex.X (0 - 1)) := F.bounded _ (by linarith),
  unfreezingI
  { exact @unique.eq_default _ linear_map.unique_of_right _ },
end))

noncomputable def resolution_projection (F : projective_resolution R M) :
  F.complex.X 0 →ₗ[R] M :=
(coker_isom F).to_linear_map.comp (F.complex.d 1 0).range.mkq

lemma surjective_of_resolution_projection (F : projective_resolution R M) :
  function.surjective (resolution_projection F) :=
(equiv.comp_surjective (F.complex.d 1 0).range.mkq (coker_isom F).to_equiv).2
  (submodule.quotient.mk_surjective _)

lemma projective_of_subsingleton (R : Type u) [ring R] (M : Type u)
  [add_comm_group M] [module R M] [subsingleton M] :
is_projective R M :=
begin
  use 0,
  simp,
end

lemma projection_ker_eq_range (F : projective_resolution R M) :
  (resolution_projection F).ker = (F.complex.d 1 0).range :=
begin
  rw [←submodule.ker_mkq (F.complex.d 1 0).range,
    ←submodule.comap_bot (linear_map.range (F.complex.d 1 0)).mkq],
  convert linear_map.ker_comp (F.complex.d 1 0).range.mkq (coker_isom F).to_linear_map,
  exact (coker_isom F).ker.symm,
end

lemma d_eq_zero_left (F : projective_resolution R M) (n m : ℤ)
  (h : n ≤ 0) : F.complex.d n m = 0 :=
begin
  cases le_iff_lt_or_eq.1 h with H H,
  { haveI : subsingleton (F.complex.X n) := F.bounded _ (by linarith),
  unfreezingI
  { exact @unique.eq_default _ linear_map.unique_of_left _ }},
  { rw H,
    cases classical.em (0 = succ m) with hm hm,
    { have : m = -1 := (add_left_inj 1).1 (by rw [neg_add_self, hm]; refl),
      rw this,
      haveI : subsingleton (F.complex.X (-1)) := F.bounded _ (by linarith),
      unfreezingI
      { exact @unique.eq_default _ linear_map.unique_of_right _ }},
    { exact F.complex.d_eq_zero hm }}
end

lemma d_eq_zero_right (F : projective_resolution R M) (n m : ℤ)
  (h : m < 0) : F.complex.d n m = 0 :=
begin
  haveI : subsingleton (F.complex.X m) := F.bounded _ (by linarith),
  unfreezingI
  { exact @unique.eq_default _ linear_map.unique_of_right _ }
end

noncomputable def projective_resolution_of_projective (R : Type u) [ring R]
  (M : Type u) [add_comm_group M] [module R M] (H : is_projective R M) :
  projective_resolution R M :=
{ complex := { X := λ n, if n = 0 then Module.of R M else Module.of R punit,
    d := λ i j, 0,
    d_comp_d := λ i j k, linear_map.comp_zero _,
    d_eq_zero := λ _ _ _, rfl },
  bounded := λ n hn, -- let n ∈ ℤ be negative
  begin
    dsimp,
    rw if_neg (int.ne_of_lt hn), -- apply the fact that n cannot be 0
    exact punit.subsingleton,
  end,
  projective := λ n,
  begin
    dsimp,
    split_ifs, -- split into the cases n = 0 and n ≠ 0
    { rwa if_pos h }, -- apply the assumptions that n = 0 and M is projective
    { rw if_neg h, -- apply the assumption n ≠ 0
      apply projective_of_subsingleton } -- apply that trivial modules are projective
  end,
  resolution := homology_of_d_eq_zero _ (λ m n, rfl) } -- apply the fact that in a complex whose
  -- maps are all zero, Hₙ ≅ Cₙ for each n.

variables {N : Type u} [add_comm_group N] [module R N]
  (F : projective_resolution R M) (G : projective_resolution R N) (f : M →ₗ[R] N)

noncomputable def lift_zero_aux : -- expresses `f : M →ₗ[R] N` as a map `F₀/Im d →ₗ[R] G₀/Im d`
  (F.complex.d 1 0).range.quotient →ₗ[R] (G.complex.d 1 0).range.quotient :=
(coker_isom G).symm.to_linear_map.comp (f.comp (coker_isom F).to_linear_map)

noncomputable def lift_zero : F.complex.X 0 ⟶ G.complex.X 0 :=
classical.some -- takes a proof that `∃ x, P x` and returns an `x` such that `P x`
  (universal_property_of_projective (F.projective 0)
  (G.complex.d 1 0).range.mkq -- natural surjection G₀ → G₀/Im d
  ((lift_zero_aux F G f).comp (F.complex.d 1 0).range.mkq)
  -- the composition `F₀ → F₀/Im d → G₀/Im d` where the latter map is `f`
  (submodule.quotient.mk_surjective _))

noncomputable def lift_step (n : ℕ)
  (φ : F.complex.X n ⟶ G.complex.X n)
  (hφ : ∀ x : F.complex.X (n + 1), φ (F.complex.d (n + 1) n x) ∈ (G.complex.d (n + 1) n).range) :
  F.complex.X (n + 1) ⟶ G.complex.X (n + 1) :=
classical.some
  (universal_property_of_projective (F.projective (n + 1))
  (linear_map.range_restrict (G.complex.d (n + 1) n)) -- natural surjection G(n + 1) → Im(d)
  (linear_map.cod_restrict (G.complex.d (n + 1) n).range (φ.comp (F.complex.d (n + 1) n)) hφ) $
  linear_map.range_eq_top.1 $ linear_map.range_range_restrict _)
  -- the composition `F(n + 1) → Im d → Im d` using the restriction of `φ`

noncomputable def lift_aux : Π (n : ℕ), {φ : F.complex.X n ⟶ G.complex.X n //
    (∀ (x : F.complex.X (n + 1)), (φ : F.complex.X n → G.complex.X n)
    (F.complex.d (n + 1) n x) ∈ (G.complex.d (n + 1) n).range)}
| 0 := ⟨lift_zero F G f,
begin
  intro x,
  have := classical.some_spec (universal_property_of_projective (F.projective 0)
    (G.complex.d 1 0).range.mkq ((lift_zero_aux F G f).comp (F.complex.d 1 0).range.mkq)
    (submodule.quotient.mk_surjective _)),
  have h := linear_map.ext_iff.1 this (F.complex.d 1 0 x),
  have hh : (linear_map.range (F.complex.d 1 0)).mkq (F.complex.d 1 0 x) = 0 :=
    linear_map.mem_ker.1 (by rw submodule.ker_mkq; exact linear_map.mem_range_self _ _),
  simp only [linear_map.comp_apply, hh, linear_map.map_zero] at h,
  erw submodule.quotient.mk_eq_zero at h,
  exact h,
end⟩
| (n+1) := ⟨lift_step F G n (lift_aux n).1 (lift_aux n).2,
begin
  intro x,
  have := classical.some_spec (universal_property_of_projective (F.projective (n + 1))
    (linear_map.range_restrict (G.complex.d (n + 1) n))
    (linear_map.cod_restrict (G.complex.d (n + 1) n).range ((lift_aux n).1.comp (F.complex.d (n + 1) n))
    (lift_aux n).2) $ linear_map.range_eq_top.1 $ linear_map.range_range_restrict _),
  erw range_eq_ker,
  rw linear_map.mem_ker,
  have h := subtype.ext_iff.1 (linear_map.ext_iff.1 this (F.complex.d (n + 1 + 1) (n + 1) x)),
  simp only [linear_map.cod_restrict_apply, linear_map.comp_apply] at h,
  erw [linear_map.ext_iff.1 (F.complex.d_comp_d _ _ _) x, linear_map.map_zero] at h,
  exact h,
end⟩

noncomputable def lift :
  F.complex ⟶ G.complex :=
{ f := λ n, int.rec_on n (λ j, (lift_aux F G f j).1) (λ j, 0),
  comm := λ n,
  begin
    induction n with n n,
    { intro k,
      induction k with k k,
      { ext,
        simp only [differential_object.complex_like.to_differential_object_d, function.comp_app,
          Module.coe_comp, subtype.val_eq_coe],
        cases classical.em (int.of_nat n = succ (int.of_nat k)) with hk hk,
        { induction k with k Hk,
          { cases hk,
            have := classical.some_spec (universal_property_of_projective (F.projective 1)
              (linear_map.range_restrict (G.complex.d 1 0))
              (linear_map.cod_restrict (G.complex.d 1 0).range ((lift_aux F G f 0).1.comp (F.complex.d 1 0))
              (lift_aux F G f 0).2) $ linear_map.range_eq_top.1 $ linear_map.range_range_restrict _),
            have h := subtype.ext_iff.1 (linear_map.ext_iff.1 this x),
            rw linear_map.cod_restrict_apply at h,
            exact h.symm },
          { cases hk,
            have := classical.some_spec (universal_property_of_projective (F.projective (k + 2))
              (linear_map.range_restrict (G.complex.d (k + 2) (k + 1)))
              (linear_map.cod_restrict (G.complex.d (k + 2) (k + 1)).range ((lift_aux F G f (k + 1)).1.comp (F.complex.d (k + 2) (k + 1)))
              (lift_aux F G f (k + 1)).2) $ linear_map.range_eq_top.1 $ linear_map.range_range_restrict _),
            have h := subtype.ext_iff.1 (linear_map.ext_iff.1 this x),
            rw linear_map.cod_restrict_apply at h,
            exact h.symm },},
          { rw [F.complex.d_eq_zero hk, G.complex.d_eq_zero hk],
            simp only [linear_map.map_zero, linear_map.zero_apply] }},
      { simp only [differential_object.complex_like.to_differential_object_d,
          category_theory.limits.comp_zero, subtype.val_eq_coe],
        rw [d_eq_zero_right G _ _ (int.neg_succ_lt_zero _), category_theory.limits.comp_zero] }},
    { simp only [differential_object.complex_like.to_differential_object_d,
        category_theory.limits.zero_comp, subtype.val_eq_coe],
      intro j,
      rw [d_eq_zero_left F _ _ (le_of_lt $ int.neg_succ_lt_zero _), category_theory.limits.zero_comp] }
  end }

theorem lift_comp (φ : F.complex ⟶ G.complex)
  (H : (linear_map.range (G.complex.d 1 0)).mkq.comp (φ.f 0) = (lift_zero_aux F G f).comp
    (linear_map.range (F.complex.d 1 0)).mkq) :
  (resolution_projection G).comp (φ.f 0) = f.comp (resolution_projection F) :=
begin
  unfold resolution_projection,
  ext,
  replace H := linear_map.ext_iff.1 H x,
  apply linear_equiv.injective (coker_isom G).symm,
  simp only [submodule.mkq_apply, linear_equiv.coe_to_linear_map,
    linear_equiv.symm_apply_apply, linear_map.comp_apply],
  exact H,
end

end is_projective
open chain_complex
variables (R : Type u) [ring R] (j : ℤ)

structure chain_complex2 :=
(X : ℤ → Module R)
(d : Π n : ℤ, X n ⟶ X (n - 1))
(d_squared' : ∀ n : ℤ, (d (n - 1)).comp (d n) = 0)

structure chain_map2 (F G : chain_complex2 R) :=
(f : Π n : ℤ, F.X n ⟶ G.X n)
(comm' : ∀ n : ℤ, (f (n - 1)).comp (F.d n) = (G.d n).comp (f n))

instance : category_theory.has_hom (chain_complex2 R) :=
{ hom := chain_map2 R }

variables {R}

def complex_cast (F : chain_complex2 R) (i j : ℤ) (h : i = j) : F.X i ≅ F.X j :=
{ hom := { to_fun := λ x, eq.rec x h,
    map_add' := λ x y, by cases h; refl,
    map_smul' := λ r x, by cases h; refl },
  inv := { to_fun := λ x, eq.rec x h.symm,
    map_add' := λ x y, by cases h; refl,
    map_smul' := λ r x, by cases h; refl },
  hom_inv_id' := by ext; cases h; refl,
  inv_hom_id' := by ext; cases h; refl }

structure homotopy2 (F G : chain_complex2 R) (f g : F ⟶ G) :=
(map : Π n : ℤ, F.X (n - 1) ⟶ G.X n)
(cond : ∀ n : ℤ, f.f n - g.f n = F.d n ≫ map n + (complex_cast F n (n + 1 - 1)
    (add_sub_cancel _ _).symm).hom ≫ map (n + 1) ≫ G.d (n + 1)
  ≫ (complex_cast G (n + 1 - 1) n (add_sub_cancel _ _)).hom)

structure chain_complex3 :=
(X : ℤ → Module R)
(d : Π i j : ℤ, X i ⟶ X j)
(d_comp_d : ∀ i j k, (d j k).comp (d i j) = 0)
(d_eq_zero : ∀ i j, j + 1 ≠ i → d i j = 0)

structure homotopy (F G : chain_complex ℤ (Module R)) (f g : F ⟶ G) :=
(map : Π i j, F.X i ⟶ G.X j)
(cond : ∀ i j k : ℤ, j + 1 = i → k + 1 = j → f.f j - g.f j
  = F.d j k ≫ map k j + map j i ≫ G.d i j)
(map_eq_zero : ∀ i j, i + 1 ≠ j → map i j = 0)

open is_projective

def homotopy_of_sub_zero (F G : chain_complex ℤ (Module R)) (f g : F ⟶ G)
  (h : homotopy F G (f - g) 0) :
  homotopy F G f g :=
{ map := h.map,
  cond := λ i j k hj hk,
  begin
    rw ←h.cond i j k hj hk,
    exact (sub_zero _).symm,
  end,
  map_eq_zero := h.map_eq_zero }

variables  {M N : Type u} [add_comm_group M] [add_comm_group N] [module R M]
  [module R N] (F : projective_resolution R M) (G : projective_resolution R N)

/-- Given a hom `φ: F₀ → G₀` which becomes 0 when we compose it with the natural surjection
`G₀ → N`, we get a hom `F₀ → G₁` making the obvious triangle commute. -/
noncomputable def lift_zero_homotopy_zero
  (φ : F.complex.X 0 →ₗ[R] G.complex.X 0) (H : (resolution_projection G).comp φ = 0) :
  F.complex.X 0 ⟶ G.complex.X 1 :=
classical.some (universal_property_of_projective (F.projective 0) (G.complex.d 1 0).range_restrict
  (linear_map.cod_restrict (G.complex.d 1 0).range φ
begin
  intro x,
  have : x ∈ ((resolution_projection G).comp φ).ker :=
    linear_map.mem_ker.1 (linear_map.ext_iff.1 H x),
  rw [linear_map.ker_comp, projection_ker_eq_range] at this,
  exact this,
end)
$ linear_map.range_eq_top.1 (linear_map.range_range_restrict _))

/-- We have d₁ ∘ lift(φ)₀ = φ₀. -/
lemma lift_zero_homotopy_zero_spec (φ : F.complex.X 0 ⟶ G.complex.X 0)
  (H : (resolution_projection G).comp φ = 0) :
  (G.complex.d 1 0).comp (lift_zero_homotopy_zero F G φ H) = φ :=
begin
  have := classical.some_spec (universal_property_of_projective (F.projective 0) (G.complex.d 1 0).range_restrict
      (linear_map.cod_restrict (G.complex.d 1 0).range φ
    begin
      intro x,
      have : x ∈ ((resolution_projection G).comp φ).ker :=
        linear_map.mem_ker.1 (linear_map.ext_iff.1 H x),
      rw [linear_map.ker_comp, projection_ker_eq_range] at this,
      exact this,
    end)
    $ linear_map.range_eq_top.1 (linear_map.range_range_restrict _)),
  ext,
  exact subtype.ext_iff.1 (linear_map.ext_iff.1 this x),
end

/-- Given a chain map `φ : F ⟶ G` such that the composition of `φ₀` with the natural surjection
`G₀ → N` is 0, we get a hom `h₁ : F₁ → G₂` satisfying `d₂ ∘ h₁ + h₀ ∘ d₁ = φ₁.` -/
noncomputable def lift_zero_homotopy_one
  (φ : F.complex ⟶ G.complex) (H : (resolution_projection G).comp (φ.f 0) = 0) :
  F.complex.X 1 ⟶ G.complex.X 2 :=
classical.some (universal_property_of_projective (F.projective 1) (G.complex.d 2 1).range_restrict
  (linear_map.cod_restrict (G.complex.d 2 1).range (φ.f 1 - (lift_zero_homotopy_zero F G (φ.f 0) H).comp (F.complex.d 1 0))
begin
  intro x,
  erw range_eq_ker,
  rw [linear_map.mem_ker, linear_map.sub_apply, linear_map.map_sub, sub_eq_zero],
  have := (lift_zero_homotopy_zero_spec F G (φ.f 0) H),
  rw linear_map.ext_iff at this,
  erw [this, linear_map.ext_iff.1 (φ.comm _ _)],
  refl,
end)
$ linear_map.range_eq_top.1 (linear_map.range_range_restrict _))

/-- We have d₂ ∘ h₁ + h₀ ∘ d₁ = φ₁. -/
lemma lift_zero_homotopy_one_spec {M N : Type u} [add_comm_group M] [add_comm_group N] [module R M]
  [module R N] (F : projective_resolution R M) (G : projective_resolution R N)
  (φ : F.complex ⟶ G.complex) (H : (resolution_projection G).comp (φ.f 0) = 0) :
  (G.complex.d 2 1).comp (lift_zero_homotopy_one F G φ H)
  + (lift_zero_homotopy_zero F G (φ.f 0) H).comp (F.complex.d 1 0) = φ.f 1 :=
begin
  have := classical.some_spec (universal_property_of_projective (F.projective 1) (G.complex.d 2 1).range_restrict
      (linear_map.cod_restrict (G.complex.d 2 1).range (φ.f 1 - (lift_zero_homotopy_zero F G (φ.f 0) H).comp (F.complex.d 1 0))
    begin
      intro x,
      erw range_eq_ker,
      rw [linear_map.mem_ker, linear_map.sub_apply, linear_map.map_sub, sub_eq_zero],
      have := (lift_zero_homotopy_zero_spec F G (φ.f 0) H),
      rw linear_map.ext_iff at this,
      erw [this, linear_map.ext_iff.1 (φ.comm _ _)],
      refl,
    end)
    $ linear_map.range_eq_top.1 (linear_map.range_range_restrict _)),
  rw ←eq_sub_iff_add_eq,
  ext,
  exact subtype.ext_iff.1 (linear_map.ext_iff.1 this x),
end

/-- Given a chain map `φ : F ⟶ G` such that `φ₀` becomes 0 when we compose it with the natural surjection
`G₀ → N,` and given homs `h1 : Fₙ → Gₙ₊₁`, `h2 : Fₙ₊₁ → Gₙ₊₂` for some `n` such that `dₙ₊₂ ∘ h2 + h1 ∘ dₙ₊₁ = φₙ₊₁`,
we get a hom `h : Fₙ₊₂ → Gₙ₊₃` such that `dₙ₊₃ ∘ h + h2 ∘ dₙ₊₂ = φₙ₊₂`. -/
noncomputable def lift_zero_homotopy_step {M N : Type u} [add_comm_group M] [add_comm_group N] [module R M]
  [module R N] (F : projective_resolution R M) (G : projective_resolution R N)
  (φ : F.complex ⟶ G.complex) (H : (resolution_projection G).comp (φ.f 0) = 0)
  (n : ℕ) (h1 : F.complex.X n ⟶ G.complex.X (n + 1)) (h2 : F.complex.X (n + 1) ⟶ G.complex.X (n + 2))
  (Hh : (G.complex.d (n + 2) (n + 1)).comp h2 + h1.comp (F.complex.d (n + 1) n) = φ.f (n + 1)) :
  F.complex.X (n + 2) ⟶ G.complex.X (n + 3) :=
/- we apply the universal property of the projectivity of `Fₙ₊₂` to the surjection `Gₙ₊₃ → Im dₙ₊₃` and the map `φₙ₊₂ - h2 ∘ dₙ₊₂ : Fₙ₊₂ → Im dₙ₊₃`.-/
classical.some (universal_property_of_projective (F.projective (n + 2)) (G.complex.d (n + 3) (n + 2)).range_restrict
  (linear_map.cod_restrict (G.complex.d (n + 3) (n + 2)).range (φ.f (n + 2) - h2.comp (F.complex.d (n + 2) (n + 1)))
begin
  intro x,
  erw range_eq_ker,
  rw [linear_map.mem_ker, linear_map.sub_apply, linear_map.map_sub, sub_eq_zero],
  replace Hh := Hh.symm,
  rw [←sub_eq_iff_eq_add, linear_map.ext_iff] at Hh,
  erw [←Hh (F.complex.d (n + 2) (n + 1) x), linear_map.sub_apply, linear_map.ext_iff.1 (φ.comm _ _)],
  convert (sub_zero _).symm,
  rw linear_map.comp_apply,
  erw linear_map.ext_iff.1 (F.complex.d_comp_d (n + 2) (n + 1) n) x,
  exact linear_map.map_zero _,
end)
$ linear_map.range_eq_top.1 (linear_map.range_range_restrict _))

/-- With assumptions and notations as above, `dₙ₊₃ ∘ h + h2 ∘ dₙ₊₂ = φₙ₊₂`. -/
lemma lift_zero_homotopy_step_spec {M N : Type u} [add_comm_group M] [add_comm_group N] [module R M]
  [module R N] (F : projective_resolution R M) (G : projective_resolution R N)
  (φ : F.complex ⟶ G.complex) (H : (resolution_projection G).comp (φ.f 0) = 0)
  (n : ℕ) (h1 : F.complex.X n ⟶ G.complex.X (n + 1)) (h2 : F.complex.X (n + 1) ⟶ G.complex.X (n + 2))
  (Hh : (G.complex.d (n + 2) (n + 1)).comp h2 + h1.comp (F.complex.d (n + 1) n) = φ.f (n + 1)) :
  (G.complex.d (n + 3) (n + 2)).comp (lift_zero_homotopy_step F G φ H n h1 h2 Hh)
  + h2.comp (F.complex.d (n + 2) (n + 1)) = φ.f (n + 2) :=
begin
  have := classical.some_spec (universal_property_of_projective (F.projective (n + 2)) (G.complex.d (n + 3) (n + 2)).range_restrict
  (linear_map.cod_restrict (G.complex.d (n + 3) (n + 2)).range (φ.f (n + 2) - h2.comp (F.complex.d (n + 2) (n + 1)))
  begin
    intro x,
    erw range_eq_ker,
    rw [linear_map.mem_ker, linear_map.sub_apply, linear_map.map_sub, sub_eq_zero],
    replace Hh := Hh.symm,
    rw [←sub_eq_iff_eq_add, linear_map.ext_iff] at Hh,
    erw [←Hh (F.complex.d (n + 2) (n + 1) x), linear_map.sub_apply, linear_map.ext_iff.1 (φ.comm _ _)],
    convert (sub_zero _).symm,
    rw linear_map.comp_apply,
    erw linear_map.ext_iff.1 (F.complex.d_comp_d (n + 2) (n + 1) n) x,
    exact linear_map.map_zero _,
  end)
  $ linear_map.range_eq_top.1 (linear_map.range_range_restrict _)),
  rw ←eq_sub_iff_add_eq,
  ext,
  exact subtype.ext_iff.1 (linear_map.ext_iff.1 this x),
end

noncomputable def lift_zero_homotopy_aux_nat {M N : Type u} [add_comm_group M] [add_comm_group N] [module R M]
  [module R N] (F : projective_resolution R M) (G : projective_resolution R N)
  (φ : F.complex ⟶ G.complex)
  (H : (resolution_projection G).comp (φ.f 0) = 0) :
  Π (n : ℕ), { h : ((F.complex.X n ⟶ G.complex.X (n + 1)) × (F.complex.X (n + 1) ⟶ G.complex.X (n + 2)))
  // (G.complex.d (n + 2) (n + 1)).comp h.2 + h.1.comp (F.complex.d (n + 1) n) = φ.f (n + 1)}
| 0 := ⟨⟨lift_zero_homotopy_zero F G (φ.f 0) H, lift_zero_homotopy_one F G φ H⟩, lift_zero_homotopy_one_spec F G φ H⟩
| (n+1) := ⟨⟨(lift_zero_homotopy_aux_nat n).1.2, lift_zero_homotopy_step F G φ H n
  (lift_zero_homotopy_aux_nat n).1.1 (lift_zero_homotopy_aux_nat n).1.2 (lift_zero_homotopy_aux_nat n).2⟩,
  lift_zero_homotopy_step_spec F G φ H _ _ _ _⟩

noncomputable def lift_zero_homotopy_aux  {M N : Type u} [add_comm_group M] [add_comm_group N] [module R M]
  [module R N] (F : projective_resolution R M) (G : projective_resolution R N)
  (φ : F.complex ⟶ G.complex)
  (H : (resolution_projection G).comp (φ.f 0) = 0) :
  Π (n : ℤ), F.complex.X n ⟶ G.complex.X (n + 1)
| (int.of_nat n) := (lift_zero_homotopy_aux_nat F G φ H n).1.1
| -[1+ n] := 0

noncomputable def lift_zero_homotopy_map {M N : Type u} [add_comm_group M] [add_comm_group N] [module R M]
  [module R N] (F : projective_resolution R M) (G : projective_resolution R N)
  (φ : F.complex ⟶ G.complex)
  (H : (resolution_projection G).comp (φ.f 0) = linear_map.comp 0 (resolution_projection F))
  (i j : ℤ) :
  F.complex.X i ⟶ G.complex.X j :=
if h : i + 1 = j then
lift_zero_homotopy_aux F G φ H i ≫ category_theory.eq_to_hom (congr_arg _ h) else 0

open category_theory

noncomputable def lift_zero_homotopy {M N : Type u} [add_comm_group M] [add_comm_group N] [module R M]
  [module R N] (F : projective_resolution R M) (G : projective_resolution R N)
  (φ : F.complex ⟶ G.complex)
  (H : (resolution_projection G).comp (φ.f 0) = 0) :
  homotopy F.complex G.complex φ 0 :=
{ map := lift_zero_homotopy_map F G φ H, -- our auxilliary definition; for `i j : ℤ` it is one of the maps we have defined if `(i, j) = (n, n + 1)` for some `n : ℕ`, and 0 otherwise.
  cond := λ i j k hj hk,
  begin
    show φ.f j - 0 = _,
    rw sub_zero,
    unfold lift_zero_homotopy_map,
    rw [dif_pos hj, dif_pos hk, add_comm], -- apply that `i + 1 = j`, `j + 1 = k`
    revert i k hj hk, -- necessary so we get a useful inductive hypothesis
    induction j with j j,
    { induction j with j Hj,
      { intros i k hj hk, -- `j = 0` case; we use `lift_zero_homotopy_zero_spec`
        erw d_eq_zero_left F _ _ (le_refl 0),
        rw [category_theory.limits.zero_comp, add_zero],
        cases hj,
        exact (lift_zero_homotopy_zero_spec F G (φ.f 0) H).symm, },
      { induction j with J hJ,
        { intros i k hj hk, -- `j = 1` case; we use `lift_zero_homotopy_one_spec`
          have h : k = 0 := by rw [←add_sub_cancel k 1, hk]; refl,
          cases hj,
          cases h,
          exact (lift_zero_homotopy_one_spec F G φ H).symm },
        { intros i k hj hk, /- `j + 2, j : ℕ` case; we do tricks to transform the goal into  a statement about `j + 1, j + 2, j + 3` (not just numbers provably equal to this triple) so that we can apply `lift_zero_homotopy_step_spec`. -/
          cases hj,
          have h : k = int.of_nat J.succ := by rw [←add_sub_cancel k 1, hk];
            simp only [int.coe_nat_succ, int.of_nat_eq_coe, add_sub_cancel, pred_int],
          cases h,
          replace Hj := Hj (succ (int.of_nat J.succ)) J rfl rfl,
          simp only [eq_to_hom_refl, category.comp_id] at Hj,
          simp only [function.comp_app, eq_to_hom_refl, category.comp_id, Module.coe_comp, linear_map.add_apply],
          exact (lift_zero_homotopy_step_spec F G φ H J (lift_zero_homotopy_aux F G φ H _)
            (lift_zero_homotopy_aux F G φ H _) Hj.symm).symm }}},
    { intros i k hj hk, -- `j < 0` case
      ext,
      rw @subsingleton.elim _ (F.bounded _ (int.neg_succ_lt_zero _)) x 0,
      simp only [linear_map.map_zero] },
  end,
  map_eq_zero := λ i j hi,
  begin
    unfold lift_zero_homotopy_map,
    erw dif_neg hi,
  end }

noncomputable def lift_unique {M N : Type u} [add_comm_group M] [add_comm_group N] [module R M]
  [module R N] (F : projective_resolution R M) (G : projective_resolution R N)
  (f : M →ₗ[R] N) (α : F.complex ⟶ G.complex) (β : F.complex ⟶ G.complex)
  (Hα : (resolution_projection G).comp (α.f 0) = f.comp (resolution_projection F))
  (Hβ : (resolution_projection G).comp (β.f 0) = f.comp (resolution_projection F)) :
  homotopy F.complex G.complex α β :=
homotopy_of_sub_zero _ _ _ _ $ lift_zero_homotopy F G
(α - β)
begin
  dsimp,
  rw [linear_map.comp_sub, Hα, Hβ, sub_self],
end

noncomputable def lift_id_unique_left {M : Type u} [add_comm_group M] [module R M]
  (F G : projective_resolution R M) (α : F.complex ⟶ G.complex) (β : G.complex ⟶ F.complex)
  (Hα : (resolution_projection G).comp (α.f 0) = resolution_projection F)
  (Hβ : (resolution_projection F).comp (β.f 0) = resolution_projection G) :
  homotopy F.complex F.complex (α ≫ β) (category_struct.id F.complex) :=
lift_unique F F linear_map.id (α ≫ β) (category_struct.id F.complex)
(show ((resolution_projection F).comp (β.f 0)).comp (α.f 0) = _,
  by rw [linear_map.id_comp, Hβ, Hα]) rfl

noncomputable def lift_id_unique_right {M : Type u} [add_comm_group M] [module R M]
  (F G : projective_resolution R M) (α : F.complex ⟶ G.complex) (β : G.complex ⟶ F.complex)
  (Hα : (resolution_projection G).comp (α.f 0) = resolution_projection F)
  (Hβ : (resolution_projection F).comp (β.f 0) = resolution_projection G) :
  homotopy G.complex G.complex (β ≫ α) (category_struct.id G.complex) :=
lift_unique G G linear_map.id (β ≫ α) (category_struct.id G.complex)
(show ((resolution_projection G).comp (α.f 0)).comp (β.f 0) = _,
  by rw [linear_map.id_comp, Hα, Hβ]) rfl
