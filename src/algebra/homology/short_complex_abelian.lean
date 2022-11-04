import algebra.homology.short_complex
import category_theory.abelian.basic

noncomputable theory

open category_theory category_theory.limits category_theory.category

variables {C : Type*} [category C]

namespace category_theory.limits

/-- change kernel.lift to get better definitional properties -/
abbreviation kernel.lift₀ {C : Type*} [category C] [has_zero_morphisms C]
  {W X Y : C} (f : X ⟶ Y) [has_kernel f] (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f :=
(kernel_is_kernel f).lift (kernel_fork.of_ι k h)

@[simp, reassoc]
lemma kernel.lift₀_ι {C : Type*} [category C] [has_zero_morphisms C]
  {W X Y : C} (f : X ⟶ Y) [has_kernel f] (k : W ⟶ X) (h : k ≫ f = 0) :
  kernel.lift₀ f k h ≫ kernel.ι f = k :=
(kernel_is_kernel f).fac (kernel_fork.of_ι k h) walking_parallel_pair.zero

/-- change cokernel.desc to get better definitional properties -/
abbreviation cokernel.desc₀ {C : Type*} [category C] [has_zero_morphisms C]
  {W X Y : C} (f : X ⟶ Y) [has_cokernel f] (k : Y ⟶ W) (h : f ≫ k = 0) : cokernel f ⟶ W :=
(cokernel_is_cokernel f).desc (cokernel_cofork.of_π k h)

@[simp, reassoc]
lemma cokernel.π_desc₀ {C : Type*} [category C] [has_zero_morphisms C]
  {W X Y : C} (f : X ⟶ Y) [has_cokernel f] (k : Y ⟶ W) (h : f ≫ k = 0) :
  cokernel.π f ≫ cokernel.desc₀ f k h = k :=
(cokernel_is_cokernel f).fac (cokernel_cofork.of_π k h) walking_parallel_pair.one

end category_theory.limits

open category_theory.limits

variable [abelian C]

namespace short_complex

@[priority 100]
instance category_with_homology_of_abelian : category_with_homology C :=
λ S, begin
  let K := kernel S.g,
  let Q := cokernel S.f,
  let f' : S.X₁ ⟶ K := kernel.lift₀ _ _ S.zero,
  let g' : Q ⟶ S.X₃ := cokernel.desc₀ _ _ S.zero,
  let H := cokernel f',
  let i : K ⟶ S.X₂ := kernel.ι S.g,
  let p : S.X₂ ⟶ Q := cokernel.π S.f,
  let π : K ⟶ H := cokernel.π f',
  let ι : H ⟶ Q := cokernel.desc₀ _ (i ≫ p)
      (by simp only [kernel.lift₀_ι_assoc, cokernel.condition]),
  have π_ι : π ≫ ι = i ≫ p := cokernel.π_desc₀ _ _ _,
  have hi₀ : i ≫ S.g = 0 := kernel.condition _,
  have hp₀ : S.f ≫ p = 0 := cokernel.condition _,
  let hi : is_limit (kernel_fork.of_ι i hi₀) := kernel_is_kernel _,
  let hp : is_colimit (cokernel_cofork.of_π p hp₀) := cokernel_is_cokernel _,
  have hπ₀ : f' ≫ π = 0 := cokernel.condition _,
  have hι₀ : ι ≫ g' = 0,
  { simp only [← cancel_epi (cokernel.π (kernel.lift₀ S.g S.f S.zero)),
      cokernel.π_desc₀_assoc, assoc, cokernel.π_desc₀, kernel.condition, comp_zero], },
  let hπ : is_colimit (cokernel_cofork.of_π π hπ₀) := cokernel_is_cokernel _,
  /- The rest of the proof is the verification of `hι`.

    The main idea is to construct an isomorphism `e : H ≅ kernel g'`. (By definition,
    `H` is the cokernel of `f'`.), which is a composition of various isomorphisms
    `H ≅ cokernel α`, `e₁ : cokernel α ≅ abelian.coimage (i ≫ p)`,
    the isomorphism `abelian.coimage_iso_image (i ≫ p)`,
    `e₂ : abelian.image (i ≫ p) ≅ kernel β`, and `kernel β ≅ kernel g'`.

    Here `α : B ⟶ K` is the canonical map from `B := abelian.image S.f`,
    i.e. `α` is the inclusion of cycles in boundaries). The isomorphism
    `H ≅ cokernel α` (which is `cokernel f' ≅ cokernel α`) is easily obtained
    from the factorisation `fac₁ : f' = f'' ≫ α` and the fact that `f''` is an epi).
    The isomorphism `e₁ : cokernel α ≅ abelian.coimage (i ≫ p)` follows from the
    definition of the coimage as a cokernel and the construction of an
    isomorphism `B ≅ kernel (i ≫ p)`.

    Similarly `β : Q ⟶ B'` is the canonical map to `B' := abelian.coimage S.g`, and
    all the arguments are dual. -/
  let B := abelian.image S.f,
  let B' := abelian.coimage S.g,
  let i' : B ⟶ S.X₂ := abelian.image.ι S.f,
  let p' : S.X₂ ⟶ B' := abelian.coimage.π S.g,
  let f'' : S.X₁ ⟶ B := abelian.factor_thru_image S.f,
  let g'' : B' ⟶ S.X₃ := abelian.factor_thru_coimage S.g,
  let α : B ⟶ K := kernel.lift₀ _ i'
    (by simp only [← cancel_epi f'', abelian.image.fac_assoc, zero, comp_zero]),
  let β : Q ⟶ B' := cokernel.desc₀ _ p'
    (by simp only [← cancel_mono g'', assoc, cokernel.π_desc, zero, zero_comp]),
  have fac₁ : f' = f'' ≫ α,
  { simp only [← cancel_mono i, assoc, abelian.image.fac, kernel.lift₀_ι], },
  have fac₂ : β ≫ g'' = g',
  { simp only [← cancel_epi p, cokernel.π_desc₀, cokernel.π_desc, cokernel.π_desc₀_assoc], },
  haveI : mono (α ≫ i) := by { rw [show α ≫ i = i', by simp], apply_instance, },
  haveI : epi (p ≫ β) := by { rw [show p ≫ β = p', by simp], apply_instance, },
  haveI : mono α := mono_of_mono α i,
  haveI : epi β := epi_of_epi p β,
  let hB : is_limit (kernel_fork.of_ι α (show α ≫ i ≫ p = 0, by simp)) :=
    kernel_fork.is_limit.of_ι _ _
      (λ A k hk, kernel.lift₀ _ (k ≫ i) (by rw [assoc, hk]))
      (λ A k hk, by simp only [← cancel_mono i, assoc, kernel.lift₀_ι])
      (λ A k hk b hb, by simp only [← cancel_mono α, ← cancel_mono i, hb, assoc, kernel.lift₀_ι]),
  let hB' : is_colimit (cokernel_cofork.of_π β (show (i ≫ p) ≫ β = 0, by simp)) :=
    cokernel_cofork.is_colimit.of_π _ _
      (λ A k hk, cokernel.desc₀ _ (p ≫ k) (by rw [← assoc, hk]))
      (λ A k hk, by simp only [← cancel_epi p, cokernel.π_desc₀_assoc, cokernel.π_desc₀])
      (λ A k hk b hb, by simp only [← cancel_epi β, ← cancel_epi p, hb,
          cokernel.π_desc₀_assoc, cokernel.π_desc₀]),
  let eB : B ≅ kernel (i ≫ p) :=
    is_limit.cone_point_unique_up_to_iso hB (kernel_is_kernel (i ≫ p)),
  let eB' : cokernel (i ≫ p) ≅ B' :=
    is_colimit.cocone_point_unique_up_to_iso (cokernel_is_cokernel (i ≫ p)) hB',
  have fac₃ : eB.hom ≫ kernel.ι (i ≫ p) = α :=
    is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_parallel_pair.zero,
  have fac₄ : cokernel.π (i ≫ p) ≫ eB'.hom = β :=
    is_colimit.comp_cocone_point_unique_up_to_iso_hom
      (cokernel_is_cokernel _) _ walking_parallel_pair.one,
  let e₁ : cokernel α ≅ abelian.coimage (i ≫ p) :=
    cokernel_iso_of_eq fac₃.symm ≪≫ cokernel_epi_comp _ _,
  let e₂ : abelian.image (i ≫ p) ≅ kernel β :=
    (kernel_comp_mono _ _).symm ≪≫ kernel_iso_of_eq fac₄,
  let e : H ≅ kernel g' := cokernel_iso_of_eq fac₁ ≪≫ cokernel_epi_comp _ _ ≪≫ e₁ ≪≫
    abelian.coimage_iso_image (i ≫ p) ≪≫ e₂ ≪≫
    (kernel_comp_mono _ _ ).symm ≪≫ kernel_iso_of_eq fac₂,
  have he : e.hom ≫ kernel.ι _ = ι,
  { ext,
    dsimp,
    simp only [lift_comp_kernel_iso_of_eq_hom, cokernel_iso_of_eq_hom_comp_desc_assoc, assoc,
      kernel.lift_ι, cokernel.π_desc_assoc, abelian.coimage_image_factorisation,
      cokernel.π_desc₀], },
  let hι : is_limit (kernel_fork.of_ι ι hι₀) := is_limit.of_iso_limit (kernel_is_kernel _)
    (by { symmetry, exact fork.ext e he, }),
  exact has_homology.mk' ⟨K, Q, H, i, p, π, ι, π_ι, hi₀, hp₀, hi, hp, hπ₀, hι₀, hπ, hι⟩,
end

instance (S : short_complex C) : inhabited (S.homology_full_data) :=
⟨(has_homology.cond S).some⟩

end short_complex

instance short_complex_with_homology.inhabited :
  inhabited (short_complex_with_homology C) :=
⟨short_complex_with_homology.mk default default⟩

instance short_complex.homology_data.inhabited (S : short_complex C) :
  inhabited (S.homology_data) :=
⟨short_complex.homology_data.of_full_data default⟩

instance short_complex.homology_pre_data.inhabited (S : short_complex C) :
  inhabited (S.homology_pre_data) :=
⟨short_complex.homology_data.to_homology_pre_data default⟩

instance short_complex_with_homology'.inhabited :
  inhabited (short_complex_with_homology' C) :=
⟨(short_complex_with_homology.forget' C).obj default⟩
