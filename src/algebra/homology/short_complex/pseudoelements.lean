import algebra.homology.short_complex.short_exact
import category_theory.abelian.pseudoelements

namespace category_theory

open limits

variables {C : Type*} [category C] [abelian C] {S S₁ S₂ : short_complex C}

lemma abelian.pseudo_surjective_of_epi'
  {A X Y : C} (f : X ⟶ Y) [epi f] (y : A ⟶ Y) :
  ∃ (A' : C) (π : A' ⟶ A) (hπ : epi π) (x : A' ⟶ X), π ≫ y = x ≫ f :=
⟨pullback f y, pullback.snd, infer_instance, pullback.fst, pullback.condition.symm⟩

lemma abelian.epi_iff_pseudo_surjective' {X Y : C} (f : X ⟶ Y) :
  epi f ↔ ∀ ⦃A : C⦄ (y : A ⟶ Y),
    ∃ (A' : C) (π : A' ⟶ A) (hπ : epi π) (x : A' ⟶ X), π ≫ y = x ≫ f :=
begin
  split,
  { introI,
    exact λ A, abelian.pseudo_surjective_of_epi' f, },
  { intro hf,
    obtain ⟨A', π, hπ, x, hx⟩ := hf (𝟙 Y),
    rw category.comp_id at hx,
    rw hx at hπ,
    haveI := hπ,
    exact epi_of_epi x f, },
end

namespace short_complex

lemma exact.pseudo_exact' (h : S.exact) {A : C} (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0) :
  ∃ (A' : C) (π : A' ⟶ A) (hπ : epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f :=
begin
  haveI := h,
  refine ⟨pullback (S.lift_cycles _ hx₂) S.to_cycles, pullback.fst, _, pullback.snd, _⟩,
  { rw short_complex.exact_iff_epi_to_cycles at h,
    haveI := h,
    apply_instance, },
  { simp only [← S.to_cycles_i, ← pullback.condition_assoc, lift_cycles_i], },
end

variable (S)

lemma exact_iff_pseudo_exact' : S.exact ↔
  ∀ ⦃A : C⦄ (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0),
  ∃ (A' : C) (π : A' ⟶ A) (hπ : epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f :=
begin
  split,
  { exact λ h A, h.pseudo_exact', },
  { exact exact.of_pseudo_exact' _, },
end

open_locale pseudoelement

lemma exact_iff_pseudo_exact : S.exact ↔
  (∀ b, S.g b = 0 → ∃ a, S.f a = b) :=
begin
  have eq : S.exact ↔ category_theory.exact S.f S.g,
  { rw exact_iff_exact_short_complex _ _ S.zero,
    cases S,
    refl, },
  rw eq,
  split,
  { intro h,
    exact (abelian.pseudoelement.pseudo_exact_of_exact h).2, },
  { intro h,
    refine abelian.pseudoelement.exact_of_pseudo_exact S.f S.g _,
    split,
    { intro a,
      rw [← abelian.pseudoelement.comp_apply, S.zero,
        abelian.pseudoelement.zero_apply], },
    { exact h}, }
end

variable {S}

lemma exact.pseudo_exact (h : S.exact) (b) (hb : S.g b = 0) :
  ∃ a, S.f a = b :=
begin
  rw exact_iff_pseudo_exact at h,
  exact h b hb,
end

lemma lift_cycles_comp_homology_π_eq_zero_iff
  {A : C} (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0) :
  S.lift_cycles x₂ hx₂ ≫ S.homology_π = 0 ↔
  ∃ (A' : C) (π : A' ⟶ A) (hπ : epi π) (x₁ : A' ⟶ S.X₁),
    π ≫ x₂ = x₁ ≫ S.f :=
begin
  split,
  { intro eq,
    let T := short_complex.mk S.to_cycles S.homology_π (by simp),
    have hT : T.exact := exact.of_g_is_cokernel S.homology_is_cokernel,
    rw exact_iff_pseudo_exact' at hT,
    obtain ⟨A', π, hπ, x₁, hx₁⟩ := hT (S.lift_cycles x₂ hx₂) eq,
    simp only [← cancel_mono S.cycles_i,
      category.assoc, lift_cycles_i, to_cycles_i] at hx₁,
    exact ⟨A', π, hπ, x₁, hx₁⟩, },
  { rintro ⟨A', π, hπ, x₁, hx₁⟩,
    haveI := hπ,
    simp only [← cancel_epi π, comp_zero, S.comp_lift_cycles_assoc x₂ hx₂ π, hx₁,
      ← S.comp_lift_cycles_assoc S.f S.zero x₁],
    change _ ≫ S.to_cycles ≫ _ = 0,
    simp only [to_cycles_comp_homology_π, comp_zero], },
end

lemma lift_cycles_comp_homology_π_eq_iff
  {A : C} (x₂ x₂': A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0) (hx₂' : x₂' ≫ S.g = 0) :
  S.lift_cycles x₂ hx₂ ≫ S.homology_π = S.lift_cycles x₂' hx₂' ≫ S.homology_π ↔
  ∃ (A' : C) (π : A' ⟶ A) (hπ : epi π) (x₁ : A' ⟶ S.X₁),
    π ≫ x₂ = π ≫ x₂' + x₁ ≫ S.f :=
begin
  have eq : S.lift_cycles x₂ hx₂ ≫ S.homology_π =
    S.lift_cycles x₂' hx₂' ≫ S.homology_π ↔
      S.lift_cycles (x₂ - x₂') (by rw [preadditive.sub_comp, hx₂, hx₂', sub_zero]) ≫ S.homology_π = 0,
  { rw [S.lift_cycles_sub _ _ hx₂ hx₂', preadditive.sub_comp, sub_eq_zero], },
  simp only [eq, lift_cycles_comp_homology_π_eq_zero_iff, preadditive.comp_sub,
    sub_eq_iff_eq_add'],
end

lemma mono_homology_map_iff (φ : S₁ ⟶ S₂) :
  mono (homology_map φ) ↔
    ∀ ⦃A : C⦄ (x₂ : A ⟶ S₁.X₂) (hx₂ : x₂ ≫ S₁.g = 0) (y₁ : A ⟶ S₂.X₁)
        (hy₁ : x₂ ≫ φ.τ₂ = y₁ ≫ S₂.f),
      ∃ (A' : C) (π : A' ⟶ A) (hπ : epi π) (x₁ : A' ⟶ S₁.X₁),
        π ≫ x₂ = x₁ ≫ S₁.f :=
begin
  split,
  { introI,
    intros A x₂ hx₂ y₁ hy₁,
    have eq : S₁.lift_cycles x₂ hx₂ ≫ S₁.homology_π = 0,
    { simp only [← cancel_mono (homology_map φ), category.assoc, zero_comp,
        homology_π_naturality, lift_cycles_comp_cycles_map_assoc],
      rw lift_cycles_comp_homology_π_eq_zero_iff,
      exact ⟨A, 𝟙 _, infer_instance, y₁, by rw [category.id_comp, hy₁]⟩, },
    simpa only [lift_cycles_comp_homology_π_eq_zero_iff] using eq, },
  { intros hφ,
    apply preadditive.mono_of_cancel_zero,
    intros A h₁ eq,
    obtain ⟨A', π, hπ, x, hx⟩ := abelian.pseudo_surjective_of_epi' S₁.homology_π h₁,
    haveI := hπ,
    let x₂ := x ≫ S₁.cycles_i,
    have hx₂ : x₂ ≫ S₁.g = 0 := by simp,
    have eqx : x = S₁.lift_cycles x₂ hx₂,
    { simp only [←cancel_mono S₁.cycles_i, lift_cycles_i], },
    replace eq := π ≫= eq,
    rw [reassoc_of hx, comp_zero, homology_π_naturality, eqx,
      lift_cycles_comp_cycles_map_assoc,
      lift_cycles_comp_homology_π_eq_zero_iff] at eq,
    rcases eq with ⟨A'', π', hπ', y₁, hy₁⟩,
    obtain ⟨A''', π'', hπ'', x₁, hx₁⟩ := hφ (π' ≫ x₂) (by simp) y₁ (by rw [category.assoc, hy₁]),
    rw [← cancel_epi π, hx, eqx],
    simp only [comp_zero, lift_cycles_comp_homology_π_eq_zero_iff],
    haveI := hπ',
    exact ⟨A''', π'' ≫ π', epi_comp _ _, x₁, by rw [category.assoc, hx₁]⟩, },
end

lemma epi_homology_map_iff (φ : S₁ ⟶ S₂) :
  epi (homology_map φ) ↔
    ∀ ⦃A : C⦄ (y₂ : A ⟶ S₂.X₂) (hy₂ : y₂ ≫ S₂.g = 0),
      ∃ (A' : C) (π : A' ⟶ A) (hπ : epi π) (x₂ : A' ⟶ S₁.X₂) (hx₂ : x₂ ≫ S₁.g = 0)
        (y₁ : A' ⟶ S₂.X₁), π ≫ y₂ = x₂ ≫ φ.τ₂ + y₁ ≫ S₂.f :=
begin
  split,
  { introI,
    intros A y₂ hy₂,
    obtain ⟨A', π, hπ, h₁, eq⟩ := abelian.pseudo_surjective_of_epi' (homology_map φ)
      (S₂.lift_cycles y₂ hy₂ ≫ S₂.homology_π),
    obtain ⟨A'', π', hπ', x₂, hx₂⟩ := abelian.pseudo_surjective_of_epi' S₁.homology_π h₁,
    obtain ⟨A''', π'', hπ'', y₁, hy₁⟩ := (lift_cycles_comp_homology_π_eq_iff (π' ≫ π ≫ y₂) (x₂ ≫ S₁.cycles_i ≫ φ.τ₂)
      (by simp [category.assoc, hy₂]) (by simp only [category.assoc, φ.comm₂₃,
        S₁.cycles_i_g_assoc, zero_comp, comp_zero])).mp begin
          simp only [← category.assoc π' π, ← S₂.comp_lift_cycles y₂ hy₂],
          simp only [category.assoc, eq, reassoc_of hx₂, homology_π_naturality],
          simp only [← category.assoc],
          congr' 1,
          simp only [← cancel_mono S₂.cycles_i, category.assoc, cycles_map_i, lift_cycles_i],
        end,
    haveI := hπ,
    haveI := hπ',
    haveI := hπ'',
    haveI : epi (π' ≫ π) := epi_comp _ _,
    exact ⟨A''', π'' ≫ π' ≫ π, epi_comp _ _, π'' ≫ x₂ ≫ S₁.cycles_i,
      by simp only [category.assoc, cycles_i_g, comp_zero], y₁,
      by simpa only [category.assoc] using hy₁⟩, },
  { intro hφ,
    rw abelian.epi_iff_pseudo_surjective',
    intros A h₂,
    obtain ⟨A', π, hπ, z₂, hz₂⟩ := abelian.pseudo_surjective_of_epi' S₂.homology_π h₂,
    let y₂ := z₂ ≫ S₂.cycles_i,
    have hy₂ : y₂ ≫ S₂.g = 0 := by simp,
    have eqz₂ : z₂ = S₂.lift_cycles y₂ hy₂,
    { simp only [← cancel_mono S₂.cycles_i], simp, },
    obtain ⟨A'', π', hπ', x₂, hx₂, y₁, hy₁⟩ := hφ y₂ hy₂,
    haveI := hπ,
    haveI := hπ',
    refine ⟨A'', π' ≫ π, epi_comp _ _, S₁.lift_cycles x₂ hx₂ ≫ S₁.homology_π, _⟩,
    simp only [category.assoc, hz₂, eqz₂, comp_lift_cycles_assoc, hy₁,
      homology_π_naturality, lift_cycles_comp_cycles_map_assoc,
      S₂.lift_cycles_add (x₂ ≫ φ.τ₂) (y₁ ≫ S₂.f)
        (by rw [category.assoc, φ.comm₂₃, reassoc_of hx₂, zero_comp]) (by simp),
      preadditive.add_comp, add_right_eq_self,
      lift_cycles_comp_homology_π_eq_zero_iff],
    exact ⟨A'', 𝟙 _, infer_instance, y₁, by rw category.id_comp⟩, },
end

end short_complex

end category_theory
