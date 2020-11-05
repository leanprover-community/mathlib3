import category_theory.adjunction.limits
import category_theory.closed.cartesian
import category_theory.conj
import logic.basic
import tactic.equiv_rw

universes v₁ v₂ u₁ u₂

namespace category_theory
namespace monoidal

open category limits

variables {C : Type u₁} [category.{v₁} C] [has_finite_products C] [cartesian_closed C]
variables {D : Type u₂} [category.{v₁} D] [has_finite_products D] [cartesian_closed D]
variables (fb : D ⥤ C) (fs : C ⥤ D) (adj : fb ⊣ fs)

def phis : Type (max u₁ v₁) :=
{ φ : Π (A B : C), fs.obj (A ⟹ B) ⟶ fs.obj A ⟹ fs.obj B //
  (∀ (A A' B : C) (f : A ⟶ A'), φ A' B ≫ pre _ (fs.map f) = fs.map (pre _ f) ≫ φ A B) ∧
  (∀ (A B B' : C) (g : B ⟶ B'), φ A B ≫ (exp _).map (fs.map g) = fs.map ((exp _).map g) ≫ φ A B') }

def pis :=
{ π : Π (A c), fb.obj (fs.obj A ⨯ c) ⟶ A ⨯ fb.obj c //
  (∀ A c c' (g : c ⟶ c'), fb.map (limits.prod.map (𝟙 _) g) ≫ π A c' = π A c ≫ limits.prod.map (𝟙 _) (fb.map g)) ∧
  (∀ A A' c (f : A ⟶ A'), fb.map (limits.prod.map (fs.map f) (𝟙 _)) ≫ π A' c = π A c ≫ limits.prod.map f (𝟙 _))  }

namespace frobenius_internal

def phis2 :=
{ q : Π (A B c), (c ⟶ fs.obj (A ⟹ B)) → (c ⟶ fs.obj A ⟹ fs.obj B) //
  (∀ A B c c' (h : c ⟶ c') t, h ≫ q A B c' t = q A B c (h ≫ t)) ∧
  (∀ A A' B (f : A ⟶ A') c t, q A' B c t ≫ pre _ (fs.map f) = q A B c (t ≫ fs.map (pre _ f))) ∧
  (∀ A B B' (g : B ⟶ B') c t, q A B c t ≫ (exp _).map (fs.map g) = q A B' c (t ≫ fs.map ((exp _).map g))) }

lemma eq_iff_comp_right_eq {Y Z : C} (f g : Y ⟶ Z) :
  (∀ (X : C) (h : X ⟶ Y), h ≫ f = h ≫ g) ↔ f = g :=
⟨eq_of_comp_right_eq, λ t X h, t ▸ rfl⟩

noncomputable def equiv12 : phis fs ≃ phis2 fs :=
begin
  apply equiv.trans _ (equiv.subtype_subtype_equiv_subtype_inter _ _),
  apply equiv.subtype_congr _ _,
  { refine ⟨λ q, ⟨λ A B c t, t ≫ q _ _, λ A B c c' h t, by simp⟩, λ q A B, q.1 A B _ (𝟙 _), _, _⟩,
    { intros q,
      ext A B,
      simp },
    { rintro ⟨q, hq⟩,
      ext,
      simp [hq] } },
  intros q,
  dsimp,
  simp_rw [assoc],
  apply and_congr,
  { apply forall₃_congr (λ A A' B, _),
    apply forall_congr (λ f, _),
    rw [eq_iff_comp_right_eq] },
  { apply forall₃_congr (λ A B B', _),
    apply forall_congr (λ f, _),
    rw [eq_iff_comp_right_eq] },
end.

lemma is_iso_iff_precomp_bij {A B : C} (f : A ⟶ B) :
  (∀ (T : C), function.bijective (λ (g : T ⟶ _), g ≫ f)) ↔ nonempty (is_iso f) :=
begin
  split,
  { intro q, choose i g hg using (q B), exact ⟨⟨g (𝟙 _), (q A).1 (by simp [hg]), hg _⟩⟩ },
  { rintro ⟨i⟩ T,
    exactI ⟨λ g₁ g₂ eq, by rwa ← cancel_mono f, λ g, ⟨g ≫ inv f, by simp⟩⟩ }
end

lemma is_iso_iff_postcomp_bij {A B : C} (f : A ⟶ B) :
  (∀ (T : C), function.bijective (λ (g : _ ⟶ T), f ≫ g)) ↔ nonempty (is_iso f) :=
begin
  split,
  { intro q, choose i g hg using (q A), exact ⟨⟨g (𝟙 _), hg _, (q B).1 (by simp [reassoc_of (hg (𝟙 _))])⟩⟩ },
  { rintro ⟨i⟩ T,
    exactI ⟨λ g₁ g₂ eq, by rwa ← cancel_epi f, λ g, ⟨inv f ≫ g, by simp⟩⟩ }
end

lemma isos12 (φ : phis fs) :
  (∀ (A B c), function.bijective (((equiv12 fs) φ).1 A B c)) ↔ (∀ (A B : C), nonempty (is_iso (φ.1 A B))) :=
forall₂_congr (λ A B, is_iso_iff_precomp_bij _)

def phis3 :=
{ q : Π (A B c), (fb.obj c ⟶ (A ⟹ B)) → (fs.obj A ⨯ c ⟶ fs.obj B) //
  (∀ A B c c' (h : c ⟶ c') t, limits.prod.map (𝟙 _) h ≫ q A B c' t = q A B c (fb.map h ≫ t)) ∧
  (∀ A A' B (f : A ⟶ A') c t, limits.prod.map (fs.map f) (𝟙 _) ≫ q A' B c t = q A B c (t ≫ pre _ f)) ∧
  (∀ A B B' (g : B ⟶ B') c t, q A B c t ≫ fs.map g = q A B' c (t ≫ (exp A).map g)) }

lemma prod_map_comp_uncurry {A A' X Y : C} (g : X ⟶ A⟹Y) (k : A' ⟶ A) :
  limits.prod.map k (𝟙 _) ≫ cartesian_closed.uncurry g = cartesian_closed.uncurry (g ≫ pre _ k) :=
by rw [pre, ← curry_natural_left, uncurry_curry, uncurry_eq, prod.map_swap_assoc]

lemma thing {A A' X Y : C} (k : A' ⟶ A) (g : A ⨯ X ⟶ Y) :
  cartesian_closed.curry (limits.prod.map k (𝟙 _) ≫ g) = cartesian_closed.curry g ≫ pre _ k :=
by rw [curry_eq_iff, ← prod_map_comp_uncurry, uncurry_curry]

noncomputable def equiv23 (adj : fb ⊣ fs) : phis2 fs ≃ phis3 fb fs :=
begin
  apply equiv.subtype_congr _ _,
  { apply equiv.Pi_congr_right (λ A, _),
    apply equiv.Pi_congr_right (λ B, _),
    apply equiv.Pi_congr_right (λ c, _),
    apply equiv.arrow_congr,
    { apply (adj.hom_equiv _ _).symm },
    { apply ((exp.adjunction _).hom_equiv _ _).symm } },
  { intro q,
    dsimp [equiv.Pi_congr_right],
    simp_rw [equiv.symm_symm],
    apply and_congr,
    { simp_rw [← uncurry_natural_left, ← uncurry.injective_iff,
               adjunction.hom_equiv_naturality_left],
      apply forall₄_congr (λ A B c c', _),
      apply forall_congr (λ h, _),
      symmetry,
      rw equiv.forall_congr (adj.hom_equiv c' ((exp A).obj B)),
      intro x,
      refl },
    { apply and_congr,
      { apply forall₃_congr (λ A A' B, _),
        apply forall₂_congr (λ f c, _),
        rw equiv.forall_congr (adj.hom_equiv c ((exp A').obj B)),
        intro t,
        rw prod_map_comp_uncurry,
        rw ← uncurry.injective_iff,
        rw adj.hom_equiv_naturality_right },
      { apply forall₃_congr (λ A B B', _),
        apply forall₂_congr (λ f c, _),
        rw equiv.forall_congr (adj.hom_equiv c ((exp A).obj B)),
        intro x,
        rw ← uncurry_natural_right,
        rw ← uncurry.injective_iff,
        rw adj.hom_equiv_naturality_right } } }
end

lemma test' {α β φ : Sort*} (g : β ≃ φ) (f : α → β) :
  function.bijective (g ∘ f) ↔ function.bijective f :=
begin
  refine ⟨_, function.bijective.comp g.bijective⟩,
  intro k,
  have : (g.symm ∘ g) ∘ f = f,
    simp only [function.comp.left_id, equiv.symm_comp_self],
  rw ← this,
  apply function.bijective.comp g.symm.bijective k,
end

lemma test'' {α β φ : Sort*} (g : α ≃ β) (f : β → φ) :
  function.bijective (f ∘ g) ↔ function.bijective f :=
begin
  refine ⟨_, λ k, function.bijective.comp k g.bijective⟩,
  intro k,
  have : f ∘ g ∘ g.symm = f,
    simp,
  rw ← this,
  apply function.bijective.comp k g.symm.bijective,
end

lemma isos23 (φ : phis2 fs) :
  (∀ (A B c), function.bijective (((equiv23 _ _ adj) φ).1 A B c)) ↔
    (∀ (A B c), function.bijective (φ.1 A B c)) :=
begin
  apply forall₃_congr,
  intros A B c,
  dsimp [equiv23, equiv.Pi_congr_right, equiv.arrow_congr],
  rw [test', test''],
end

def phis4 :=
{ q : Π (A B c), (A ⨯ fb.obj c ⟶ B) → (fb.obj (fs.obj A ⨯ c) ⟶ B) //
  (∀ A B B' c (g : B ⟶ B') t, q A B c t ≫ g = q A B' c (t ≫ g)) ∧
  (∀ A B c c' (h : c ⟶ c') t, fb.map (limits.prod.map (𝟙 _) h) ≫ q A B c' t = q _ _ _ (limits.prod.map (𝟙 _) (fb.map h) ≫ t)) ∧
  (∀ A A' B c f t, fb.map (limits.prod.map (fs.map f) (𝟙 _)) ≫ q A' B c t = q A B c (limits.prod.map f (𝟙 _) ≫ t)) }

noncomputable def equiv34 (adj : fb ⊣ fs) : phis3 fb fs ≃ phis4 fb fs :=
begin
  apply equiv.subtype_congr _ _,
  { apply equiv.Pi_congr_right (λ A, _),
    apply equiv.Pi_congr_right (λ B, _),
    apply equiv.Pi_congr_right (λ c, _),
    apply equiv.arrow_congr,
    { apply ((exp.adjunction _).hom_equiv _ _).symm },
    { apply (adj.hom_equiv _ _).symm } },
  intro q,
  dsimp [equiv.Pi_congr_right, equiv.arrow_congr],
  simp_rw [equiv.symm_symm],
  dsimp,
  rw ← and.rotate,
  apply and_congr,
  { apply forall₃_congr (λ A B B', _),
    rw forall_swap,
    apply forall₂_congr (λ c g, _),
    symmetry,
    apply equiv.forall_congr ((exp.adjunction A).hom_equiv (fb.obj c) B),
    intro x,
    rw [← adjunction.hom_equiv_naturality_right_symm, equiv.apply_eq_iff_eq, curry_natural_right] },
  { apply and_congr,
    { apply forall₄_congr (λ A B c c', _),
      apply forall_congr (λ g, _),
      symmetry,
      apply equiv.forall_congr ((exp.adjunction A).hom_equiv (fb.obj c') B),
      intro x,
      rw [← adjunction.hom_equiv_naturality_left_symm, equiv.apply_eq_iff_eq, curry_natural_left] },
    { apply forall₃_congr (λ A A' B, _),
      rw forall_swap,
      apply forall₂_congr (λ c g, _),
      symmetry,
      apply equiv.forall_congr ((exp.adjunction A').hom_equiv (fb.obj c) B),
      intro x,
      rw [← adj.hom_equiv_naturality_left_symm, equiv.apply_eq_iff_eq, thing] } }
end

lemma isos34 (adj : fb ⊣ fs) (φ : phis3 fb fs) :
  (∀ (A B c), function.bijective (((equiv34 _ _ adj) φ).1 A B c)) ↔
    (∀ (A B c), function.bijective (φ.1 A B c)) :=
begin
  apply forall₃_congr,
  intros A B c,
  dsimp [equiv34, equiv.Pi_congr_right, equiv.arrow_congr],
  rw [equiv.symm_symm, test', test''],
end

noncomputable def endequiv : phis4 fb fs ≃ pis fb fs :=
begin
  symmetry,
  apply equiv.trans _ (equiv.subtype_subtype_equiv_subtype_inter _ _),
  apply equiv.subtype_congr _ _,
  { refine ⟨λ q, ⟨λ A B c t, q _ _ ≫ t, λ A B B' c h t, by simp⟩, λ q A B, q.1 _ _ _ (𝟙 _), _, _⟩,
    { intros q,
      ext : 2,
      simp },
    { rintro ⟨q, hq⟩,
      ext,
      simp [hq] } },
  intros q,
  dsimp,
  apply and_congr,
  { split,
    { intros k A B c c' h t,
      rw reassoc_of (k A c c' h) },
    { intros k A c c' g,
      simpa using k A _ c c' g (𝟙 _) } },
  { split,
    { intros k A A' B c f t,
      rw reassoc_of (k A A' c f) },
    { intros k A A' c f,
      simpa using k A A' _ c f (𝟙 _) } }
end

lemma isos45 (φ : phis4 fb fs) :
  (∀ (A c), nonempty (is_iso ((endequiv fb fs φ).1 A c))) ↔ (∀ (A B c), function.bijective (φ.1 A B c)) :=
begin
  apply forall_congr (λ A, _),
  rw forall_swap,
  apply forall_congr (λ c, _),
  equiv_rw endequiv fb fs at φ,
  rw ← is_iso_iff_postcomp_bij,
  refl,
end

end frobenius_internal

noncomputable def big_equiv (adj : fb ⊣ fs) : phis fs ≃ pis fb fs :=
begin
  apply equiv.trans (frobenius_internal.equiv12 fs) _,
  refine equiv.trans (frobenius_internal.equiv23 _ _ adj) _,
  refine equiv.trans (frobenius_internal.equiv34 _ _ adj) _,
  apply frobenius_internal.endequiv _ _,
end

noncomputable def frobenius_map (A : C) (B : D) (adj : fb ⊣ fs) :
  fb.obj (fs.obj A ⨯ B) ⟶ A ⨯ fb.obj B :=
prod_comparison fb (fs.obj A) B ≫ limits.prod.map (adj.counit.app A) (𝟙 _)

noncomputable def exp_comparison' (adj : fb ⊣ fs) : phis fs :=
{ val := λ A B,
  begin
    haveI := adj.right_adjoint_preserves_limits,
    apply exp_comparison fs,
  end,
  property :=
  begin
    split,
    { intros A A' B f,
      apply exp_comparison_natural_left },
    { intros A B B' f,
      apply exp_comparison_natural_right }
  end }

lemma big_equiv_comparison (adj : fb ⊣ fs) (A B) :
  (big_equiv _ _ adj (exp_comparison' fb fs adj)).1 A B = frobenius_map _ _ _ _ adj :=
begin
  haveI := adj.right_adjoint_preserves_limits,
  -- dsimp [big_equiv, frobenius_internal.equiv12, equiv.subtype_subtype_equiv_subtype_inter,
  --        equiv.subtype_subtype_equiv_subtype_exists, equiv.subtype_congr_right, exp_comparison'],
  -- dsimp [frobenius_internal.equiv23, equiv.Pi_congr_right, equiv.arrow_congr],
  -- dsimp [frobenius_internal.equiv34, equiv.Pi_congr_right, equiv.arrow_congr],
  -- dsimp [frobenius_internal.endequiv, equiv.subtype_subtype_equiv_subtype_inter,
  --        equiv.subtype_subtype_equiv_subtype_exists, equiv.subtype_congr_right],

  -- change ((adj.hom_equiv (fs.obj A ⨯ B) (A ⨯ fb.obj B)).symm) (cartesian_closed.uncurry (((adj.hom_equiv B ((exp A).obj (A ⨯ fb.obj B))).symm.symm) ((((exp.adjunction A).hom_equiv (fb.obj B) (A ⨯ fb.obj B)).symm.symm) (𝟙 (A ⨯ fb.obj B))) ≫ exp_comparison fs A (A ⨯ fb.obj B))) = frobenius_map fb fs A B adj,
  -- change (adj.hom_equiv _ _).symm (cartesian_closed.uncurry _) = _,
  -- dsimp [frobenius_internal.equiv12, equiv.subtype_subtype_equiv_subtype_inter,
  --        equiv.subtype_subtype_equiv_subtype_exists],
  change (adj.hom_equiv _ _).symm (cartesian_closed.uncurry (adj.hom_equiv _ _ (cartesian_closed.curry _) ≫ _)) = _,
  dsimp [exp_comparison'],
  dsimp [exp_comparison, frobenius_map],
  rw ← curry_natural_left,
  rw uncurry_curry,
  apply prod.hom_ext,
  {
  }

  -- dsimp [big_equiv, exp_comparison', frobenius_internal.equiv12, frobenius_internal.equiv23,
  --        frobenius_internal.equiv34, frobenius_internal.endequiv,
  --        equiv.subtype_subtype_equiv_subtype_inter, equiv.subtype_subtype_equiv_subtype_exists,
  --        equiv.Pi_congr_right, equiv.arrow_congr],
  -- dsimp [equiv.subtype_congr],
  -- dsimp [equiv.trans, equiv.subtype_congr_right],
  -- dsimp [equiv.refl, equiv.subtype_congr],
end


end monoidal
end category_theory
