import linear_algebra.basic

open function lattice

reserve infix `≃ₗ` : 50

universes u v w x y
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type y} {ι : Type x}

namespace linear_map
variables [ring α] [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
variables [module α β] [module α γ] [module α δ]
variables (f : β →ₗ γ)

/-- First Isomorphism Law -/
noncomputable def quot_ker_equiv_range : f.ker.quotient ≃ₗ f.range :=
have hr : ∀ x : f.range, ∃ y, f y = ↑x := λ x, x.2.imp $ λ _, and.right,
let F : f.ker.quotient →ₗ f.range :=
  f.ker.liftq (cod_restrict f.range f $ λ x, ⟨x, trivial, rfl⟩)
    (λ x hx, by simp; apply subtype.coe_ext.2; simpa using hx) in
{ inv_fun    := λx, submodule.quotient.mk (classical.some (hr x)),
  left_inv   := by rintro ⟨x⟩; exact
    (submodule.quotient.eq _).2 (sub_mem_ker_iff.2 $
      classical.some_spec $ hr $ F $ submodule.quotient.mk x),
  right_inv  := λ x : range f, subtype.eq $ classical.some_spec (hr x),
  .. F }

-- p / p ⊓ p' ≃ p ⊔ p' / p'
-- liftq f _ : p / p ⊓ p' → p ⊔ p' / p'
-- f := mkq ∘ of_le _ : p → p ⊔ p' / p'
-- liftq g _ : p ⊔ p' / p' → p / p ⊓ p'
-- g : p ⊔ p' → p / p ⊓ p'
/-- Second Isomorphism Law -/
def union_quotient_equiv_quotient_inter (p p' : submodule α β) :
  (comap p.subtype (p ⊓ p')).quotient ≃ₗ
  (comap (p ⊔ p').subtype p').quotient :=
begin
  let F : (comap p.subtype (p ⊓ p')).quotient →ₗ
          (comap (p ⊔ p').subtype p').quotient :=
    (comap p.subtype (p ⊓ p')).liftq
      ((comap (p ⊔ p').subtype p').mkq.comp (of_le le_sup_left))
      _,
  have hsup : ∀ x : p ⊔ p', ∃ y, y ∈ p ∧ x - y ∈ p',
  { sorry },
  refine {
    inv_fun := quotient.lift_on'
      (comap (p ⊔ p').subtype p')
      (λ x, _) _,
    ..F }
end

.
let sel₁ : s → span (s ∪ t) := λb, ⟨(b : β), subset_span $ or.inl b.2⟩ in
have sel₁_val : ∀b:s, (sel₁ b : β) = b, from assume b, rfl,
have ∀b'∈span (s ∪ t), ∃x:s, ∃y∈t, b' = x.1 + y,
  by simp [span_union, span_eq_of_is_submodule, _inst_4, _inst_5] {contextual := tt},
let sel₂ : span (s ∪ t) → s := λb', classical.some (this b'.1 b'.2) in
have sel₂_spec : ∀b':span (s ∪ t), ∃y∈t, (b' : β) = (sel₂ b' : β) + y,
  from assume b', classical.some_spec (this b'.1 b'.2),
{ to_fun :=
  begin
    intro b,
    fapply quotient.lift_on' b,
    { intro b', exact sel₁ b' },
    { assume b₁ b₂ h,
      change b₁ - b₂ ∈ coe ⁻¹' (s ∩ t) at h,
      apply quotient_module.eq.2, simp * at * }
  end,
  inv_fun :=
  begin
    intro b,
    fapply quotient.lift_on' b,
    { intro b', exact sel₂ b' },
    { intros b₁ b₂ h,
      change b₁ - b₂ ∈ _ at h,
      rcases (sel₂_spec b₁) with ⟨c₁, hc₁, eq_c₁⟩,
      rcases (sel₂_spec b₂) with ⟨c₂, hc₂, eq_c₂⟩,
      have : ((sel₂ b₁ : β) - (sel₂ b₂ : β)) + (c₁ - c₂) ∈ t,
      { simpa [eq_c₁, eq_c₂, add_comm, add_left_comm, add_assoc] using h, },
      have ht : (sel₂ b₁ : β) - (sel₂ b₂ : β) ∈ t,
      { rwa [is_submodule.add_left_iff (is_submodule.sub hc₁ hc₂)] at this },
      have hs : (sel₂ b₁ : β) - (sel₂ b₂ : β) ∈ s,
      { from is_submodule.sub (sel₂ b₁).2 (sel₂ b₂).2 },
      apply quotient_module.eq.2,
      simp * at * }
  end,
  right_inv := assume b', quotient.induction_on' b'
  begin
    intro b, apply quotient_module.eq.2,
    rcases (sel₂_spec b) with ⟨c, hc, eq_c⟩,
    simp [eq_c, hc, is_submodule.neg_iff]
  end,
  left_inv := assume b', @quotient.induction_on _ (quotient_rel _) _ b'
  begin
    intro b, apply quotient_module.eq.2,
    rcases (sel₂_spec (sel₁ b)) with ⟨c, hct, eq⟩,
    have b_eq : (b : β) = c + (sel₂ (sel₁ b)),
    { simpa [sel₁_val] using eq },
    have : (b : β) ∈ s, from b.2,
    have hcs : c ∈ s,
    { rwa [b_eq, is_submodule.add_left_iff (sel₂ (sel₁ b)).mem] at this },
    show (sel₂ (sel₁ b) - b : β) ∈ s ∩ t, { simp [b_eq, hct, hcs, is_submodule.neg_iff] }
  end,
  linear_fun :=  is_linear_map_quotient_lift _ $ (is_linear_map_quotient_mk _).comp $
    is_linear_map_subtype_mk _ (is_submodule.is_linear_map_coe s) _ }

end linear_map