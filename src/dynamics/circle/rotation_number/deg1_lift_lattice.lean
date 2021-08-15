
def conj_neg : circle_deg1_lift ≃* circle_deg1_lift :=
mul_equiv.of_involutive
  { to_fun := λ f, ⟨λ x, -f (-x), λ x y h, neg_le_neg $ f.monotone (neg_le_neg h), λ x,
      by rw [neg_add, ← sub_eq_add_neg, f.map_sub_one, neg_sub, sub_eq_neg_add]⟩,
    map_one' := ext $ λ x, by simp,
    map_mul' := λ f g, ext $ λ x, by simp } $
  λ f, ext $ λ x, by simp

def conj_neg_order_iso : circle_deg1_lift ≃o order_dual circle_deg1_lift :=
{ to_equiv := conj_neg.to_equiv.trans order_dual.to_dual,
  map_rel_iff' := λ f g, ⟨λ H, (equiv.neg _).surjective.forall.2 $
    λ x, neg_le_neg_iff.1 (H x), λ H x, neg_le_neg (H (-x))⟩ }

/-- An auxiliary definition for `circle_deg1_lift.has_Sup`. -/
noncomputable def Sup_aux (s : set circle_deg1_lift) (Hne : s.nonempty)
  (H : ∀ x, bdd_above ((λ f : circle_deg1_lift, f x) '' s)) :
  circle_deg1_lift :=
{ to_fun := λ x, ⨆ f : s, f x,
  monotone' := λ x y h, csupr_le_csupr (by simpa only [image_eq_range] using H y)
    (λ f, f.1.monotone h),
  map_add_one' := λ x,
    begin
      haveI := Hne.to_subtype,
      simp only [coe_fn_coe_base, map_add_one, image_eq_range] at H ⊢,
      exact (csupr_add (H x) _).symm
    end }

lemma le_Sup_aux (s : set circle_deg1_lift) (hf : f ∈ s)
  (H : ∀ x, bdd_above ((λ f : circle_deg1_lift, f x) '' s)) :
  f ≤ Sup_aux s ⟨f, hf⟩ H :=
λ x, by { have := H x, rw image_eq_range at this, exact le_csupr this ⟨f, hf⟩ }

lemma bdd_above_tfae (s : set circle_deg1_lift) :
  tfae [bdd_above s,
    ∀ x, bdd_above ((λ f : circle_deg1_lift, f x - x) '' s),
    ∀ x, bdd_above ((λ f : circle_deg1_lift, f x) '' s),
    ∃ x, bdd_above ((λ f : circle_deg1_lift, f x - x) '' s),
    ∃ x, bdd_above ((λ f : circle_deg1_lift, f x) '' s)] :=
begin
  tfae_have : 1 ↔ 3,
  { refine ⟨λ H x, (monotone_apply x).map_bdd_above H, λ H, _⟩,
    rcases s.eq_empty_or_nonempty with rfl|hne, { exact bdd_above_empty },
    exact ⟨Sup_aux s hne H, λ f hf, f.le_Sup_aux _ hf _⟩ },
  have : ∀ x, bdd_above ((λ f : circle_deg1_lift, f x) '' s) ↔
    bdd_above ((λ f : circle_deg1_lift, f x - x) '' s),
  { intro x,
    rw [← (order_iso.add_right (-x)).bdd_above_image, image_image],
    refl },
  tfae_have : 3 ↔ 2, from forall_congr this,
  tfae_have : 5 ↔ 4, from exists_congr this,
  tfae_have : 3 ↔ 5,
  { simp only [image_eq_range],
    exact forall_bdd_above_iff_exists_of_mono_of_map_add_le zero_lt_one (λ f, f.1.monotone)
      (monotone_id.add_const 1) (λ f x, (f.1.map_add_one x).le) },
  tfae_finish
end

noncomputable instance : conditionally_complete_lattice circle_deg1_lift :=
conditionally_complete_lattice_of_is_lub_of_rel_iso
  (λ s hne hbdd, _) 1 conj_neg_order_iso

noncomputable instance : has_Sup circle_deg1_lift :=
⟨λ s, if hs : s.nonempty ∧ bdd_above s
  then Sup_aux s hs.1 (((bdd_above_tfae s).out 0 2).mp hs.2) else 1⟩

lemma Sup_apply (s : set circle_deg1_lift) (hne : s.nonempty) (hbdd : bdd_above s) (x : ℝ) :
  Sup s x = ⨆ f : s, f x :=
by { dsimp only [circle_deg1_lift.has_Sup], rw dif_pos (and.intro hne hbdd), refl }

private lemma Sup_le (s : set circle_deg1_lift) (hne : s.nonempty) (hle : ∀ g ∈ s, g ≤ f) :
  Sup s ≤ f :=
have hbdd : bdd_above s := ⟨f, hle⟩,
λ x, by { rw Sup_apply s hne hbdd, haveI := hne.to_subtype, exact csupr_le (λ g, hle g g.2 x) }

/-
{ Inf := λ s, conj_neg (Sup $ conj_neg ⁻¹' s),
  le_cSup := λ s f hbdd hfs x, by { haveI : nonempty s := ⟨⟨f, hfs⟩⟩,
    exact (le_csupr _ _).trans_eq (Sup_apply _ _ _ _).symm },
.. circle_deg1_lift.lattice, .. circle_deg1_lift.has_Sup }-/
