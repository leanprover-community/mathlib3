import category_theory.limits.filtered_colimit_commutes_finite_limit2
import category_theory.elements
import category_theory.limits.elements
import category_theory.functor_category
import category_theory.limits.preserves.limits
import category_theory.limits.yoneda
import category_theory.limits.creates
import category_theory.adjunction.limits

namespace category_theory
open limits opposite

universes w v₁ v₂ u₁ u₂

variables (J : Type v₁) [category.{v₂} J]
variables {C : Type u₁} [category.{v₁} C]

-- set_option pp.universes true

@[simps {rhs_md := semireducible}]
def my_functor (F : C ⥤ Type v₁) : F.elementsᵒᵖ ⥤ C ⥤ Type v₁ :=
functor.op (category_of_elements.π F) ⋙ coyoneda

@[simps]
def alt_cocone (F : C ⥤ Type v₁) :
  cocone (my_functor F) :=
{ X := F,
  ι :=
  { app := λ p,
    { app := λ Y f, F.map f p.unop.2,
      naturality' := λ Y₁ Y₂ g,
      begin
        ext f,
        apply functor_to_types.map_comp_apply F f g,
      end },
    naturality' := λ p₁ p₂ α,
    begin
      ext X x,
      change F.map (α.unop.1 ≫ x) _ = F.map _ _,
      rw [functor_to_types.map_comp_apply F, α.unop.2],
    end } }


namespace flat_finite_limits

variables (F : C ⥤ Type v₁) {J} (K : J ⥤ C) (c : cone K) (t : is_limit c)

@[simps {rhs_md := semireducible}]
def Γ : F.elementsᵒᵖ ⥤ J ⥤ Type v₁ :=
my_functor F ⋙ (whiskering_left J C _).obj K

def cj (q : F.elementsᵒᵖ) : cone ((Γ F K).obj q) :=
((my_functor F).obj q).map_cone c

def ck (j : J) : cocone ((Γ F K).flip.obj j) :=
((evaluation C (Type v₁)).obj (K.obj j)).map_cocone (alt_cocone F)

def tj (q : F.elementsᵒᵖ) (t : is_limit c) : is_limit (cj F K c q) :=
begin
  apply is_limit_of_preserves (coyoneda.obj (op (unop q).fst)) t,
end

def alt_cocone_eval (v : C) :
  is_colimit (((evaluation C (Type v₁)).obj v).map_cocone (alt_cocone F)) :=
{ desc := λ s q, s.ι.app (op ⟨v, q⟩) (𝟙 _ ),
  fac' := λ s q,
  begin
    op_induction q,
    cases q with w hw,
    ext (f : w ⟶ v),
    let w' : F.elementsᵒᵖ := op ⟨w, hw⟩,
    let v' : F.elementsᵒᵖ := op ⟨v, F.map f hw⟩,
    let f' : v' ⟶ w' := has_hom.hom.op ⟨f, rfl⟩,
    change s.ι.app v' _ = _,
    rw ←s.w f',
    dsimp,
    simp,
  end,
  uniq' := λ s m w,
  begin
    ext,
    rw ← w,
    dsimp,
    simp
  end }

def tk (j : J) : is_colimit (ck F K j) :=
begin
  change is_colimit (functor.map_cocone _ _),
  apply alt_cocone_eval,
end

def c₁ : cocone (cones_to_functor (λ q, tj F K c q t)) :=
begin
  let : my_functor F ⋙ (evaluation C (Type v₁)).obj c.X ≅ cones_to_functor (λ (q : (F.elements)ᵒᵖ), tj F K c q t),
  { refine nat_iso.of_components (λ q, iso.refl _) _,
    intros q₁ q₂ f,
    -- ext1 (x : (unop q₁).1 ⟶ _),
    -- dsimp at x,
    dsimp,
    rw category.comp_id,
    rw category.id_comp,
    apply is_limit.hom_ext (tj F K c q₂ t),
    intro j,
    rw is_limit.map_π,
    ext1 (x : (unop q₁).1 ⟶ _),
    dsimp [my_functor, cj],
    rw category.assoc },
  apply (cocones.precompose this.inv).obj _,
  apply ((evaluation C (Type v₁)).obj c.X).map_cocone (alt_cocone F)
end

noncomputable def c₂ : cone (cocones_to_functor (tk F K)) :=
limit.cone _

def t₁ : is_colimit (c₁ F K c t) :=
begin
  change is_colimit ((cocones.precompose _).obj _),
  apply (is_colimit.precompose_inv_equiv _ _).symm _,
  apply alt_cocone_eval
end

noncomputable def t₂ : is_limit (c₂ F K) :=
limit.is_limit _
-- is_limit_of_preserves (coyoneda.obj (op (unop q).fst)) t

noncomputable def my_thm
  (J : Type v₁) [category.{v₂} J] [fin_category J]
  {C : Type u₁} [category.{v₁} C]
  (F : C ⥤ Type v₁) (hF : is_filtered F.elementsᵒᵖ) :
  preserves_limits_of_shape J F :=
begin
  split,
  intro K,
  split,
  intros c t,
  let Γ' := Γ F K,
  let tj : Π (q : F.elementsᵒᵖ), is_limit (cj F K c q) := λ q, tj F K c q t,
  let q : cocones_to_functor (tk F K) ≅ K ⋙ F,
  { refine nat_iso.of_components (λ X, iso.refl _) _,
    intros X Y f,
    dsimp,
    rw [category.id_comp, category.comp_id],
    apply (tk F K X).hom_ext,
    intro j,
    rw is_colimit.ι_map,
    ext q,
    dsimp [alt_cocone, my_functor, ck],
    simp, },
  let i₂ := has_limit.iso_of_nat_iso q,

  let i₃ : F.obj c.X ≅ limit (K ⋙ F) :=
    filtered_colimit_finite_limit_iso Γ' tj (tk F K) (t₁ F K c t) (t₂ F K) ≪≫ i₂,
  apply is_limit.of_point_iso (limit.is_limit (K ⋙ F)),
  dsimp,
  have : limit.lift (K ⋙ F) (F.map_cone c) = i₃.hom,
  { apply limit.hom_ext,
    intro j,
    rw limit.lift_π,
    dsimp,
    change _ = (_ ≫ _) ≫ _,
    rw category.assoc,
    simp only [iso.refl_hom, category.comp_id, nat_iso.of_components.hom_app,
      has_limit.iso_of_nat_iso_hom_π],
    apply (t₁ F K c t).hom_ext,
    intro k,
    change _ = _ ≫ _ ≫ (c₂ F K).π.app j,
    rw ι_colimit_to_limit_π,
    ext q,
    dsimp [cj, ck,
           category_theory.flat_finite_limits.cj, c₁,
           category_theory.flat_finite_limits.c₁],
    simp, },
  rw this,
  apply is_iso.of_iso,
end

end flat_finite_limits

-- #exit

def is_set_flat (F : C ⥤ Type w) := is_filtered F.elementsᵒᵖ

lemma representable_is_set_flat (X : Cᵒᵖ) : is_set_flat (coyoneda.obj X) :=
is_filtered.of_terminal (terminal_op_of_initial (is_initial X.unop))

variable (C)

@[derive category]
def ind := {F : Cᵒᵖ ⥤ Type w // is_set_flat F}

@[derive [full, faithful, reflects_isomorphisms]]
def ind_to_presheaf : ind C ⥤ (Cᵒᵖ ⥤ Type v₁) := full_subcategory_inclusion _

@[simps]
def right (c : C) : Type v₁ ⥤ (C ⥤ Type v₁) :=
{ obj := λ X,
  { obj := λ d, (d ⟶ c) → X,
    map := λ d d' f g h, g (f ≫ h) },
  map := λ X Y f,
  { app := λ Z g h, f (g h) } }

def adj (c : C) : (evaluation _ (Type v₁)).obj c ⊣ right C c :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ F Y,
  { to_fun := λ f,
    { app := λ X x g, f (F.map g x),
      naturality' := λ X Y g,
      begin
        ext t,
        dsimp,
        rw functor_to_types.map_comp_apply,
      end },
    inv_fun := λ f x, f.app c x (𝟙 _),
    left_inv := λ f,
    begin
      ext,
      simp,
    end,
    right_inv := λ f,
    begin
      ext t g,
      dsimp,
      rw functor_to_types.naturality,
      dsimp,
      simp,
    end } }

-- #exit

-- def adj (c : C) : is_left_adjoint ((evaluation _ (Type u₁)).obj c)


def six_three_six {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D] [is_filtered D]
  (H : D ⥤ C ⥤ Type v₁)
  {c : cocone H}
  (t : is_colimit c)
  (t' : ∀ x, is_colimit (((evaluation C (Type v₁)).obj x).map_cocone c))
  (hD : ∀ d, is_set_flat (H.obj d)) : is_set_flat c.X :=
{ nonempty :=
  begin
    haveI : nonempty D := is_filtered.nonempty,
    inhabit D,
    obtain ⟨t⟩ := (hD (default D)).nonempty,
    refine ⟨op ⟨(unop t).1, (c.ι.app (default D)).app _ (unop t).2⟩⟩,
  end,
  cocone_objs :=
  begin
    intros Aa Bb,
    op_induction Aa,
    op_induction Bb,
    cases Aa with A a,
    cases Bb with B b,
    have : is_colimit (((evaluation C (Type v₁)).obj A).map_cocone c),
    { apply is_colimit_of_preserves ((evaluation C (Type v₁)).obj A) t,

    },
    rcases types.jointly_surjective _ (t' A) a with ⟨d, a' : (H.obj _).obj _, ha' : (c.ι.app d).app A a' = a⟩,
    rcases types.jointly_surjective _ (t' B) b with ⟨d', (b' : (H.obj _).obj _), hb' : (c.ι.app d').app B b' = b⟩,
    rcases is_filtered_or_empty.cocone_objs d d' with ⟨d'', f, g, ⟨⟩⟩,
    let a'' := (H.map f).app A a',
    have ha'' : (c.ι.app d'').app A a'' = a,
    { rw ←c.w f at ha',
      apply ha' },
    let b'' := (H.map g).app B b',
    have hb'' : (c.ι.app d'').app B b'' = b,
    { rw ←c.w g at hb',
      apply hb' },
    clear_value a'' b'',
    clear ha' hb' a' b' f g d d',
    subst ha'',
    subst hb'',
    rename d'' d,
    rename a'' a',
    rename b'' b',
    have cof := (hD d).cocone_objs,
    rcases cof (op ⟨_, a'⟩) (op ⟨_, b'⟩) with ⟨Cc, u, v, ⟨⟩⟩,

    -- Manually do the op_induction/cases on Cc
    let C' := Cc.unop.1,
    let c' : (H.obj _).obj C' := Cc.unop.2,
    have : Cc = op ⟨C', c'⟩,
    { simp },
    clear_value C' c',
    subst this,

    have ha' : (H.obj _).map u.unop.1 c' = a' := u.unop.2,
    have hb' : (H.obj _).map v.unop.1 c' = b' := v.unop.2,
    have : c.X.obj C' := (c.ι.app d).app C' c',
    refine ⟨op ⟨_, (c.ι.app d).app C' c'⟩,
            has_hom.hom.op ⟨u.unop.1, _⟩,
            has_hom.hom.op ⟨v.unop.1, _⟩, ⟨⟩⟩,
    { change ((c.ι.app d).app C' ≫ c.X.map u.unop.1) c' = (c.ι.app d).app A a',
      have : _ = (c.ι.app d).app C' ≫ c.X.map u.unop.val := (c.ι.app d).naturality u.unop.1,
      rw ← this,
      change (c.ι.app d).app A ((H.obj d).map u.unop.1 c') = (c.ι.app d).app A a',
      apply congr_arg _ ha' },
    { change ((c.ι.app d).app C' ≫ c.X.map v.unop.1) c' = (c.ι.app d).app B b',
      have : _ = (c.ι.app d).app C' ≫ c.X.map v.unop.val := (c.ι.app d).naturality v.unop.1,
      rw ← this,
      change (c.ι.app d).app B ((H.obj d).map v.unop.1 c') = (c.ι.app d).app B b',
      apply congr_arg _ hb' },
  end,
  cocone_maps :=
  begin
    intros Bb Aa u' v',
    let A := Aa.unop.1,
    let a : c.X.obj A := Aa.unop.2,
    let B := Bb.unop.1,
    let b : c.X.obj B := Bb.unop.2,
    have : Aa = op ⟨A, a⟩, simp,
    have : Bb = op ⟨B, b⟩, simp,
    clear_value A a B b,
    subst Aa,
    subst Bb,
    let u : A ⟶ B := u'.unop.1,
    let v : A ⟶ B := v'.unop.1,
    have hu : c.X.map u a = b := u'.unop.2,
    have hv : c.X.map v a = b := v'.unop.2,

    -- let t' : is_colimit (((evaluation C _).obj A).map_cocone c) := is_colimit_of_preserves _ t,
    rcases types.jointly_surjective _ (t' A) a with ⟨d, a' : (H.obj _).obj _, ha' : (c.ι.app d).app A a' = a⟩,
    -- let t'' : is_colimit (((evaluation C _).obj B).map_cocone c) := is_colimit_of_preserves _ t,
    rcases types.jointly_surjective _ (t' B) b with ⟨d', (b' : (H.obj _).obj _), hb' : (c.ι.app d').app B b' = b⟩,
    rcases is_filtered_or_empty.cocone_objs d d' with ⟨d'', f, g, ⟨⟩⟩,
    let a'' := (H.map f).app A a',
    have ha'' : (c.ι.app d'').app A a'' = a,
    { rw ←c.w f at ha',
      apply ha' },
    let b'' := (H.map g).app B b',
    have hb'' : (c.ι.app d'').app B b'' = b,
    { rw ←c.w g at hb',
      apply hb' },
    clear_value a'' b'',
    clear' a' b' ha' hb' f g d d',
    rename [d'' d, a'' a', b'' b', ha'' ha', hb'' hb'],
    have q : ((H.obj d).map u ≫ (c.ι.app d).app B) a' = ((H.obj d).map v ≫ (c.ι.app d).app B) a',
    { rw [(c.ι.app d).naturality, (c.ι.app d).naturality, types_comp_apply, types_comp_apply, ha'],
      change c.X.map u a = c.X.map v a,
      rw [hu, hv] },
    rw [types_comp_apply, types_comp_apply] at q,
    -- have : (c.ι.app d).app _ = _,
    have : (c.ι.app d).app B ((H.obj d).map u a') = (c.ι.app d).app B ((H.obj d).map v a') ↔ _ :=
      types.filtered_colimit.is_colimit_eq_iff' _ (t' B),
    dsimp at this,
    rw this at q,
    rcases q with ⟨d', dh, q⟩,
    let b'' := (H.map dh).app B ((H.obj d).map u a'),
    have hua : (H.obj d').map u ((H.map dh).app _ a') = b'',
    { rw ←functor_to_types.naturality },
    have hva : (H.obj d').map v ((H.map dh).app _ a') = b'',
    { rw ←functor_to_types.naturality, rw ←q },
    let A' : (H.obj d').elementsᵒᵖ := op ⟨A, (H.map dh).app _ a'⟩,
    let B' : (H.obj d').elementsᵒᵖ := op ⟨B, b''⟩,
    let u' : B' ⟶ A' := has_hom.hom.op ⟨u, hua⟩,
    let v' : B' ⟶ A' := has_hom.hom.op ⟨v, hva⟩,
    haveI : is_filtered _ := hD d',
    let Cc := is_filtered.coeq u' v',
    let w : A' ⟶ Cc := is_filtered.coeq_hom u' v',
    refine ⟨op ⟨Cc.unop.1, (c.ι.app _).app _ Cc.unop.2⟩, _, _⟩,
    refine has_hom.hom.op ⟨w.unop.1, _⟩,
    change ((c.ι.app d').app _ ≫ c.X.map w.unop.1) _ = a,
    erw ←(c.ι.app d').naturality,
    rw types_comp_apply,
    rw w.unop.2,
    change ((H.map dh ≫ c.ι.app d').app A) a' = a,
    rw c.w, apply ha',
    apply has_hom.hom.unop_inj,
    ext1,
    change w.unop.1 ≫ u = w.unop.1 ≫ v,
    have := is_filtered.coeq_condition u' v',
    have := congr_arg has_hom.hom.unop this,
    rw subtype.ext_iff_val at this,
    exact this,
  end }.

instance {C : Type u₁} [category.{v₁} C] {J : Type u₂} [category.{v₂} J]  :
  reflects_colimits_of_shape J (ind_to_presheaf C) :=
fully_faithful_reflects_colimits_of_shape (ind_to_presheaf C)

-- It *should* be possible to generalise the universe levels here
instance {C : Type u₁} [small_category C] {J : Type u₁} [small_category J] [is_filtered J] :
  creates_colimits_of_shape J (ind_to_presheaf C) :=
{ creates_colimit := λ K,
  { lifts := λ c t,
    { lifted_cocone :=
      { X := ⟨c.X, six_three_six (K ⋙ ind_to_presheaf _) _ (λ j, (K.obj j).2)⟩,
        ι :=
        { app := λ j, c.ι.app j,
          naturality' := λ j₁ j₂ f, c.ι.naturality f } },
      valid_lift :=
      begin
        refine cocones.ext (iso.refl _) _,
        intro j,
        apply category.comp_id
      end } } }

/-- If `C` is small, then the category of ind-objects has filtered colimits. -/
-- TODO: Figure out how much we can generalise the universes here.
instance {C : Type u₁} [small_category C] {J : Type u₁} [small_category J] [is_filtered J] :
  has_colimits_of_shape J (ind C) :=
has_colimits_of_shape_of_has_colimits_of_shape_creates_colimits_of_shape (ind_to_presheaf C)

-- set_option pp.universes true


-- def six_three_six {C : Type u₁} [category.{v₁} C] {D : Type u₁} [small_category D] [is_filtered D]
--   (H : D ⥤ C ⥤ Type u₁)
--   {c : cocone H} (t : is_colimit c)
--   (hD : ∀ d, is_set_flat (H.obj d)) : is_set_flat c.X :=

def is_set_flat_of_filtered_colimit_of_representables
  {C : Type u₁} [category.{u₁} C]
  {D : Type u₁} [category.{v₂} D]
  (ψ : D ⥤ Cᵒᵖ)
  [is_filtered D]
  (c : cocone (ψ ⋙ coyoneda))
  (t : is_colimit c) :
  is_set_flat c.X :=
six_three_six (ψ ⋙ coyoneda) t (λ d, representable_is_set_flat _)

-- { nonempty :=
--   begin
--     haveI : nonempty D := is_filtered.nonempty,
--     inhabit D,
--     refine ⟨op ⟨op (ψ.obj (default D)), (c.ι.app (default D)).app _ (𝟙 _)⟩⟩,
--   end,
--   cocone_objs :=
--   begin
--     intros Aa Aa',
--     op_induction Aa,
--     op_induction Aa',
--     cases Aa with A a,
--     cases Aa' with A' a',

--   end,
--   cocone_maps := _


-- }

end category_theory
