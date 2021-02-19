import category_theory.Fintype
import category_theory.limits.flat
import category_theory.limits.opposites
import data.finset.lattice

universe u

namespace category_theory
open limits

-- Every type is a filtered colimit of finite sets: namely the (directed) union of its finite
-- subsets, which is a directed union

instance {X : Type u} [decidable_eq X] : is_filtered (finset X) := {}.

open_locale classical

@[simps obj map]
def finite_subsets_diagram (X : Type u) : finset X ⥤ Fintype.{u} :=
{ obj := λ x, Fintype.of ((x : set X) : Type u),
  map := λ x y f t, ⟨_, le_of_hom f t.2⟩ }

noncomputable def forward : ind.{u} Fintype.skeleton ⥤ Type u :=
@ind_extend _ _ _ _ Fintype.incl (λ J 𝒥₁ 𝒥₂, _)

-- { obj := λ X, colimit (finite_subsets_diagram X ⋙ ind_embed Fintype),
--   map := λ X Y f,
--   begin
--     apply colimit.desc _ ⟨_, _⟩,
--     have := cocone.whisker,
--     -- apply colimit.desc _ ⟨_, λ (Z : finset _), _ ≫ colimit.ι _ (Z.image f), _⟩,
--     -- apply (ind_embed Fintype).map _,
--     -- intro x,
--     -- dsimp at x,
--     -- refine ⟨f x.1, _⟩,
--     -- rw finset.coe_image,
--     -- apply set.mem_image_of_mem _ x.2,

--   end

-- }

#exit

@[simps obj map]
def finite_subsets_diagram (X : Type u) : finset X ⥤ Type u :=
{ obj := λ x, ((x : set X) : Type u),
  map := λ x y f t, ⟨_, le_of_hom f t.2⟩ }

@[simps]
def finite_subsets_cocone (X : Type u) : cocone (finite_subsets_diagram X) :=
{ X := X, ι := { app := λ Y y, y.1 } }

def finite_subsets_colimit (X : Type u) : is_colimit (finite_subsets_cocone X) :=
{ desc := λ s x, s.ι.app {x} ⟨x, by simp⟩,
  fac' := λ s j,
  begin
    ext ⟨x, hx⟩,
    dsimp,
    have x_le_j : {x} ≤ j,
    { simpa using hx },
    rw ← s.w (hom_of_le x_le_j),
    refl,
  end,
  uniq' := λ s m w,
  begin
    ext x,
    rw ← w,
    refl
  end }

@[simps obj map]
def finite_subsets_diagram' (X : Type u) : finset X ⥤ Fintype.{u} :=
{ obj := λ x, Fintype.of ((x : set X) : Type u),
  map := λ x y f t, ⟨_, le_of_hom f t.2⟩ }

-- def representable (X : Type u) (Q) :
--   (finite_subsets_diagram' X ⋙ Fintype.incl).obj Q ≅ sorry :=
-- begin
--   change Q ≅ _,
-- end

open_locale classical

@[simps]
def finite_subsets_cocone' (X : Type u) :
  cocone (finite_subsets_diagram' X ⋙ yoneda) :=
{ X := Fintype.incl.op ⋙ yoneda.obj X,
  ι := { app := λ S, { app := λ x t u, (t u).1 } } }

-- instance : has_finite_colimits Fintype := by apply_instance

universes v₂ u₂

instance {J : Type u₂} [category.{v₂} J] :
  reflects_colimits_of_shape J Fintype.incl :=
fully_faithful_reflects_colimits_of_shape _

-- instance : has_finite_colimits Fintype :=
-- λ J 𝒥₁ 𝒥₂,
-- { has_colimit := λ F, by exactI
--   has_colimit.mk
--   { cocone :=
--     {

--     }

--   }
-- }

universes w v

-- def quot.rel {J : Type u} [category.{v} J] (F : J ⥤ Type w) :
--   (Σ j, F.obj j) → (Σ j, F.obj j) → Prop :=
-- λ p p', ∃ f : p.1 ⟶ p'.1, p'.2 = F.map f p.2

-- def quot {J : Type u} [category.{v} J] (F : J ⥤ Type w) : Type (max u w) :=
-- @quot (Σ j, F.obj j) (quot.rel F)

noncomputable instance quot.fintype {α : Type*} [fintype α] (r : α → α → Prop) : fintype (quot r) :=
fintype.of_surjective (quot.mk r) quot.exists_rep

noncomputable instance {J : Type u₂} [category.{v₂} J] [fintype J] {K : J ⥤ Fintype.{u₂}} :
  fintype (types.quot (K ⋙ Fintype.incl)) :=
begin
  rw types.quot,
  apply quot.fintype _,
  apply sigma.fintype _,
  apply_instance,
  intro j,
  dsimp,
  apply_instance,
end

noncomputable instance {J : Type u₂} [category.{v₂} J] [fintype J] :
  creates_colimits_of_shape J Fintype.incl.{u₂} :=
{ creates_colimit := λ K,
    creates_colimit_of_fully_faithful_of_iso
      _
      (types.colimit_cocone_is_colimit _)
      ⟨limits.types.quot (K ⋙ Fintype.incl), by apply_instance⟩
      (iso.refl _) }

universes v₁ v₃ u₁ u₃

def reflects_op' {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]
  {J : Type u₃} [category.{v₃} J]
  (F : C ⥤ D) (K : J ⥤ C) [reflects_limit K F] :
  reflects_colimit K.op F.op :=
{ reflects := λ c t,
  begin
    have : is_limit c.unop := is_limit_of_reflects F _,
    apply is_colimit.of_iso_colimit this.op _,
    refine cocones.ext (iso.refl _) _,
    { intro j,
      apply category.comp_id },
    have := F.map_cone_op c.unop,
    -- have := is_limit.op (is_limit_of_reflects F _),
    suffices : is_limit (F.map_cone c.unop).op.unop,
    { refine this.of_iso_limit (cones.ext (iso.refl _) (by tidy)) },
    apply is_colimit.unop,
    apply t.of_iso_colimit _,
    apply _ ≪≫ this.symm,
    apply (cocones.functoriality _ F.op).map_iso _,
    refine cocones.ext (iso.refl _) (by tidy)
  end
}

-- def creates_op' {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]
--   {J : Type u₃} [category.{v₃} J]
--   (F : C ⥤ D) (K : J ⥤ C) [creates_limit K F] :
--   creates_colimit K.op F.op :=
-- {

-- }

-- def creates_op {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]
--   {J : Type u₃} [category.{v₃} J]
--   (F : C ⥤ D)
--   [creates_limits_of_shape J F] : creates_colimits_of_shape Jᵒᵖ F.op :=
-- { creates_colimit := λ K,
--   begin
--     have := functor.unop K,
--     letI : creates_limit K.unop F := infer_instance,

--   end

-- }

instance : has_finite_colimits Fintype.{u₂} :=
λ J 𝒥₁ 𝒥₂,
  by exactI has_colimits_of_shape_of_has_colimits_of_shape_creates_colimits_of_shape Fintype.incl

-- (decidable_eq_obj : decidable_eq J . tactic.apply_instance)
-- (fintype_obj : fintype J . tactic.apply_instance)
-- (decidable_eq_hom : Π (j j' : J), decidable_eq (j ⟶ j') . tactic.apply_instance)
-- (fintype_hom : Π (j j' : J), fintype (j ⟶ j') . tactic.apply_instance)

instance {J : Type u₂} [category.{v₂} J] [fcj : fin_category J] : fin_category Jᵒᵖ :=
{ decidable_eq_obj := λ x y, decidable_of_decidable_of_iff infer_instance opposite.unop_injective.eq_iff,
  fintype_obj :=
    { elems := finset.map ⟨opposite.op, opposite.op_injective⟩ _,
      complete := λ x, finset.mem_map_of_mem _ (fintype.complete x.unop) },
  decidable_eq_hom := λ x y f g, decidable_of_decidable_of_iff infer_instance has_hom.hom.unop_inj.eq_iff,
  fintype_hom := λ X Y,
  { elems := (@fin_category.fintype_hom J _ fcj Y.unop X.unop).elems.map ⟨has_hom.hom.op, has_hom.hom.op_inj⟩,
    complete := λ f, finset.mem_map_of_mem _ (fintype.complete f.unop) } }

-- lemma thing (X : Type u) : is_set_flat (Fintype.incl.{u}.op ⋙ yoneda.obj X) :=
-- begin
--   apply set_flat_of_preserves_finite_limits _,
--   { introsI J 𝒥₁ 𝒥₂,
--     exact has_limits_of_shape_op_of_has_colimits_of_shape },
--   introsI J 𝒥₁ 𝒥₂,
--   letI : creates_limits_of_shape J Fintype.incl.{u}.op,
--   {

--   },
--   letI : has_limits_of_shape J (Type u)ᵒᵖ := has_limits_of_shape_op_of_has_colimits_of_shape,
--   apply limits.comp_preserves_limits_of_shape,
-- end

open opposite

@[simp] lemma Fintype.types_comp_apply {X Y Z : Fintype} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.α) :
  (f ≫ g) x = g (f x) := rfl

-- #exit
noncomputable def finite_subsets_colimit' (X : Type u) :
  is_colimit (finite_subsets_cocone' X) :=
{ desc := λ s,
  { app := λ S (f : S.unop.α → X), (s.ι.app (finset.univ.image f)).app S (λ t, ⟨f t, by simp⟩),
    naturality' := λ S₁ S₂ g,
    begin
      ext (f : S₁.unop.α → X),
      dsimp,
      have leq : (finset.univ : finset S₂.unop.α).image (Fintype.incl.map g.unop ≫ f : S₂.unop.α → X) ≤ (finset.univ : finset S₁.unop.α).image f,
      { intros x hx,
        simp only [finset.mem_univ, function.comp_app, exists_prop_of_true, finset.mem_image] at hx,
        rcases hx with ⟨x, rfl⟩,
        simp },
      have := s.w (hom_of_le leq),
      rw ←congr_app this S₂,
      have q := (s.ι.app (finset.univ.image f)).naturality g,
      replace q := congr_fun q,
      dsimp at q,
      rw ← q,
      refl,
    end },
  fac' := λ s j,
  begin
    ext q f,
    dsimp [finite_subsets_cocone'],
    dsimp at f,
    have : (finset.image (λ (u : (unop q).α), (f u).1) finset.univ : finset X) ≤ j,
    { intros x hx,
      simp only [finset.mem_univ, exists_prop_of_true, finset.mem_image, subtype.val_eq_coe] at hx,
      rcases hx with ⟨x, rfl⟩,
      apply (f x).2 },
    have z := s.w (hom_of_le this),
    dsimp at z,
    rw ← z,
    dsimp,
    congr' 1,
    ext1,
    dsimp [types_comp_apply, finite_subsets_diagram'],
  end,
  uniq' := sorry
}

#exit

instance {X : Type u} [decidable_eq X] : is_filtered (finset X) := {}.

def type_to_ind_fintype : Type u ⥤ ind.{u} Fintype.{u} :=
{ obj := λ X, ⟨_,
    is_set_flat'_of_filtered_colimit_of_representables
      (finset X)
      (finite_subsets_diagram' X) _ _⟩,

}

-- def ind_fintype_to_type : ind.{u} Fintype.{u} ⥤ Type u :=
-- ind_extension _

def ind_fintype_equiv_type : ind Fintype.{u} ≌ Type u :=
begin

end

end category_theory
