import general_nonsense
import variety
import category_theory.concrete_category.bundled_hom

noncomputable theory
open category_theory category_theory.limits

variable (σ : signature)

instance struct_bundled_hom : bundled_hom (λ A B [σ A] [σ B], by exactI σ.hom A B) :=
{ to_fun := λ A B [σ A] [σ B] f, by exactI f,
  id := λ A [σ A], by exactI σ.id_hom A,
  comp := λ A B C [σ A] [σ B] [σ C] f g, by exactI f.comp g }

def Struct := bundled (struct σ)

attribute [derive [has_coe_to_sort, large_category, concrete_category]] Struct

instance (A : Struct σ) : struct σ ↥A := A.str

variables {σ} {J : Type} [small_category J] [is_filtered J] (F : J ⥤ Struct σ)

def cl' : Type := cl (F ⋙ forget (Struct σ))

/-- the structure on the colimit type -/
@[simps] instance : struct σ (cl' F) :=
{ function := λ n s,
  begin
    refine _ ∘ cl_equiv _,
    refine cl_desc _ ⟨_, _, _⟩,
    { exact λ j v, cl_ι (F ⋙ forget (Struct σ)) j (s.app v : F.obj j) },
    { intros j j' f,
      ext,
      simp only [forget_map_eq_coe, functor.comp_map, coyoneda_obj_map, functor.const.obj_map, types_comp_apply, types_id_apply],
      erw ←signature.hom.app_comm,
      exact congr_fun (colimit.w (F ⋙ forget (Struct σ)) f) (s.app x : F.obj j), }
  end }

/-- the structue on the colimit turns the inclusions into structure homs -/
def ι_hom (j : J) : σ.hom (F.obj j) (cl' F) :=
{ to_fun := cl_ι (F ⋙ forget (Struct σ)) j,
  app_comm' := begin
    intros n s v,
    simp only [cl_ι, cl_equiv_comm, cl_desc, signature.symbol.app, types.colimit.ι_desc_apply,
      function.comp_app, cl'.struct_function],
  end }

variables (T : theory σ) [∀ j, lawful_struct T (F.obj j)]

/-- if all the components are lawful, then so is the colimit -/
instance : lawful_struct T (cl' F) :=
{ lhs_eq_rhs :=
  begin
    intros a ha,
    erw (cl_equiv (F ⋙ forget _)).symm.surjective.forall,
    apply congr_fun,
    apply ext_fun,
    intros j x,
    dsimp at x,
    have := cl_equiv_comm (F ⋙ forget _) j x,
    rw equiv.apply_eq_iff_eq_symm_apply at this,
    rw ←this,
    clear this,
    change eval σ (ι_hom F j ∘ x) a.lhs = eval σ (ι_hom F j ∘ x) a.rhs,
    rw ←eval_naturality,
    change ι_hom F j _ = ι_hom F j _,
    exact congr_arg _ (lawful_struct.lhs_eq_rhs a ha _),
  end }
