import category_theory.sites.sheaf
import category_theory.flat_functors
import category_theory.sites.cover_preserving

universes v u

namespace category_theory
section cover_dense
variables {C : Type*} [category C] {D : Type*} [category D] {E : Type*} [category E]
variables (J : grothendieck_topology C) (K : grothendieck_topology D)
variables {L : grothendieck_topology E}

structure factors_through_image_obj (G : C ⥤ D) {V U : D} (f : V ⟶ U) :=
(obj : C) (lift : V ⟶ G.obj obj) (map : G.obj obj ⟶ U) (fac : f = lift ≫ map)

def all_factors_through_image_obj (G : C ⥤ D) {U : D} (R : presieve U) :=
∀ ⦃V⦄ {f : V ⟶ U} (hf : R f), factors_through_image_obj G f

structure factors_through_image_obj_and_map (G : C ⥤ D) {V : D} {U : D} (f : V ⟶ U)
  (O : finset (structured_arrow U G)) extends factors_through_image_obj G f :=
(premap : ∀ (f : O), obj ⟶ f.val.right)
(map_fac : ∀ (f : O), G.map (premap f) = map ≫ f.val.hom)

def all_factors_through_image_obj_and_map (G : C ⥤ D) {U : D} (R : presieve U) (O) :=
∀ ⦃V⦄ {f : V ⟶ U} (hf : R f), factors_through_image_obj_and_map G f O

def all_through_both_to_through_obj {G : C ⥤ D} {U} {R : presieve U} {O}
  (H : all_factors_through_image_obj_and_map G R O) : all_factors_through_image_obj G R :=
λ V f hf, (H hf).to_factors_through_image_obj

lemma factors_through_image_obj_and_map.map_fac' {G : C ⥤ D} {V : D} {U : D} {f : V ⟶ U}
  {O : finset (structured_arrow U G)} (H : factors_through_image_obj_and_map G f O) (f' : O) :
  H.lift ≫ G.map (H.premap f') = f ≫ f'.val.hom :=
begin
  rw [H.map_fac f', ← category.assoc],
  congr,
  exact H.fac.symm
end

noncomputable
def through_obj_to_through_both {G : C ⥤ D} {U V} {f : V ⟶ U}
  {O : finset (structured_arrow U G)} (H : factors_through_image_obj G f)
  (H' : ∀ (f : O), ∃ (g : H.obj ⟶ f.val.right), G.map g = H.map ≫ f.val.hom) :
  factors_through_image_obj_and_map G f O :=
{ premap := λ f, (H' f).some, map_fac := λ f, (H' f).some_spec, ..H}

structure cover_dense (J : grothendieck_topology C) (K : grothendieck_topology D) (G : C ⥤ D) :=
(obj          : ∀ (U : D), K U)
(obj_fac      : ∀ (U : D), all_factors_through_image_obj G (obj U))
(map          : ∀ {U V : C} (f : G.obj U ⟶ G.obj V), J U)
(map_fac_map  : ∀ {U V W} (f : G.obj U ⟶ G.obj V) {g : W ⟶ U} (hg : map f g), W ⟶ V)
(map_fac      : ∀ {U V W} (f : G.obj U ⟶ G.obj V) {g : W ⟶ U} (hg : map f g),
  G.map (map_fac_map f hg) = G.map g ≫ f)

def cover_dense_mk_of_full (J : grothendieck_topology C) (K : grothendieck_topology D) (G : C ⥤ D)
  [full G] (create : ∀ (U : D), Σ (S : K U), all_factors_through_image_obj G S) :
  cover_dense J K G :=
{ obj          := λ U, (create U).1,
  obj_fac      := λ U, (create U).2,
  map          := λ U V f, ⟨_, J.top_mem U⟩,
  map_fac_map  := λ U V W f g hg, g ≫ G.preimage f,
  map_fac      := λ U V W f g hg, by simp }

section factor_cover_sieve
variables {J} {K} {G : C ⥤ D} (H : cover_dense J K G) (H' : cover_preserving J K G)
variables {X : D} {Y : C} (f : X ⟶ G.obj Y) (S : K X) (HS : all_factors_through_image_obj G S)

def cover_dense.obj' (H : cover_dense J K G) (U : D) : K U :=
⟨⟨λ Y f, nonempty (factors_through_image_obj G f), λ Y Z f ⟨hf⟩ g,
  ⟨{ obj := hf.obj, lift := g ≫ hf.lift, map := hf.map, fac := by rw [category.assoc, ←hf.fac] }⟩⟩,
    K.superset_covering (λ V f hf, ⟨H.obj_fac U hf⟩) (H.obj U).property⟩

noncomputable
def cover_dense.obj_fac' (H : cover_dense J K G) (U : D) :
  all_factors_through_image_obj G (H.obj' U) := λ V f hf, hf.some

lemma cover_dense.obj'_in (H : cover_dense J K G) {U : D} {V : C} (f : G.obj V ⟶ U) :
  H.obj' U f := ⟨{ obj := V, lift := 𝟙 _, map := f, fac := by simp }⟩

include H H' f S HS

@[simps]
def factor_cover_sieve_one : K X :=
begin
  split, apply K.bind_covering S.property,
  intros Z g hg,
  exact (K.pullback_stable (HS hg).lift
    (H'.cover_preserve (H.map ((HS hg).map ≫ f)).property) : _)
end

omit f S HS

/-
Thus given any finite family of morphisms `{ fᵢ : X ⟶ G(Yᵢ) }`, we may obtain a covering sieve of
`X` that factors through the image of `G`, and factors through an image map of `G` after composing
with each `fᵢ` by repeatedly applying of `factor_cover_sieve_one`.
-/
lemma factor_cover_sieve_exists (O : finset (structured_arrow X G)) :
  ∃ (S : K X) (H₁ : all_factors_through_image_obj_and_map G S O), true :=
begin
  classical,
  apply finset.induction_on O,
  { use H.obj X, split, swap, trivial,
    intros Y g hg,
    apply through_obj_to_through_both (H.obj_fac X hg),
    intro X, exfalso, exact X.2 },
  rintros f O' - ⟨S, hS, -⟩,
  use factor_cover_sieve_one H H' f.hom S (all_through_both_to_through_obj hS),
  split, swap, trivial,
  intros Y g hg,
  choose Y' g' f' H₁ H₂ H₃ using hg,
  rcases presieve.get_functor_pushforward_structure H₂ with ⟨Y'', g'', f'', H₄, H₅⟩,
  let : factors_through_image_obj G g :=
  { obj := Y'', lift := f'', map := G.map g'' ≫ (hS H₁).map, fac := by
    { rw [← H₃, ← category.assoc, ← H₅, category.assoc], congr, exact (hS H₁).fac } },
  apply through_obj_to_through_both this,
  rintros ⟨f₀, hf₀⟩,
  cases finset.mem_insert.mp hf₀ with hf₀' hf₀',
  { cases hf₀',
    use H.map_fac_map ((hS H₁).map ≫ f.hom) H₄,
    rw category.assoc,
    exact H.map_fac _ H₄ },
  { use g'' ≫ (hS H₁).premap ⟨f₀, hf₀'⟩,
    rw [G.map_comp, (hS H₁).map_fac ⟨_, hf₀'⟩, category.assoc] }
end

noncomputable
def factor_cover_sieve {G : C ⥤ D} (H : cover_dense J K G) (H' : cover_preserving J K G)
  {X : D} (O : finset (structured_arrow X G)) : K X :=
(factor_cover_sieve_exists H H' O).some

noncomputable
def factor_cover_sieve_factor {G : C ⥤ D} (H : cover_dense J K G) (H' : cover_preserving J K G)
  {X : D} (O : finset (structured_arrow X G)) :
  all_factors_through_image_obj_and_map G (factor_cover_sieve H H' O) O :=
(factor_cover_sieve_exists H H' O).some_spec.some

end factor_cover_sieve
end cover_dense
namespace presieve.family_of_elements
open presieve
open opposite
open structured_arrow
universes v₁ u₁ u₂
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₁} D]
variables {J : grothendieck_topology C} {K : grothendieck_topology D}
variables (u : C ⥤ D) (hu₁ : cover_dense J K u) (hu₂ : cover_preserving J K u)
variables {P : Dᵒᵖ ⥤ Type v₁} {Z : C} {T : presieve Z}
variables (hT : is_sheaf K P)
variables {x : family_of_elements (u.op ⋙ P) T} (h : x.compatible)
include hu₁ hu₂ hT

/-
We ought to show that for each `f₁ ≫ u.map g₁ = f₂ ≫ u.map g₂`, the restriction of
`x` along the two paths are the same given `x` is compatible in the image of `u`.
  -/
lemma functor_pushforward_compatible_of_dense_subsite {Y₁ Y₂ : C} {X Z: D}
  (f₁ : X ⟶ u.obj Y₁) (f₂ : X ⟶ u.obj Y₂) (g₁ : u.obj Y₁ ⟶ Z) (g₂ : u.obj Y₂ ⟶ Z)
  (eq : f₁ ≫ g₁ = f₂ ≫ g₂)
  (x₁ : P.obj (op (u.obj Y₁))) (x₂ : P.obj (op (u.obj Y₂)))
  (hx : ∀ {X' : C} (f₁' : X' ⟶ Y₁) (f₂' : X' ⟶ Y₂) (h : u.map f₁' ≫ g₁ = u.map f₂' ≫ g₂),
    P.map (u.map f₁').op x₁ = P.map (u.map f₂').op x₂) :
  P.map f₁.op x₁ = P.map f₂.op x₂ :=
begin
  classical,
  let O := [mk f₁, mk f₂].to_finset,
  let f₁' : O := ⟨mk f₁, by simp⟩,
  let f₂' : O := ⟨mk f₂, by simp⟩,
  apply (hT _ (factor_cover_sieve hu₁ hu₂ O).property).is_separated_for.ext,
  intros Y f hf,
  let H := factor_cover_sieve_factor hu₁ hu₂ O hf,
  simp only [← types_comp_apply (P.map _) (P.map _), ← P.map_comp, ← op_comp],
  have e₁ : _ = f ≫ f₁ := H.map_fac' f₁',
  have e₂ : _ = f ≫ f₂ := H.map_fac' f₂',
  simp only [←e₁, ←e₂, op_comp, P.map_comp, types_comp_apply],
  congr,
  apply hx (H.premap f₁') (H.premap f₂'),
  simp [H.map_fac f₁', H.map_fac f₂', eq],
end

include h
variable [faithful u]

lemma functor_pushforward_compatible_of_dense_subsite_of_compatible {Y₁ Y₂ : C} {X : D}
  (f₁ : X ⟶ u.obj Y₁) (f₂ : X ⟶ u.obj Y₂) {g₁ : Y₁ ⟶ Z} {g₂ : Y₂ ⟶ Z}
  (hg₁ : T g₁) (hg₂ : T g₂) (eq : f₁ ≫ u.map g₁ = f₂ ≫ u.map g₂) :
  P.map f₁.op (x g₁ hg₁) = P.map f₂.op (x g₂ hg₂) :=
begin
  apply functor_pushforward_compatible_of_dense_subsite u hu₁ hu₂ hT f₁ f₂ _ _ eq,
  intros X' f₁' f₂' eq',
  apply h,
  apply u.map_injective,
  simpa using eq'
end

lemma compatible.functor_pushforward_of_dense_subsite : (x.functor_pushforward u).compatible :=
begin
  rintros Z₁ Z₂ W g₁ g₂ f₁' f₂' H₁ H₂ eq,
  unfold family_of_elements.functor_pushforward,
  rcases get_functor_pushforward_structure H₁ with ⟨X₁, f₁, h₁, hf₁, rfl⟩,
  rcases get_functor_pushforward_structure H₂ with ⟨X₂, f₂, h₂, hf₂, rfl⟩,
  suffices : P.map (g₁ ≫ h₁).op (x f₁ hf₁) = P.map (g₂ ≫ h₂).op (x f₂ hf₂), simpa using this,
  apply functor_pushforward_compatible_of_dense_subsite_of_compatible u hu₁ hu₂ hT h _ _ hf₁ hf₂,
  simpa using eq
end

lemma functor_pushforward_apply_map_of_dense_subsite {Y : C} {f: Y ⟶ Z} (hf) :
  x.functor_pushforward u (u.map f) (image_mem_functor_pushforward u T hf) = x f hf :=
begin
  unfold family_of_elements.functor_pushforward,
  rcases e₁ : get_functor_pushforward_structure (image_mem_functor_pushforward u T hf) with
    ⟨X, g, f', hg, eq⟩,
  simpa using functor_pushforward_compatible_of_dense_subsite_of_compatible u hu₁ hu₂ hT h f' (𝟙 _)
    hg hf (by simp[eq])
end

end presieve.family_of_elements

section
open limits
open opposite
open presieve
variables {C D : Type u} [category.{u} C] [category.{u} D] {G : C ⥤ D}
variables {J : grothendieck_topology C} {K : grothendieck_topology D}
variables {A : Type v} [category.{u} A]
variables (H : cover_dense J K G) (H' : cover_preserving J K G)



namespace subsite_comparison
variables {ℱ ℱ' : SheafOfTypes K} (α : G.op ⋙ ℱ.val ⟶ G.op ⋙ ℱ'.val)

@[simps]
def sheaf_over (ℱ : Sheaf K A) (X : A) : SheafOfTypes K :=
⟨ℱ.val ⋙ coyoneda.obj (op X), ℱ.property X⟩

@[simps]
def iso_over {ℱ ℱ' : Sheaf K A} (α : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) (X : A) :
  G.op ⋙ (sheaf_over ℱ X).val ≅ G.op ⋙ (sheaf_over ℱ' X).val :=
iso_whisker_right α (coyoneda.obj (op X))

include H H' ℱ ℱ'
open structured_arrow
namespace types
@[simp] noncomputable
def pushforward_family {X}
  (x : ℱ.val.obj (op X)) : family_of_elements ℱ'.val (H.obj' X) := λ Y f hf,
  ℱ'.val.map (H.obj_fac' _ hf).lift.op $ α.app (op (H.obj_fac' X hf).obj) $
    ℱ.val.map (H.obj_fac' _ hf).map.op x

variable [faithful G]

lemma pushforward_family_compatible {X} (x : ℱ.val.obj (op X)) :
  (pushforward_family H H' α x).compatible :=
begin
  intros Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e,
  change (ℱ'.val.map (H.obj_fac' X h₁).lift.op ≫ ℱ'.val.map g₁.op) _ =
  (ℱ'.val.map (H.obj_fac' X h₂).lift.op ≫ ℱ'.val.map g₂.op) _,
  simp only [←functor.map_comp, ← op_comp],
  apply presieve.family_of_elements.functor_pushforward_compatible_of_dense_subsite G H H'
    ℱ'.property (g₁ ≫ (H.obj_fac' X h₁).lift) (g₂ ≫ (H.obj_fac' X h₂).lift)
    (H.obj_fac' X h₁).map (H.obj_fac' X h₂).map,
  { simp only [category.assoc],
    convert e,
    exact (H.obj_fac' _ h₁).fac.symm,
    exact (H.obj_fac' _ h₂).fac.symm },
  {
    intros X' f₁' f₂' eq',
    convert congr_fun _ x,
    change ℱ.val.map _ ≫ α.app (op _) ≫ ℱ'.val.map _ =
      ℱ.val.map _ ≫ α.app (op _) ≫ ℱ'.val.map _,
    erw [← α.naturality f₁'.op, ← α.naturality f₂'.op],
    simp only [quiver.hom.unop_op, functor.comp_map, G.op_map,
    ← category.assoc, ← ℱ.val.map_comp, ←op_comp, eq'] }
end

noncomputable
def app_hom (X : D) : ℱ.val.obj (op X) ⟶ ℱ'.val.obj (op X) := λ x,
  (ℱ'.property _ (H.obj' X).property).amalgamate
    (pushforward_family H H' α x)
    (pushforward_family_compatible H H' α x)

@[simp]
lemma pushforward_family_apply {X} (x : ℱ.val.obj (op X)) {Y : C} {f : G.obj Y ⟶ X} :
  pushforward_family H H' α x f (H.obj'_in f) = α.app (op Y) (ℱ.val.map f.op x) :=
begin
  unfold pushforward_family, conv_rhs { rw (H.obj_fac' X (H.obj'_in f)).fac },
  refine eq.trans _ (functor_to_types.map_id_apply ℱ'.val _),
  rw ← op_id,
  apply presieve.family_of_elements.functor_pushforward_compatible_of_dense_subsite G H H'
    ℱ'.property _ _ (H.obj_fac' X (H.obj'_in f)).map f,
  { rw ←(H.obj_fac' X (H.obj'_in f)).fac, simp },
  intros X' f₁' f₂' eq',
  simp,
  change (ℱ.val.map _ ≫ α.app (op (H.obj_fac' X (H.obj'_in f)).obj) ≫ ℱ'.val.map _) _
    = (ℱ.val.map _ ≫ ℱ.val.map _ ≫ α.app (op Y) ≫ ℱ'.val.map _) _,
  erw [← α.naturality f₁'.op, ← α.naturality f₂'.op],
  simp only [quiver.hom.unop_op, functor.comp_map, G.op_map,
    ← category.assoc, ← ℱ.val.map_comp, ←op_comp, eq'],
  conv_lhs { rw (H.obj_fac' X (H.obj'_in f)).fac },
  simp
end

section end
@[simp] lemma app_hom_restrict {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) (x) :
  ℱ'.val.map f (app_hom H H' α X x) = α.app (op Y) (ℱ.val.map f x) :=
begin
  refine ((ℱ'.property _ (H.obj' X).property).valid_glue
    (pushforward_family_compatible H H' α x) f.unop (H.obj'_in f.unop)).trans _,
  apply pushforward_family_apply,
end

@[simp]
lemma app_hom_valid_glue {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) :
  (app_hom H H' α X) ≫ ℱ'.val.map f = ℱ.val.map f ≫ α.app (op Y) :=
by { ext, apply app_hom_restrict }

@[simps] noncomputable
def app_iso (eq : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) (X : D) :
  ℱ.val.obj (op X) ≅ ℱ'.val.obj (op X) :=
{ hom := app_hom H H' eq.hom X,
  inv := app_hom H H' eq.inv X,
  hom_inv_id' :=
  begin
    ext x,
    apply (ℱ.property _ (H.obj' X).property).is_separated_for.ext,
    intros Y f hf,
    rw (H.obj_fac' _ hf).fac,
    simp
  end,
  inv_hom_id' :=
  begin
    ext x,
    apply (ℱ'.property _ (H.obj' X).property).is_separated_for.ext,
    intros Y f hf,
    rw (H.obj_fac' _ hf).fac,
    simp
  end }

@[simps] noncomputable
def sheaf_iso (eq : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) : ℱ.val ≅ ℱ'.val :=
begin
  classical,
  fapply nat_iso.of_components,
  { intro X,
    exact app_iso H H' eq (unop X) },
  { intros X Y f,
    ext x,
    apply (ℱ'.property _ (H.obj' (unop Y)).property).is_separated_for.ext,
    intros Y' f' hf',
    rw (H.obj_fac' _ hf').fac,
    simp only [app_hom_restrict, types_comp_apply, op_comp,
      functor_to_types.map_comp_apply, app_iso],
    change _ = ℱ'.val.map _ ((ℱ'.val.map _ ≫ ℱ'.val.map _) _),
    rw [← ℱ'.val.map_comp, ← f.op_unop, ← op_comp, app_hom_restrict],
    simp }
end
end types
open types

variable [faithful G]

@[simp, reassoc]
lemma app_hom_is_valid_glue (ℱ ℱ' : Sheaf K A) (eq : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) (X) {Y U}
{f : Y ⟶ U} (hf : (H.obj' U).val f) (x) :
 app_hom H H' (iso_over eq (unop X)).hom U x ≫ ℱ'.val.map (H.obj_fac' U hf).map.op =
  x ≫ ℱ.val.map (H.obj_fac' U hf).map.op ≫ eq.hom.app (op (H.obj_fac' U hf).obj) :=
(congr_fun (app_hom_valid_glue H H' (iso_over eq (unop X)).hom (H.obj_fac' U hf).map.op) x).trans
  (by { rw ←category.assoc, refl  })

@[simp]
lemma app_hom_apply_comp (ℱ ℱ' : Sheaf K A) (eq : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) (X Y) (U) (x y) :
  app_hom H H' (iso_over eq (unop X)).hom U (y ≫ x) =
    y ≫ app_hom H H' (iso_over eq (unop Y)).hom U x :=
begin
  apply ((sheaf_over ℱ' (unop X)).property _ (H.obj' U).property).is_separated_for,
  apply is_sheaf_for.is_amalgamation,
  intros Y f h,
  conv_lhs { rw (H.obj_fac' _ h).fac },
  delta sheaf_over,
  simp only [pushforward_family, op_comp, functor_to_types.map_comp_apply, iso_over_hom_app,
    functor.comp_map, coyoneda_obj_map, category.assoc],
  congr' 1,
  simp
end

@[simp]
lemma app_hom_apply_comp_id (ℱ ℱ' : Sheaf K A) (eq : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) (X) (U)
  (x : X ⟶ ℱ.val.obj U) :
  x ≫ app_hom H H' (iso_over eq (ℱ.val.obj U)).hom (unop U) (𝟙 _) =
    app_hom H H' (iso_over eq X).hom (unop U) x :=
begin
  convert (app_hom_apply_comp H H' ℱ ℱ' eq (op X) (op (ℱ.val.obj U)) (unop U) (𝟙 _) x).symm,
  exact (category.comp_id x).symm,
end


@[simps] noncomputable
def sheaf_coyoneda_iso (ℱ ℱ' : Sheaf K A)
  (eq : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
  coyoneda ⋙ (whiskering_left Dᵒᵖ A (Type u)).obj ℱ.val ≅
  coyoneda ⋙ (whiskering_left Dᵒᵖ A (Type u)).obj ℱ'.val :=
begin
  fapply nat_iso.of_components,
  intro X, dsimp,
  exact sheaf_iso H H' (iso_over eq (unop X)),
  intros X Y f, ext U x,
  change app_hom H H' (iso_over eq (unop Y)).hom (unop U) (f.unop ≫ x) =
    f.unop ≫ app_hom H H' (iso_over eq (unop X)).hom (unop U) x,
  apply ((sheaf_over ℱ' (unop Y)).property _ (H.obj' (unop U)).property).is_separated_for,
  apply is_sheaf_for.is_amalgamation,
  intros Y' f' h',
  dsimp[pushforward_family],
  conv_lhs { rw (H.obj_fac' _ h').fac },
  simp only [category.assoc, op_comp, functor.map_comp],
  congr' 1,
  simp only [←category.assoc],
  congr' 1,
  have := app_hom_restrict H H' (iso_over eq (unop X)).hom (H.obj_fac' (unop U) h').map.op x,
  refine this.trans _,
  dsimp, simp
end

@[simps] noncomputable
def sheaf_yoneda_iso (ℱ ℱ' : Sheaf K A) (eq : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
  ℱ.val ⋙ yoneda ≅ ℱ'.val ⋙ yoneda :=
begin
  let α := sheaf_coyoneda_iso H H' ℱ ℱ' eq,
  fapply nat_iso.of_components,
    intro U,
    fapply nat_iso.of_components,
      intro X,
      exact (α.app X).app U,
      intros X Y f,
      simpa using congr_app (α.hom.naturality f) U,
    intros U V i,
    ext X x,
    exact congr_fun ((α.app X).hom.naturality i) x,
end

@[simps] noncomputable
def sheaf_iso (ℱ ℱ' : Sheaf K A) (eq : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
  ℱ.val ≅ ℱ'.val :=
fully_faithful_cancel_right yoneda (sheaf_yoneda_iso H H' ℱ ℱ' eq)

section end
lemma app_eq_sheaf_yoneda_iso_app {ℱ ℱ' : Sheaf K A} (α : ℱ.val ⟶ ℱ'.val)
  (Hα : is_iso (whisker_left G.op α)) (X) : α.app X =
    (((sheaf_yoneda_iso H H' ℱ ℱ' (as_iso (whisker_left G.op α))).app X).app
      (op (ℱ.val.obj X))).hom (𝟙 _) :=
begin
  apply ((sheaf_over ℱ' (ℱ.val.obj X)).property _ (H.obj' (unop X)).property).is_separated_for,
  swap,
  apply is_sheaf_for.is_amalgamation,
  intros Y f hf,
  nth_rewrite_lhs 0 (H.obj_fac' (unop X) hf).fac,
  dsimp,
  simp
end


lemma iso_of_restrict_iso {ℱ ℱ' : Sheaf K A} (α : ℱ.val ⟶ ℱ'.val)
  (eq : is_iso (whisker_left G.op α)) : is_iso α :=
begin
  convert is_iso.of_iso (sheaf_iso H H' ℱ ℱ' (as_iso (whisker_left G.op α))),
  ext X,
  rw app_eq_sheaf_yoneda_iso_app H H' α eq,
  apply yoneda.map_injective,
  ext U x,
  erw functor.image_preimage,
  dsimp,
  apply app_hom_apply_comp_id,
  apply_instance
end

end subsite_comparison
end
end category_theory
