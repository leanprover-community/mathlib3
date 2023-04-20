/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.adjunction.fully_faithful
import category_theory.sites.plus
import category_theory.limits.concrete_category
import category_theory.concrete_category.elementwise

/-!

# Sheafification

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We construct the sheafification of a presheaf over a site `C` with values in `D` whenever
`D` is a concrete category for which the forgetful functor preserves the appropriate (co)limits
and reflects isomorphisms.

We generally follow the approach of https://stacks.math.columbia.edu/tag/00W1

-/

namespace category_theory

open category_theory.limits opposite

universes w v u
variables {C : Type u} [category.{v} C] {J : grothendieck_topology C}
variables {D : Type w} [category.{max v u} D]

section
variables [concrete_category.{max v u} D]

local attribute [instance]
  concrete_category.has_coe_to_sort
  concrete_category.has_coe_to_fun

/-- A concrete version of the multiequalizer, to be used below. -/
@[nolint has_nonempty_instance]
def meq {X : C} (P : Cᵒᵖ ⥤ D) (S : J.cover X) :=
{ x : Π (I : S.arrow), P.obj (op I.Y) //
  ∀ (I : S.relation), P.map I.g₁.op (x I.fst) = P.map I.g₂.op (x I.snd) }
end

namespace meq

variables [concrete_category.{max v u} D]

local attribute [instance]
  concrete_category.has_coe_to_sort
  concrete_category.has_coe_to_fun


instance {X} (P : Cᵒᵖ ⥤ D) (S : J.cover X) : has_coe_to_fun (meq P S)
  (λ x, Π (I : S.arrow), P.obj (op I.Y)) := ⟨λ x, x.1⟩

@[ext]
lemma ext {X} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x y : meq P S)
  (h : ∀ I : S.arrow, x I = y I) : x = y := subtype.ext $ funext $ h

lemma condition {X} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : meq P S) (I : S.relation) :
  P.map I.g₁.op (x ((S.index P).fst_to I)) = P.map I.g₂.op (x ((S.index P).snd_to I)) := x.2 _

/-- Refine a term of `meq P T` with respect to a refinement `S ⟶ T` of covers. -/
def refine {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.cover X} (x : meq P T) (e : S ⟶ T) :
  meq P S :=
⟨λ I, x ⟨I.Y, I.f, (le_of_hom e) _ I.hf⟩,
  λ I, x.condition ⟨I.Y₁, I.Y₂, I.Z, I.g₁, I.g₂, I.f₁, I.f₂,
    (le_of_hom e) _ I.h₁, (le_of_hom e) _ I.h₂, I.w⟩⟩

@[simp]
lemma refine_apply {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.cover X} (x : meq P T) (e : S ⟶ T)
  (I : S.arrow) : x.refine e I = x ⟨I.Y, I.f, (le_of_hom e) _ I.hf⟩ := rfl

/-- Pull back a term of `meq P S` with respect to a morphism `f : Y ⟶ X` in `C`. -/
def pullback {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : meq P S) (f : Y ⟶ X) :
  meq P ((J.pullback f).obj S) :=
⟨λ I, x ⟨_,I.f ≫ f, I.hf⟩, λ I, x.condition
  ⟨I.Y₁, I.Y₂, I.Z, I.g₁, I.g₂, I.f₁ ≫ f, I.f₂ ≫ f, I.h₁, I.h₂, by simp [reassoc_of I.w]⟩ ⟩

@[simp]
lemma pullback_apply {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : meq P S) (f : Y ⟶ X)
  (I : ((J.pullback f).obj S).arrow) : x.pullback f I = x ⟨_, I.f ≫ f, I.hf⟩ := rfl

@[simp]
lemma pullback_refine {Y X : C} {P : Cᵒᵖ ⥤ D} {S T : J.cover X} (h : S ⟶ T)
  (f : Y ⟶ X) (x : meq P T) : (x.pullback f).refine
  ((J.pullback f).map h) = (refine x h).pullback _ := rfl

/-- Make a term of `meq P S`. -/
def mk {X : C} {P : Cᵒᵖ ⥤ D} (S : J.cover X) (x : P.obj (op X)) : meq P S :=
⟨λ I, P.map I.f.op x, λ I, by { dsimp, simp only [← comp_apply, ← P.map_comp, ← op_comp, I.w] }⟩

lemma mk_apply {X : C} {P : Cᵒᵖ ⥤ D} (S : J.cover X) (x : P.obj (op X)) (I : S.arrow) :
  mk S x I = P.map I.f.op x := rfl

variable [preserves_limits (forget D)]

/-- The equivalence between the type associated to `multiequalizer (S.index P)` and `meq P S`. -/
noncomputable
def equiv {X : C} (P : Cᵒᵖ ⥤ D) (S : J.cover X) [has_multiequalizer (S.index P)] :
  (multiequalizer (S.index P) : D) ≃ meq P S :=
limits.concrete.multiequalizer_equiv _

@[simp]
lemma equiv_apply {X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} [has_multiequalizer (S.index P)]
  (x : multiequalizer (S.index P)) (I : S.arrow) :
equiv P S x I = multiequalizer.ι (S.index P) I x := rfl

@[simp]
lemma equiv_symm_eq_apply {X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} [has_multiequalizer (S.index P)]
  (x : meq P S) (I : S.arrow) : multiequalizer.ι (S.index P) I ((meq.equiv P S).symm x) = x I :=
begin
  let z := (meq.equiv P S).symm x,
  rw ← equiv_apply,
  simp,
end

end meq

namespace grothendieck_topology

namespace plus

variables [concrete_category.{max v u} D]

local attribute [instance]
  concrete_category.has_coe_to_sort
  concrete_category.has_coe_to_fun

variable [preserves_limits (forget D)]
variables [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]
variables [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), has_multiequalizer (S.index P)]

noncomputable theory

/-- Make a term of `(J.plus_obj P).obj (op X)` from `x : meq P S`. -/
def mk {X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : meq P S) : (J.plus_obj P).obj (op X) :=
colimit.ι (J.diagram P X) (op S) ((meq.equiv P S).symm x)

lemma res_mk_eq_mk_pullback {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : meq P S) (f : Y ⟶ X) :
  (J.plus_obj P).map f.op (mk x) = mk (x.pullback f) :=
begin
  dsimp [mk, plus_obj],
  simp only [← comp_apply, colimit.ι_pre, ι_colim_map_assoc],
  simp_rw [comp_apply],
  congr' 1,
  apply_fun meq.equiv P _,
  erw equiv.apply_symm_apply,
  ext i,
  simp only [diagram_pullback_app,
    meq.pullback_apply, meq.equiv_apply, ← comp_apply],
  erw [multiequalizer.lift_ι, meq.equiv_symm_eq_apply],
  cases i, refl,
end

lemma to_plus_mk {X : C} {P : Cᵒᵖ ⥤ D} (S : J.cover X) (x : P.obj (op X)) :
  (J.to_plus P).app _ x = mk (meq.mk S x) :=
begin
  dsimp [mk, to_plus],
  let e : S ⟶ ⊤ := hom_of_le (order_top.le_top _),
  rw ← colimit.w _ e.op,
  delta cover.to_multiequalizer,
  simp only [comp_apply],
  congr' 1,
  dsimp [diagram],
  apply concrete.multiequalizer_ext,
  intros i,
  simpa only [← comp_apply, category.assoc, multiequalizer.lift_ι,
    category.comp_id, meq.equiv_symm_eq_apply],
end

lemma to_plus_apply {X : C} {P : Cᵒᵖ ⥤ D} (S : J.cover X) (x : meq P S) (I : S.arrow) :
  (J.to_plus P).app _ (x I) = (J.plus_obj P).map I.f.op (mk x) :=
begin
  dsimp only [to_plus, plus_obj],
  delta cover.to_multiequalizer,
  dsimp [mk],
  simp only [← comp_apply, colimit.ι_pre, ι_colim_map_assoc],
  simp only [comp_apply],
  dsimp only [functor.op],
  let e : (J.pullback I.f).obj (unop (op S)) ⟶ ⊤ := hom_of_le (order_top.le_top _),
  rw ← colimit.w _ e.op,
  simp only [comp_apply],
  congr' 1,
  apply concrete.multiequalizer_ext,
  intros i,
  dsimp [diagram],
  simp only [← comp_apply, category.assoc, multiequalizer.lift_ι,
    category.comp_id, meq.equiv_symm_eq_apply],
  let RR : S.relation :=
    ⟨_, _, _, i.f, 𝟙 _, I.f, i.f ≫ I.f, I.hf, sieve.downward_closed _ I.hf _, by simp⟩,
  cases I,
  erw x.condition RR,
  simpa [RR],
end

lemma to_plus_eq_mk {X : C} {P : Cᵒᵖ ⥤ D} (x : P.obj (op X)) :
  (J.to_plus P).app _ x = mk (meq.mk ⊤ x) :=
begin
  dsimp [mk, to_plus],
  delta cover.to_multiequalizer,
  simp only [comp_apply],
  congr' 1,
  apply_fun (meq.equiv P ⊤),
  ext i,
  simpa,
end

variables [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]

lemma exists_rep {X : C} {P : Cᵒᵖ ⥤ D} (x : (J.plus_obj P).obj (op X)) :
  ∃ (S : J.cover X) (y : meq P S), x = mk y :=
begin
  obtain ⟨S,y,h⟩ := concrete.colimit_exists_rep (J.diagram P X) x,
  use [S.unop, meq.equiv _ _ y],
  rw ← h,
  dsimp [mk],
  simp,
end

lemma eq_mk_iff_exists {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.cover X}
  (x : meq P S) (y : meq P T) : mk x = mk y ↔ (∃ (W : J.cover X) (h1 : W ⟶ S) (h2 : W ⟶ T),
    x.refine h1 = y.refine h2) :=
begin
  split,
  { intros h,
    obtain ⟨W, h1, h2, hh⟩ := concrete.colimit_exists_of_rep_eq _ _ _ h,
    use [W.unop, h1.unop, h2.unop],
    ext I,
    apply_fun (multiequalizer.ι (W.unop.index P) I) at hh,
    convert hh,
    all_goals
    { dsimp [diagram],
      simp only [← comp_apply, multiequalizer.lift_ι, category.comp_id, meq.equiv_symm_eq_apply],
      cases I, refl } },
  { rintros ⟨S,h1,h2,e⟩,
    apply concrete.colimit_rep_eq_of_exists,
    use [(op S), h1.op, h2.op],
    apply concrete.multiequalizer_ext,
    intros i,
    apply_fun (λ ee, ee i) at e,
    convert e,
    all_goals
    { dsimp [diagram],
      simp only [← comp_apply, multiequalizer.lift_ι, meq.equiv_symm_eq_apply],
      cases i, refl } },
end

/-- `P⁺` is always separated. -/
theorem sep {X : C} (P : Cᵒᵖ ⥤ D) (S : J.cover X) (x y : (J.plus_obj P).obj (op X))
  (h : ∀ (I : S.arrow), (J.plus_obj P).map I.f.op x = (J.plus_obj P).map I.f.op y) :
  x = y :=
begin
  -- First, we choose representatives for x and y.
  obtain ⟨Sx,x,rfl⟩ := exists_rep x,
  obtain ⟨Sy,y,rfl⟩ := exists_rep y,
  simp only [res_mk_eq_mk_pullback] at h,

  -- Next, using our assumption,
  -- choose covers over which the pullbacks of these representatives become equal.
  choose W h1 h2 hh using λ (I : S.arrow), (eq_mk_iff_exists _ _).mp (h I),

  -- To prove equality, it suffices to prove that there exists a cover over which
  -- the representatives become equal.
  rw eq_mk_iff_exists,

  -- Construct the cover over which the representatives become equal by combining the various
  -- covers chosen above.
  let B : J.cover X := S.bind W,
  use B,

  -- Prove that this cover refines the two covers over which our representatives are defined
  -- and use these proofs.
  let ex : B ⟶ Sx := hom_of_le begin
    rintros Y f ⟨Z,e1,e2,he2,he1,hee⟩,
    rw ← hee,
    apply le_of_hom (h1 ⟨_, _, he2⟩),
    exact he1,
  end,
  let ey : B ⟶ Sy := hom_of_le begin
    rintros Y f ⟨Z,e1,e2,he2,he1,hee⟩,
    rw ← hee,
    apply le_of_hom (h2 ⟨_, _, he2⟩),
    exact he1,
  end,
  use [ex, ey],

  -- Now prove that indeed the representatives become equal over `B`.
  -- This will follow by using the fact that our representatives become
  -- equal over the chosen covers.
  ext1 I,
  let IS : S.arrow := I.from_middle,
  specialize hh IS,
  let IW : (W IS).arrow := I.to_middle,
  apply_fun (λ e, e IW) at hh,
  convert hh,
  { let Rx : Sx.relation := ⟨I.Y, I.Y, I.Y, 𝟙 _, 𝟙 _, I.f,
      I.to_middle_hom ≫ I.from_middle_hom, _, _, by simp [I.middle_spec]⟩,
    have := x.condition Rx,
    simpa using this },
  { let Ry : Sy.relation := ⟨I.Y, I.Y, I.Y, 𝟙 _, 𝟙 _, I.f,
      I.to_middle_hom ≫ I.from_middle_hom, _, _, by simp [I.middle_spec]⟩,
    have := y.condition Ry,
    simpa using this },
end

lemma inj_of_sep (P : Cᵒᵖ ⥤ D) (hsep : ∀ (X : C) (S : J.cover X) (x y : P.obj (op X)),
  (∀ I : S.arrow, P.map I.f.op x = P.map I.f.op y) → x = y) (X : C) :
  function.injective ((J.to_plus P).app (op X)) :=
begin
  intros x y h,
  simp only [to_plus_eq_mk] at h,
  rw eq_mk_iff_exists at h,
  obtain ⟨W, h1, h2, hh⟩ := h,
  apply hsep X W,
  intros I,
  apply_fun (λ e, e I) at hh,
  exact hh
end

/-- An auxiliary definition to be used in the proof of `exists_of_sep` below.
  Given a compatible family of local sections for `P⁺`, and representatives of said sections,
  construct a compatible family of local sections of `P` over the combination of the covers
  associated to the representatives.
  The separatedness condition is used to prove compatibility among these local sections of `P`. -/
def meq_of_sep (P : Cᵒᵖ ⥤ D)
  (hsep : ∀ (X : C) (S : J.cover X) (x y : P.obj (op X)),
    (∀ I : S.arrow, P.map I.f.op x = P.map I.f.op y) → x = y)
  (X : C) (S : J.cover X)
  (s : meq (J.plus_obj P) S)
  (T : Π (I : S.arrow), J.cover I.Y)
  (t : Π (I : S.arrow), meq P (T I))
  (ht : ∀ (I : S.arrow), s I = mk (t I)) : meq P (S.bind T) :=
{ val := λ I, t I.from_middle I.to_middle,
  property := begin
    intros II,
    apply inj_of_sep P hsep,
    rw [← comp_apply, ← comp_apply, (J.to_plus P).naturality, (J.to_plus P).naturality,
      comp_apply, comp_apply],
    erw [to_plus_apply (T II.fst.from_middle) (t II.fst.from_middle) II.fst.to_middle,
         to_plus_apply (T II.snd.from_middle) (t II.snd.from_middle) II.snd.to_middle,
         ← ht, ← ht, ← comp_apply, ← comp_apply, ← (J.plus_obj P).map_comp,
         ← (J.plus_obj P).map_comp],
    rw [← op_comp, ← op_comp],
    let IR : S.relation :=
      ⟨_, _, _, II.g₁ ≫ II.fst.to_middle_hom, II.g₂ ≫ II.snd.to_middle_hom,
        II.fst.from_middle_hom, II.snd.from_middle_hom, II.fst.from_middle_condition,
        II.snd.from_middle_condition, _⟩,
    swap, { simp only [category.assoc, II.fst.middle_spec, II.snd.middle_spec], apply II.w },
    exact s.condition IR,
  end }

theorem exists_of_sep (P : Cᵒᵖ ⥤ D)
  (hsep : ∀ (X : C) (S : J.cover X) (x y : P.obj (op X)),
    (∀ I : S.arrow, P.map I.f.op x = P.map I.f.op y) → x = y)
  (X : C) (S : J.cover X)
  (s : meq (J.plus_obj P) S) :
  ∃ t : (J.plus_obj P).obj (op X), meq.mk S t = s :=
begin
  have inj : ∀ (X : C), function.injective ((J.to_plus P).app (op X)) := inj_of_sep _ hsep,

  -- Choose representatives for the given local sections.
  choose T t ht using λ I, exists_rep (s I),

  -- Construct a large cover over which we will define a representative that will
  -- provide the gluing of the given local sections.
  let B : J.cover X := S.bind T,
  choose Z e1 e2 he2 he1 hee using λ I : B.arrow, I.hf,

  -- Construct a compatible system of local sections over this large cover, using the chosen
  -- representatives of our local sections.
  -- The compatilibity here follows from the separatedness assumption.
  let w : meq P B := meq_of_sep P hsep X S s T t ht,

  -- The associated gluing will be the candidate section.
  use mk w,
  ext I,
  erw [ht, res_mk_eq_mk_pullback],

  -- Use the separatedness of `P⁺` to prove that this is indeed a gluing of our
  -- original local sections.
  apply sep P (T I),
  intros II,
  simp only [res_mk_eq_mk_pullback, eq_mk_iff_exists],

  -- It suffices to prove equality for representatives over a
  -- convenient sufficiently large cover...
  use (J.pullback II.f).obj (T I),
  let e0 : (J.pullback II.f).obj (T I) ⟶ (J.pullback II.f).obj ((J.pullback I.f).obj B) :=
    hom_of_le begin
      intros Y f hf,
      apply sieve.le_pullback_bind _ _ _ I.hf,
      { cases I,
        exact hf },
    end,
  use [e0, 𝟙 _],
  ext IV,
  dsimp only [meq.refine_apply, meq.pullback_apply, w],
  let IA : B.arrow := ⟨_, (IV.f ≫ II.f) ≫ I.f, _⟩,
  swap,
  { refine ⟨I.Y, _, _, I.hf, _, rfl⟩,
    apply sieve.downward_closed,
    convert II.hf,
    cases I, refl },
  let IB : S.arrow := IA.from_middle,
  let IC : (T IB).arrow := IA.to_middle,
  let ID : (T I).arrow := ⟨IV.Y, IV.f ≫ II.f, sieve.downward_closed (T I) II.hf IV.f⟩,
  change t IB IC = t I ID,
  apply inj IV.Y,
  erw [to_plus_apply (T I) (t I) ID, to_plus_apply (T IB) (t IB) IC, ← ht, ← ht],

  -- Conclude by constructing the relation showing equality...
  let IR : S.relation := ⟨_, _, IV.Y, IC.f, ID.f, IB.f, I.f, _, I.hf, IA.middle_spec⟩,
  convert s.condition IR,
  cases I, refl,
end

variable [reflects_isomorphisms (forget D)]

/-- If `P` is separated, then `P⁺` is a sheaf. -/
theorem is_sheaf_of_sep (P : Cᵒᵖ ⥤ D)
  (hsep : ∀ (X : C) (S : J.cover X) (x y : P.obj (op X)),
    (∀ I : S.arrow, P.map I.f.op x = P.map I.f.op y) → x = y) :
  presheaf.is_sheaf J (J.plus_obj P) :=
begin
  rw presheaf.is_sheaf_iff_multiequalizer,
  intros X S,
  apply is_iso_of_reflects_iso _ (forget D),
  rw is_iso_iff_bijective,
  split,
  { intros x y h,
    apply sep P S _ _,
    intros I,
    apply_fun (meq.equiv _ _) at h,
    apply_fun (λ e, e I) at h,
    convert h,
    { erw [meq.equiv_apply, ← comp_apply, multiequalizer.lift_ι] },
    { erw [meq.equiv_apply, ← comp_apply, multiequalizer.lift_ι] } },
  { rintros (x : (multiequalizer (S.index _) : D)),
    obtain ⟨t,ht⟩ := exists_of_sep P hsep X S (meq.equiv _ _ x),
    use t,
    apply_fun meq.equiv _ _,
    swap, { apply_instance },
    rw ← ht,
    ext i,
    dsimp,
    rw [← comp_apply, multiequalizer.lift_ι],
    refl }
end

variable (J)

/-- `P⁺⁺` is always a sheaf. -/
theorem is_sheaf_plus_plus (P : Cᵒᵖ ⥤ D) :
  presheaf.is_sheaf J (J.plus_obj (J.plus_obj P)) :=
begin
  apply is_sheaf_of_sep,
  intros X S x y,
  apply sep,
end

end plus

variables (J)
variables
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), has_multiequalizer (S.index P)]
  [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]

/-- The sheafification of a presheaf `P`.
*NOTE:* Additional hypotheses are needed to obtain a proof that this is a sheaf! -/
def sheafify (P : Cᵒᵖ ⥤ D) : Cᵒᵖ ⥤ D := J.plus_obj (J.plus_obj P)

/-- The canonical map from `P` to its sheafification. -/
def to_sheafify (P : Cᵒᵖ ⥤ D) : P ⟶ J.sheafify P :=
J.to_plus P ≫ J.plus_map (J.to_plus P)

/-- The canonical map on sheafifications induced by a morphism. -/
def sheafify_map {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : J.sheafify P ⟶ J.sheafify Q :=
J.plus_map $ J.plus_map η

@[simp]
lemma sheafify_map_id (P : Cᵒᵖ ⥤ D) : J.sheafify_map (𝟙 P) = 𝟙 (J.sheafify P) :=
by { dsimp [sheafify_map, sheafify], simp }

@[simp]
lemma sheafify_map_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) :
  J.sheafify_map (η ≫ γ) = J.sheafify_map η ≫ J.sheafify_map γ :=
by { dsimp [sheafify_map, sheafify], simp }

@[simp, reassoc]
lemma to_sheafify_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
  η ≫ J.to_sheafify _ = J.to_sheafify _ ≫ J.sheafify_map η :=
by { dsimp [sheafify_map, sheafify, to_sheafify], simp }

variable (D)

/-- The sheafification of a presheaf `P`, as a functor.
*NOTE:* Additional hypotheses are needed to obtain a proof that this is a sheaf! -/
def sheafification : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D := (J.plus_functor D ⋙ J.plus_functor D)

@[simp]
lemma sheafification_obj (P : Cᵒᵖ ⥤ D) : (J.sheafification D).obj P = J.sheafify P := rfl

@[simp]
lemma sheafification_map {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : (J.sheafification D).map η =
  J.sheafify_map η := rfl

/-- The canonical map from `P` to its sheafification, as a natural transformation.
*Note:* We only show this is a sheaf under additional hypotheses on `D`. -/
def to_sheafification : 𝟭 _ ⟶ sheafification J D :=
J.to_plus_nat_trans D ≫ whisker_right (J.to_plus_nat_trans D) (J.plus_functor D)

@[simp]
lemma to_sheafification_app (P : Cᵒᵖ ⥤ D) : (J.to_sheafification D).app P = J.to_sheafify P := rfl

variable {D}

lemma is_iso_to_sheafify {P : Cᵒᵖ ⥤ D} (hP : presheaf.is_sheaf J P) :
  is_iso (J.to_sheafify P) :=
begin
  dsimp [to_sheafify],
  haveI : is_iso (J.to_plus P) := by { apply is_iso_to_plus_of_is_sheaf J P hP },
  haveI : is_iso ((J.plus_functor D).map (J.to_plus P)) := by { apply functor.map_is_iso },
  exact @is_iso.comp_is_iso _ _ _ _ _ (J.to_plus P)
    ((J.plus_functor D).map (J.to_plus P)) _ _,
end

/-- If `P` is a sheaf, then `P` is isomorphic to `J.sheafify P`. -/
def iso_sheafify {P : Cᵒᵖ ⥤ D} (hP : presheaf.is_sheaf J P) :
  P ≅ J.sheafify P :=
by letI := is_iso_to_sheafify J hP; exactI as_iso (J.to_sheafify P)

@[simp]
lemma iso_sheafify_hom {P : Cᵒᵖ ⥤ D} (hP : presheaf.is_sheaf J P) :
  (J.iso_sheafify hP).hom = J.to_sheafify P := rfl

/-- Given a sheaf `Q` and a morphism `P ⟶ Q`, construct a morphism from
`J.sheafifcation P` to `Q`. -/
def sheafify_lift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : presheaf.is_sheaf J Q) :
  J.sheafify P ⟶ Q := J.plus_lift (J.plus_lift η hQ) hQ

@[simp, reassoc]
lemma to_sheafify_sheafify_lift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : presheaf.is_sheaf J Q) :
  J.to_sheafify P ≫ sheafify_lift J η hQ = η :=
by { dsimp only [sheafify_lift, to_sheafify], simp }

lemma sheafify_lift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : presheaf.is_sheaf J Q)
  (γ : J.sheafify P ⟶ Q) :
  J.to_sheafify P ≫ γ = η → γ = sheafify_lift J η hQ :=
begin
  intros h,
  apply plus_lift_unique,
  apply plus_lift_unique,
  rw [← category.assoc, ← plus_map_to_plus],
  exact h,
end

@[simp]
lemma iso_sheafify_inv {P : Cᵒᵖ ⥤ D} (hP : presheaf.is_sheaf J P) :
  (J.iso_sheafify hP).inv = J.sheafify_lift (𝟙 _) hP :=
begin
  apply J.sheafify_lift_unique,
  simp [iso.comp_inv_eq],
end

lemma sheafify_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : J.sheafify P ⟶ Q) (hQ : presheaf.is_sheaf J Q)
  (h : J.to_sheafify P ≫ η = J.to_sheafify P ≫ γ) : η = γ :=
begin
  apply J.plus_hom_ext _ _ hQ,
  apply J.plus_hom_ext _ _ hQ,
  rw [← category.assoc, ← category.assoc, ← plus_map_to_plus],
  exact h,
end

@[simp, reassoc]
lemma sheafify_map_sheafify_lift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
  (hR : presheaf.is_sheaf J R) :
  J.sheafify_map η ≫ J.sheafify_lift γ hR = J.sheafify_lift (η ≫ γ) hR :=
begin
  apply J.sheafify_lift_unique,
  rw [← category.assoc, ← J.to_sheafify_naturality,
    category.assoc, to_sheafify_sheafify_lift],
end

end grothendieck_topology

variables (J)
variables
  [concrete_category.{max v u} D]
  [preserves_limits (forget D)]
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), has_multiequalizer (S.index P)]
  [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]
  [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]
  [reflects_isomorphisms (forget D)]

lemma grothendieck_topology.sheafify_is_sheaf (P : Cᵒᵖ ⥤ D) :
  presheaf.is_sheaf J (J.sheafify P) :=
grothendieck_topology.plus.is_sheaf_plus_plus _ _

variables (D)

/-- The sheafification functor, as a functor taking values in `Sheaf`. -/
@[simps]
def presheaf_to_Sheaf : (Cᵒᵖ ⥤ D) ⥤ Sheaf J D :=
{ obj := λ P, ⟨J.sheafify P, J.sheafify_is_sheaf P⟩,
  map := λ P Q η, ⟨J.sheafify_map η⟩,
  map_id' := λ P, Sheaf.hom.ext _ _ $ J.sheafify_map_id _,
  map_comp' := λ P Q R f g, Sheaf.hom.ext _ _ $ J.sheafify_map_comp _ _ }

instance presheaf_to_Sheaf_preserves_zero_morphisms [preadditive D] :
  (presheaf_to_Sheaf J D).preserves_zero_morphisms  :=
{ map_zero' := λ F G, by { ext, erw [colimit.ι_map, comp_zero, J.plus_map_zero,
    J.diagram_nat_trans_zero, zero_comp] } }

/-- The sheafification functor is left adjoint to the forgetful functor. -/
@[simps unit_app counit_app_val]
def sheafification_adjunction : presheaf_to_Sheaf J D ⊣ Sheaf_to_presheaf J D :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ P Q,
  { to_fun := λ e, J.to_sheafify P ≫ e.val,
    inv_fun := λ e, ⟨J.sheafify_lift e Q.2⟩,
    left_inv := λ e, Sheaf.hom.ext _ _ $ (J.sheafify_lift_unique _ _ _ rfl).symm,
    right_inv := λ e, J.to_sheafify_sheafify_lift _ _ },
  hom_equiv_naturality_left_symm' := begin
    intros P Q R η γ, ext1, dsimp, symmetry,
    apply J.sheafify_map_sheafify_lift,
  end,
  hom_equiv_naturality_right' := λ P Q R η γ, by { dsimp, rw category.assoc } }

instance Sheaf_to_presheaf_is_right_adjoint : is_right_adjoint (Sheaf_to_presheaf J D) :=
⟨_, sheafification_adjunction J D⟩

instance presheaf_mono_of_mono {F G : Sheaf J D} (f : F ⟶ G) [mono f] : mono f.1 :=
(Sheaf_to_presheaf J D).map_mono _

lemma Sheaf.hom.mono_iff_presheaf_mono {F G : Sheaf J D} (f : F ⟶ G) : mono f ↔ mono f.1 :=
⟨λ m, by { resetI, apply_instance },
 λ m, by { resetI, exact Sheaf.hom.mono_of_presheaf_mono J D f }⟩

variables {J D}
/-- A sheaf `P` is isomorphic to its own sheafification. -/
@[simps]
def sheafification_iso (P : Sheaf J D) :
  P ≅ (presheaf_to_Sheaf J D).obj P.val :=
{ hom := ⟨(J.iso_sheafify P.2).hom⟩,
  inv := ⟨(J.iso_sheafify P.2).inv⟩,
  hom_inv_id' := by { ext1, apply (J.iso_sheafify P.2).hom_inv_id },
  inv_hom_id' := by { ext1, apply (J.iso_sheafify P.2).inv_hom_id } }

instance is_iso_sheafification_adjunction_counit (P : Sheaf J D) :
  is_iso ((sheafification_adjunction J D).counit.app P) :=
is_iso_of_fully_faithful (Sheaf_to_presheaf J D) _

instance sheafification_reflective : is_iso (sheafification_adjunction J D).counit :=
nat_iso.is_iso_of_is_iso_app _

end category_theory
