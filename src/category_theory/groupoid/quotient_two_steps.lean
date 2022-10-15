import category_theory.groupoid
import category_theory.groupoid.basic
import category_theory.groupoid.subgroupoid


open set classical function
local attribute [instance] prop_decidable


namespace category_theory

universes u v

namespace groupoid

variables {C : Type u} [groupoid C] (S : subgroupoid C) (Sn : S.is_normal)

namespace quotient

open subgroupoid

section isotropy
/-!
We first define what's here called “isotropy quotient”:
Given a normal subgroupoid `S`, this quotient is collapses all loops of `S`, that is
all vertex groups.
After quotienting by these vertex groups, the image of `S` in the quotient `is_graph_like`
which is easy to quotient out again.
-/

section congr

variables {c d : C} (f g h : c ⟶ d)

def congr := ∃ (γ ∈ S.arrows c c) (δ ∈ S.arrows d d), g = γ ≫ f ≫ δ
def cgr (c) (d) (f) (g) := @congr _ _ S c d f g
/-
lemma congr.refl (f : c ⟶ d) : congr S f f :=  ⟨(𝟙 c), Sn.wide c, (𝟙 d), Sn.wide d, by simp ⟩
lemma congr.symm {f g : c ⟶ d} : congr S f g → congr S g f :=
λ ⟨γ,hγ,δ,hδ,e⟩, ⟨inv γ, S.inv hγ, inv δ, S.inv hδ, by { rw e, simp, } ⟩
lemma congr.tran {f g h : c ⟶ d} : congr S f g → congr S g h → congr S f h :=
λ ⟨γ,hγ,δ,hδ,e⟩ ⟨δ',hδ',ε,hε,e'⟩,
⟨δ' ≫ γ, S.mul hδ' hγ, δ ≫ ε, S.mul hδ hε, by {rw [e',e], simp, }⟩
-/
end congr

def isotropy.quotient (S : subgroupoid C) (Sn : S.is_normal) := C

namespace isotropy

instance : groupoid (isotropy.quotient S Sn) :=
{ hom := λ c d, quot (cgr S c d),
  id := λ c, quot.mk _ (𝟙 c),
  comp := λ a b c f g,
    quot.lift_on₂ f g
      ( λ f g, quot.mk (cgr S a c) (f ≫ g) )
      ( λ f g₁ g₂ ⟨γ,hγ,δ,hδ,e⟩,
        quot.sound ⟨(f ≫ γ ≫ inv f), Sn.conj' f hγ, δ, hδ, by { rw e, simp only [inv_eq_inv, category.assoc, is_iso.inv_hom_id_assoc], } ⟩ )
      ( λ f₁ f₂ g ⟨γ,hγ,δ,hδ,e⟩,
        quot.sound ⟨γ, hγ, (inv g ≫ δ ≫ g), Sn.conj g hδ, by { rw e, simp only [category.assoc, inv_eq_inv, is_iso.hom_inv_id_assoc], } ⟩ ),
  comp_id' := λ a b, by
    { refine quot.ind (λ f, _),
      simp only [quot.lift_on₂_mk, category.comp_id], },
  id_comp' := λ a b, by
    { refine quot.ind (λ f, _),
      simp only [quot.lift_on₂_mk, category.id_comp], },
  assoc' :=  λ a b c d f g h, by
    { refine quot.induction_on₃ f g h (λ f g h, _),
      simp only [quot.lift_on₂_mk, category.assoc],  },
  inv := λ a b f,
    quot.lift_on f
      ( λ f, quot.mk (cgr S b a) (inv f) )
      ( λ f₁ f₂ ⟨γ,hγ,δ,hδ,e⟩, quot.sound ⟨inv δ, S.inv hδ, inv γ, S.inv hγ, by { rw e, simp, } ⟩ ),
  comp_inv' := λ a b f, by
    { refine quot.induction_on f (λ f, _),
      simp only [quot.lift_on₂_mk, inv_eq_inv, is_iso.hom_inv_id], },
  inv_comp' := λ a b f, by
    { refine quot.induction_on f (λ f, _),
      simp only [quot.lift_on₂_mk, inv_eq_inv, is_iso.inv_hom_id], }, }

def of : C ⥤ (quotient S Sn) :=
{ obj := λ c, c,
  map := λ c d f, quot.mk _ f,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ _ _, rfl, }

lemma of_inj_on_objects : function.injective (of S Sn).obj := by { intros a b e, assumption }

lemma of_onto : im (of S Sn) (of_inj_on_objects S Sn) = (⊤ : subgroupoid $ quotient S Sn) :=
le_antisymm (le_top) $ λ ⟨c,d,f⟩ _, quot.induction_on f (λ f, by { constructor, constructor, })


/-- The image of `S` via the quotient is graph-like (since every loop is killed, essentially) -/
lemma map_is_graph_like : (map (of S Sn) (of_inj_on_objects S Sn) S).is_graph_like :=
begin
  rw subgroupoid.is_graph_like_iff,
  rintro c d,
  constructor,
  rintro ⟨_,hf⟩ ⟨_,hg⟩,
  cases hf,
  cases hg,
  simp only [subtype.mk_eq_mk],
  apply quot.sound,
  refine ⟨𝟙 _, Sn.wide _, inv hf_f ≫ hg_f, S.mul (S.inv _) _, _⟩,
  assumption,
  assumption,
  simp only [inv_eq_inv, is_iso.hom_inv_id_assoc, category.id_comp],
end

section ump
/-!
The universal mapping property of the quotient by the isotropy part of a normal subgroupoid.
-/

variables  {D : Type*} [groupoid D]
  (φ : C ⥤ D) (hφ : ∀ (c : C) (γ : c ⟶ c), γ ∈ₐ S → γ ∈ₐ ker φ)

include hφ
def lift : (quotient S Sn) ⥤ D :=
{ obj := λ c, φ.obj c,
  map := λ c d f,
    quot.lift_on f
      ( λ f, φ.map f )
      ( λ f₁ f₂ ⟨γ,hγ,δ,hδ,e⟩, by
        { let hφγ := hφ c γ hγ,
          let hφδ := hφ d δ hδ,
          simp only [mem_subgroupoid_iff, mem_ker_iff, eq_self_iff_true,
                     exists_true_left] at hφγ hφδ,
          simp only [e, functor.map_comp,hφγ,hφδ,category.comp_id,category.id_comp,
                     eq_to_hom_refl], } ),
  map_id' := λ c, by simp,
  map_comp' := λ a b c f g, by { apply quot.induction_on₂ f g, rintros, simp, } }

lemma lift_spec : (of S Sn) ⋙ (lift S Sn φ hφ) = φ :=
begin
  apply functor.ext,
  { rintros, dsimp only [of, lift], simp, },
  { rintros, dsimp only [of, lift], simp, },
end

lemma lift_unique (Φ : (quotient S Sn) ⥤ D) (hΦ : (of S Sn) ⋙ Φ = φ) :
  Φ = (lift S Sn φ hφ) :=
begin
  subst_vars,
  apply functor.ext,
  { rintros, dsimp [of, lift], apply quot.induction_on f, rintro f, simp, },
  { rintros, dsimp only [of, lift], refl, }
end

end ump

end isotropy

end isotropy


namespace graph_like
/-!
Quotient of a groupoid by a normal, graph-like subgroupoid.
By graph-likeness, the quotient be represented by the full subgroupoid induced by taking any
set of representatives of the vertices, which makes dealing with quotients easier.
-/

variable (Sg : S.is_graph_like)

abbreviation r := λ c d, nonempty (S.arrows c d)

lemma r.refl (c : C) : r S c c := ⟨⟨𝟙 c, Sn.wide c⟩⟩
lemma r.symm {c d : C} : r S c d → r S d c := λ ⟨⟨f,fS⟩⟩, ⟨⟨inv f, S.inv fS⟩⟩
lemma r.tran {c d e : C} : r S c d → r S d e → r S c e := λ ⟨⟨f,fS⟩⟩ ⟨⟨g,gS⟩⟩, ⟨⟨f≫g, S.mul fS gS⟩⟩

 def R : setoid C :=
{ r := r S ,  iseqv := ⟨λ _, r.refl S Sn _, λ _ _, r.symm S, λ _ _ _, r.tran S⟩ }

instance : setoid C := R S Sn

abbreviation C_by_r := _root_.quotient (R S Sn)

abbreviation r_reps : set C := set.range (@quotient.out C (R S Sn))

def quotient := (full_on $ r_reps S Sn).coe

instance : groupoid (quotient S Sn) := (full_on $ r_reps S Sn).coe_groupoid

abbreviation qmk := @_root_.quotient.mk _ (R S Sn)
noncomputable abbreviation qout := @quotient.out _ (R S Sn)
abbreviation qouteq := @quotient.out_eq _ (R S Sn)
abbreviation qex := @quotient.exact _ (R S Sn)

@[simp] lemma noname (c : C) : qout S Sn (qmk S Sn c) ∈ r_reps S Sn := ⟨qmk S Sn c, rfl⟩

lemma qoutmk (c : C) : (R S Sn).r (qout S Sn (qmk S Sn c)) c :=
begin
  apply qex,
  simp only [quotient.out_eq],
end

lemma in_quotient (c : quotient S Sn) : ∃ (c₀ : C), c.val = (qout S Sn $ qmk S Sn c₀) :=
begin
  obtain ⟨c₀,⟨_,⟨_,⟨c,h⟩⟩⟩⟩ := c,
  use c₀,
  simp only [←h, quotient.out_inj],
  letI := R S Sn,
  change c = ⟦c.out⟧,
  simp only [quotient.out_eq],
end


noncomputable def of : C ⥤ quotient S Sn :=
{ obj := λ c,
  ⟨ qout S Sn (qmk S Sn c),
    by { refine ⟨𝟙 (qout S Sn $ qmk S Sn c),_⟩, constructor; simp, } ⟩,
  map := λ c d f,
    let
      γ := (qex S Sn (qouteq S Sn (qmk S Sn c))).some.val,
      δ := inv (qex S Sn (qouteq S Sn (qmk S Sn d))).some.val
    in
      ⟨γ ≫ f ≫ δ, by { constructor; simp, } ⟩,
  map_id' := λ _, by
    { simp only [subtype.val_eq_coe, inv_eq_inv, category.id_comp, is_iso.hom_inv_id],
      refl, },
  map_comp' := λ _ _ _ _ _, by
    { ext,
      simp only [inv_eq_inv, category.assoc, subtype.coe_mk, coe_groupoid_to_category_comp_coe,
                 is_iso.inv_hom_id_assoc], } }

def fo : (quotient S Sn) ⥤ C := coe_embedding _

section ump

variables {D : Type*} [groupoid D] (φ : C ⥤ D) (hφ : S ≤ ker φ)

def lift : quotient S Sn ⥤ D := (fo S Sn) ⋙ φ

include hφ
lemma lift_spec : (of S Sn) ⋙ (lift S Sn φ) = φ :=
begin
  dsimp only [lift, of, fo, full_on, coe_embedding],
  fapply functor.ext,
  { rintro c,
    simp only [functor.comp_obj],
    obtain ⟨γ,γS⟩ := (qoutmk S Sn c).some,
    let := hφ γS, rw mem_ker_iff at this,
    exact this.some, },
  { rintro c d f,
    simp only [subtype.val_eq_coe, inv_eq_inv, functor.comp_map,
               functor.map_comp, functor.map_inv],

    obtain ⟨γ,hγ⟩ := (qex S Sn (qouteq S Sn (qmk S Sn c))).some,
    obtain ⟨δ,hδ⟩ := (qex S Sn (qouteq S Sn (qmk S Sn d))).some,
    let hγ' := hφ hγ,
    let hδ' := hφ hδ,
    rw mem_ker_iff at hγ' hδ',
    obtain ⟨eγ,hγ'⟩ := hγ',
    obtain ⟨eδ,hδ'⟩ := hδ',
    simp only [subtype.coe_mk,hδ',hγ',inv_eq_to_hom], refl, },
end

lemma lift_unique (Φ : quotient S Sn ⥤ D) (hΦ : (of S Sn) ⋙ Φ = φ) :
  Φ = (lift S Sn φ) :=
begin
  letI := R S Sn,
  subst_vars,
  dsimp [lift],
  fapply functor.ext,
  { rintro ⟨c₀,⟨_,⟨_,⟨c,h⟩⟩⟩⟩,
    simp only [lift, of, fo, full_on, coe_embedding, functor.comp_obj],
    congr,
    rw ←h,
    change c.out = ⟦c.out⟧.out,
    simp only [quotient.out_eq], },
  { rintro ⟨c,⟨_,⟨_,⟨c₀,hc⟩⟩⟩⟩ ⟨d,⟨_,⟨_,⟨d₀,hd⟩⟩⟩⟩ f,
    obtain ⟨γ,hγ⟩ := (qex S Sn (qouteq S Sn (qmk S Sn c))).some,
    obtain ⟨δ,hδ⟩ := (qex S Sn (qouteq S Sn (qmk S Sn d))).some,
    let hγ' := hφ hγ,
    let hδ' := hφ hδ,
    rw mem_ker_iff at hγ' hδ',
    obtain ⟨eγ,hγ'⟩ := hγ',
    obtain ⟨eδ,hδ'⟩ := hδ',
    dsimp only [lift, of, fo, full_on, coe_embedding] at *,
    simp only [inv_eq_inv, functor.comp_map] at *,

    sorry },
end

end ump

end graph_like

section quotient

def _root_.category_theory.groupoid.quotient :=
  graph_like.quotient
    (map (isotropy.of S Sn) (isotropy.of_inj_on_objects S Sn) S)
    (is_normal_map
      S
      (isotropy.of S Sn)
      (isotropy.of_inj_on_objects S Sn)
      (isotropy.of_onto S Sn)
      Sn)

instance quotient_groupoid : groupoid (quotient S Sn) :=
  graph_like.quotient.category_theory.groupoid
    (map /-(isotropy.of S Sn)-/ _ (isotropy.of_inj_on_objects S Sn) S)
    (is_normal_map
      /-S-/ _
      /-(isotropy.of S Sn)-/ _
      (isotropy.of_inj_on_objects S Sn)
      (isotropy.of_onto S Sn)
      Sn)

noncomputable def of : C ⥤ quotient S Sn := (isotropy.of _ _) ⋙ (graph_like.of _ _)

section ump

variables {D : Type*} [groupoid D] (φ : C ⥤ D) (hφ : S ≤ ker φ)

include hφ
def lift : quotient S Sn ⥤ D :=
begin
  apply graph_like.lift,
  fapply isotropy.lift,
  exact φ,
  rintro c γ γS, exact hφ γS,
end

lemma lift_spec : (of S Sn) ⋙ (quotient.lift S Sn φ hφ) = φ :=
begin
  change isotropy.of S Sn ⋙ (graph_like.of (map (isotropy.of S Sn) _ S) _) ⋙
    graph_like.lift (map (isotropy.of S Sn) _ S) _ (isotropy.lift S Sn φ _) = φ,
  rw graph_like.lift_spec,
  apply isotropy.lift_spec,
  { rintros a b f ⟨_,_,g,gS⟩,
    exact hφ gS, },
end


def lift_unique (Φ : quotient S Sn ⥤ D) (hΦ : (of S Sn) ⋙ Φ = φ) :
  Φ = (quotient.lift S Sn φ hφ) :=
begin
  apply graph_like.lift_unique,
  { rintros a b f ⟨_,_,g,gS⟩,
    exact hφ gS, },
  apply isotropy.lift_unique,
  exact hΦ,
end

end ump

end quotient

end quotient

end groupoid

end category_theory
