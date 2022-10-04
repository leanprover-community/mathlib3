import category_theory.groupoid.vertex_group
import category_theory.groupoid.subgroupoid
import category_theory.groupoid
import category_theory.groupoid.basic


open set classical function
local attribute [instance] prop_decidable


namespace category_theory

universes u v

namespace groupoid

variables {C : Type u} [groupoid C] (S : subgroupoid C) (Sn : S.is_normal)

namespace subgroupoid

section isotropy_quotient

section congr

variables {c d : C} (f g h : c ⟶ d)

def congr := ∃ (γ ∈ S.arrws c c) (δ ∈ S.arrws d d), g = γ ≫ f ≫ δ
def cgr (c) (d) (f) (g) := ∃ (γ ∈ S.arrws c c) (δ ∈ S.arrws d d), g = γ ≫ f ≫ δ


lemma congr.refl (f : c ⟶ d) : congr S f f :=  ⟨(𝟙 c), Sn.wide c, (𝟙 d), Sn.wide d, by simp ⟩
lemma congr.symm {f g : c ⟶ d} : congr S f g → congr S g f :=
λ ⟨γ,hγ,δ,hδ,e⟩, ⟨inv γ, S.inv' hγ, inv δ, S.inv' hδ, by { rw e, simp, } ⟩
lemma congr.tran {f g h : c ⟶ d} : congr S f g → congr S g h → congr S f h :=
λ ⟨γ,hγ,δ,hδ,e⟩ ⟨δ',hδ',ε,hε,e'⟩,
⟨δ' ≫ γ, S.mul' hδ' hγ, δ ≫ ε, S.mul' hδ hε, by {rw [e',e], simp, }⟩

def R (c d) : setoid (c ⟶ d) :=
{ r := congr S ,  iseqv := ⟨λ _, congr.refl S Sn _, λ _ _, congr.symm S, λ _ _ _, congr.tran S⟩ }

end congr

def isotropy_quotient (S : subgroupoid C) (Sn : S.is_normal) := C

@[instance,simps]
def category_struct_isotropy_quotient : category_struct (isotropy_quotient S Sn) :=
{ hom := λ c d, quot (cgr S c d),
  id := λ c, quot.mk _ (𝟙 c),
  comp := λ a b c f g,
    quot.lift_on₂ f g
      ( λ f g, quot.mk (cgr S a c) (f ≫ g) )
      ( λ f g₁ g₂ ⟨γ,hγ,δ,hδ,e⟩,
        quot.sound ⟨(f ≫ γ ≫ inv f), Sn.conj' f γ hγ, δ, hδ, by { rw e, simp, } ⟩ )
      ( λ f₁ f₂ g ⟨γ,hγ,δ,hδ,e⟩,
        quot.sound ⟨γ, hγ, (inv g ≫ δ ≫ g), Sn.conj g δ hδ, by { rw e, simp, } ⟩ ) }

instance groupoid_isotropy_quotient : groupoid (isotropy_quotient S Sn) :=
{ to_category_struct := category_struct_isotropy_quotient S Sn,
  comp_id' := λ a b, by
    { refine quot.ind (λ f, _),
      rw [category_struct_isotropy_quotient_id, category_struct_isotropy_quotient_comp,
      quot.lift_on₂_mk, category.comp_id], },
  id_comp' := λ a b, by
    { refine quot.ind (λ f, _),
      rw [category_struct_isotropy_quotient_id, category_struct_isotropy_quotient_comp,
      quot.lift_on₂_mk, category.id_comp], },
  assoc' :=  λ a b c d f g h, by
    { refine quot.induction_on₃ f g h (λ f g h, _),
      simp [category_struct_isotropy_quotient_comp, quot.lift_on₂_mk, category.assoc],  },
  inv := λ a b f,
    quot.lift_on f
      ( λ f, quot.mk (cgr S b a) (inv f) )
      ( λ f₁ f₂ ⟨γ,hγ,δ,hδ,e⟩, quot.sound ⟨inv δ, S.inv' hδ, inv γ, S.inv' hγ, by { rw e, simp, } ⟩ ),
  comp_inv' := λ a b f, by
    { refine quot.induction_on f (λ f, _),
      simp, },
  inv_comp' := λ a b f, by
    { refine quot.induction_on f (λ f, _),
      simp, }, }

def of : C ⥤ (isotropy_quotient S Sn) :=
{ obj := λ c, c,
  map := λ c d f, quot.mk _ f,
  map_id' := λ c, by simp,
  map_comp' := λ a b c f g, by simp }

lemma of_injective : function.injective (of S Sn).obj := by { intros a b e, assumption }

lift 


end isotropy_quotient




namespace is_graph_like
/-!
Quotient of a groupoid by a normal, graph-like subgroupoid.
By graph-likeness, the quotient be represented by the full subgroupoid induced by taking any
set of representatives of the vertices, which makes dealing with quotients easier.
-/

variable (Sg : is_graph_like (S.coe))

abbreviation r := λ c d, nonempty (S.arrws c d)

lemma r.refl (c : C) : r S c c := ⟨⟨𝟙 c, Sn.wide c⟩⟩
lemma r.symm {c d : C} : r S c d → r S d c := λ ⟨⟨f,fS⟩⟩, ⟨⟨inv f, S.inv' fS⟩⟩
lemma r.tran {c d e : C} : r S c d → r S d e → r S c e := λ ⟨⟨f,fS⟩⟩ ⟨⟨g,gS⟩⟩, ⟨⟨f≫g, S.mul' fS gS⟩⟩

 def R : setoid C :=
{ r := r S ,  iseqv := ⟨λ _, r.refl S Sn _, λ _ _, r.symm S, λ _ _ _, r.tran S⟩ }

instance : setoid C := R S Sn

def C_by_r := _root_.quotient (R S Sn)

def r_reps : set C := set.range (@quotient.out C (R S Sn))

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


lemma fo_of : (fo S Sn) ⋙ (of S Sn) = 𝟭 _ :=
begin
  dsimp only [of,fo,coe_embedding,full_on],
  simp only [inv_eq_inv],
  fapply functor.ext,
  { rintro ⟨c,hc⟩,
    simp only [functor.comp_obj, functor.id_obj, subtype.mk_eq_mk],
    cases hc, cases hc_h, cases hc_h_hc, subst_vars,
    simp only [quotient.out_inj], apply quotient.out_eq, },
  { rintros ⟨c,hc⟩ ⟨d,hd⟩ ⟨f,hf⟩,
    simp only [functor.comp_map, functor.id_map],
    cases hc, cases hc_h, cases hc_h_hc,
    cases hd, cases hd_h, cases hd_h_hd,
    cases hf, cases hf_hc, cases  hf_hd,
    subst_vars, ext, simp,
    sorry,
   }
end


section ump

variables {D : Type*} [groupoid D] (φ : C ⥤ D) (hφ : S ≤ ker φ)

def lift : quotient S Sn ⥤ D := (fo S Sn) ⋙ φ

include hφ
lemma lift_spec : (of S Sn) ⋙ (lift S Sn φ) = φ :=
begin
  dsimp [lift, of, fo, full_on, coe_embedding], simp,
  apply functor.hext,
  { rintro c, simp, }
end

lemma fo_of : (fo S Sn) ⋙ (of S Sn) = 𝟭 _ :=
begin

end

def lift_spec_unique (Φ : quotient S Sn ⥤ D) (hΦ : (of S Sn) ⋙ Φ = φ) : Φ = (lift S Sn φ) :=
begin
  subst hΦ, sorry,
end

end ump


end is_graph_like
end subgroupoid

end groupoid

end category_theory
