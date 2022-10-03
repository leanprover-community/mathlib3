import category_theory.groupoid.vertex_group
import category_theory.groupoid.subgroupoid
import category_theory.groupoid
import algebra.group.defs
import algebra.hom.group
import algebra.hom.equiv
import data.set.lattice

open set classical function
local attribute [instance] prop_decidable


namespace category_theory

universes u v

variables {C : Type u} [groupoid C] (S : groupoid.subgroupoid C)
  (Sn : S.is_normal) (Sg : S.is_graph_like)

namespace groupoid

namespace subgroupoid

namespace is_graph_like
/-!
Quotient of a groupoid by a normal, graph-like subgroupoid.
By graph-likeness, the quotient be represented by the full subgroupoid induced by taking any
set of representatives of the vertices, which makes dealing with quotients easier.
-/

abbreviation r := λ c d, nonempty (S.arrws c d)

lemma r.refl (c : C) : r S c c := ⟨⟨𝟙 c, Sn.wide c⟩⟩
lemma r.symm {c d : C} : r S c d → r S d c := λ ⟨⟨f,fS⟩⟩, ⟨⟨inv f, S.inv' fS⟩⟩
lemma r.tran {c d e : C} : r S c d → r S d e → r S c e := λ ⟨⟨f,fS⟩⟩ ⟨⟨g,gS⟩⟩, ⟨⟨f≫g, S.mul' fS gS⟩⟩

 def R : setoid C :=
{ r := r S ,  iseqv := ⟨λ _, r.refl S Sn _, λ _ _, r.symm S, λ _ _ _, r.tran S⟩ }

instance : setoid C := R S Sn

def C_by_r := quotient (R S Sn)

def r_reps : set C := set.range (@quotient.out C (R S Sn))

def quotient := (full_on $ r_reps S Sn).coe

instance : groupoid (quotient S Sn) := (full_on $ r_reps S Sn).coe_groupoid

abbreviation qmk := @quotient.mk _ (R S Sn)
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
