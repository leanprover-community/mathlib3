import .vertex_group
import .subgroupoid
import category_theory.groupoid
import algebra.group.defs
import algebra.hom.group
import algebra.hom.equiv
import data.set.lattice
import combinatorics.quiver.connected_component

open set classical function
local attribute [instance] prop_decidable


namespace category_theory

universes u v

variables {C : Type u} [groupoid C] (S : groupoid.subgroupoid C) (Sn : S.is_normal)

namespace groupoid

namespace subgroupoid

lemma is_normal.arrws_nonempty_refl {S : subgroupoid C} (Sn : S.is_normal) (c : C) :
  (S.arrws c c).nonempty :=
⟨𝟙 c, Sn.wide c⟩

lemma is_normal.arrws_nonempty_symm {S : subgroupoid C} (Sn : S.is_normal)
  {c d : C} : (S.arrws c d).nonempty → (S.arrws d c).nonempty :=
by { rintro ⟨f, hf⟩, exact ⟨groupoid.inv f, S.inv' hf⟩ }

lemma is_normal.arrws_nonempty_trans {S : subgroupoid C} (Sn : S.is_normal)
  {c d e : C} : (S.arrws c d).nonempty → (S.arrws d e).nonempty → (S.arrws c e).nonempty :=
by { rintro ⟨f, hf⟩ ⟨g, hg⟩, exact ⟨f ≫ g, S.mul' hf hg⟩ }

def is_normal.arrws_nonempty_setoid {S : subgroupoid C} (Sn : S.is_normal) : setoid C :=
{ r := λ c d, (S.arrws c d).nonempty,
  iseqv := ⟨Sn.arrws_nonempty_refl,
            λ c d, Sn.arrws_nonempty_symm,
            λ c d e, Sn.arrws_nonempty_trans⟩ }

end subgroupoid

open subgroupoid

section quotient

open subgroupoid

-- The vertices of the quotient of G by S
@[reducible] def quot_v := quotient Sn.arrws_nonempty_setoid

def quot_v_mk (c : C) : quot_v S Sn := quotient.mk' c

def subgroupoid.conj {a b c d : C} (f : a ⟶ b) (g : c ⟶ d) : Prop :=
∃ (α ∈ S.arrws a c) (β ∈ S.arrws d b), f = α ≫ g ≫ β

attribute [reassoc] inv_comp comp_inv -- groupoid

lemma conj.refl {a b : C} (f : a ⟶ b) : S.conj f f := ⟨_, Sn.wide _, _, Sn.wide _, by simp⟩

lemma conj.symm {a b c d : C} (f : a ⟶ b) (g : c ⟶ d) : S.conj f g → S.conj g f :=
λ ⟨α, hα, β, hβ, he⟩, ⟨_, S.inv' hα, _, S.inv' hβ, by simp [he]⟩

lemma conj_comm {a b c d : C} (f : a ⟶ b) (g : c ⟶ d) : S.conj f g ↔ S.conj g f :=
⟨conj.symm S f g, conj.symm S g f⟩

lemma conj.trans {a b c d e f : C} (g : a ⟶ b) (h : c ⟶ d) (i : e ⟶ f) :
  S.conj g h → S.conj h i → S.conj g i :=
λ ⟨α₁, hα₁, β₁, hβ₁, he₁⟩ ⟨α₂, hα₂, β₂, hβ₂, he₂⟩,
  ⟨_, S.mul' hα₁ hα₂, _, S.mul' hβ₂ hβ₁, by simp [he₁, he₂]⟩

def conj_setoid (a b : quot_v S Sn) :
  setoid (Σ (c : {c // quot.mk _ c = a}) (d : {d // quot.mk _ d = b}), c.1 ⟶ d.1) :=
{ r := λ f g, S.conj f.2.2 g.2.2,
  iseqv := ⟨λ _, conj.refl _ Sn _, λ _ _, conj.symm _ _ _, λ _ _ _, conj.trans _ _ _ _⟩ }

lemma conj_comp {a b c d e : C} (f : a ⟶ b) (g : c ⟶ d) {h : d ⟶ e} (hS : h ∈ S.arrws d e) :
  S.conj f (g ≫ h) ↔ S.conj f g :=
⟨λ ⟨α, hα, β, hβ, he⟩, ⟨α, hα, h ≫ β, S.mul' hS hβ, by simp [he]⟩,
 λ ⟨α, hα, β, hβ, he⟩, ⟨α, hα, inv h ≫ β, S.mul' (S.inv' hS) hβ, by simp [he]⟩⟩

lemma conj_comp' {a b c d e : C} (f : a ⟶ b) (g : c ⟶ d) {h : e ⟶ c} (hS : h ∈ S.arrws e c) :
  S.conj f (h ≫ g) ↔ S.conj f g :=
⟨λ ⟨α, hα, β, hβ, he⟩, ⟨α ≫ h, S.mul' hα hS, β, hβ, by simp [he]⟩,
 λ ⟨α, hα, β, hβ, he⟩, ⟨α ≫ inv h, S.mul' hα (S.inv' hS), β, hβ, by simp [he]⟩⟩

lemma conj_inv {a b c d: C} (f : a ⟶ b) (g : c ⟶ d) :
  S.conj f g → S.conj (inv f) (inv g) :=
λ ⟨α, hα, β, hβ, he⟩,
  ⟨inv β, S.inv' hβ, inv α, S.inv' hα, by {simp only [inv_eq_inv,←is_iso.inv_comp],congr,simp [he]}⟩

lemma conj_congr_left {a b c d : C} (f₁ : a ⟶ c) (f₂ : b ⟶ c) (g : c ⟶ d) (h : S.conj f₁ f₂) :
  S.conj (f₁ ≫ g) (f₂ ≫ g) :=
let ⟨α, hα, β, hβ, he⟩ := h in ⟨α, hα, (inv g) ≫  β ≫ g, Sn.conj g β hβ, by simp [he]⟩

lemma conj_congr_right {a b c d : C} (f : a ⟶ b) (g₁ : b ⟶ c) (g₂ : b ⟶ d) (h : S.conj g₁ g₂) :
  S.conj (f ≫ g₁) (f ≫ g₂) :=
let ⟨α, hα, β, hβ, he⟩ := h in ⟨_, Sn.conj (groupoid.inv f) _ hα, β, hβ, by simp [he]⟩

@[instance]
def quotient_quiver : quiver (quot_v S Sn) :=
{ hom := λ a b, quotient (conj_setoid S Sn a b) }

noncomputable def quot_id (c : quot_v S Sn) : c ⟶ c :=
quot.mk _ ⟨⟨quot.out c, quot.out_eq c⟩, ⟨quot.out c, quot.out_eq c⟩, 𝟙 (quot.out c)⟩

noncomputable def quot_comp {c d e : quot_v S Sn} : (c ⟶ d) → (d ⟶ e) → (c ⟶ e) :=
begin
  let sm := @nonempty.some_mem,
  refine quot.lift₂ (λ f g, quot.mk _ _) (λ f g₁ g₂ h, _) (λ f₁ f₂ g h, _),
  { letI := Sn.arrws_nonempty_setoid,
    exact ⟨_, _, f.2.2 ≫ (quotient.exact $ f.2.1.2.trans g.1.2.symm).some ≫ g.2.2⟩ },
  all_goals { apply quot.sound, dsimp only [conj_setoid] },
  { apply conj_congr_right S Sn,
    rw [conj_comp' S _ _ (sm _), conj_comm, conj_comp' S _ _ (sm _), conj_comm],
    exact h },
  { simp only [← category.assoc],
    apply conj_congr_left S Sn,
    rw [conj_comp S _ _ (sm _), conj_comm, conj_comp S _ _ (sm _), conj_comm],
    exact h },
end

def quot_inv {c d : quot_v S Sn} : (c ⟶ d) → (d ⟶ c) :=
begin
  refine quot.lift (λ f, quot.mk _ _) (λ f₁ f₂ h, _),
  { exact ⟨f.2.1, f.1, inv f.2.2⟩ },
  { apply quot.sound,
    dsimp only [conj_setoid], apply conj_inv, exact h, },
end

@[instance]
noncomputable def quotient_category_struct : category_struct (quot_v S Sn) :=
{ to_quiver := quotient_quiver S Sn
, id := quot_id S Sn
, comp := λ _ _ _, quot_comp S Sn }

@[instance]
noncomputable def quotient_category : category (quot_v S Sn) :=
{ to_category_struct := quotient_category_struct S Sn
, comp_id' := by
  { letI := Sn.arrws_nonempty_setoid,
    rintros,
    refine quot.induction_on f (λ a, quot.sound _),
    dsimp only [conj_setoid], simp only [category.comp_id],
    rw [conj_comm, conj_comp S _ _ (quotient.exact $ a.2.1.2.trans (quot.out_eq Y).symm).some_mem],
    apply conj.refl S Sn, }
, id_comp' := by
  { letI := Sn.arrws_nonempty_setoid,
    rintros,
    refine quot.induction_on f (λ a, quot.sound _),
    dsimp only [conj_setoid], simp only [category.id_comp],
    rw [conj_comm, conj_comp' S _ _ (quotient.exact $ (quot.out_eq X).trans a.1.2.symm).some_mem],
    apply conj.refl S Sn, }
, assoc' := by
  { letI := Sn.arrws_nonempty_setoid,
    rintros,
    refine quot.induction_on₃ f g h (λ f g h, quot.sound _),
    dsimp only [conj_setoid], simp only [category.assoc],
    apply conj.refl S Sn, }
 }

noncomputable instance groupoid : groupoid (quot_v S Sn) :=
{ to_category := quotient_category S Sn
, inv := λ _ _, quot_inv S Sn
, inv_comp' := by
  { letI := Sn.arrws_nonempty_setoid,
    rintros,
    refine quot.induction_on f (λ f, quot.sound _),
    dsimp only [conj_setoid],
    rcases f with ⟨⟨a,rfl⟩,⟨b,rfl⟩,f⟩,
    simp only [inv_eq_inv],
    have : (S.arrws a a).nonempty := subgroupoid.is_normal.arrws_nonempty_refl Sn a,
    let sS := this.some_mem,
    let s := this.some,
    have : S.conj (inv f ≫ s ≫ f) (𝟙 (quot.mk setoid.r b).out), by
    { let t := inv f ≫ s ≫ f,
      let tS : t ∈ S.arrws b b := Sn.conj f s sS,
      let G := setoid.symm (quotient.exact $ quot.out_eq (quot.mk setoid.r a)),
      show S.conj t (𝟙 (quot.mk setoid.r b).out),
      sorry, --use [inv G.some],-- G.some_mem, (G.some ≫ t), S.mul' G.some_mem tS], --S.inv' G.some_mem, (G.some ≫ t), S.mul' G.some_mem tS], simp, },
      },
    convert this, simp, }
, comp_inv' := by
  { letI := Sn.arrws_nonempty_setoid,
    rintros,
    refine quot.induction_on f (λ f, quot.sound _),
    dsimp only [conj_setoid],
    rcases f with ⟨⟨a,rfl⟩,⟨b,rfl⟩,f⟩,
    have ss : (S.arrws b b).nonempty := subgroupoid.is_normal.arrws_nonempty_refl Sn b,
    let t := f ≫ ss.some ≫ inv f,
    let tS : t ∈ S.arrws a a := Sn.conj' f ss.some ss.some_mem,
    let G := (quotient.exact $ quot.out_eq (quot.mk setoid.r a)),
    use [inv G.some, S.inv' G.some_mem, (G.some ≫ t), S.mul' G.some_mem tS],
    simp only [inv_eq_inv, category.id_comp, is_iso.inv_hom_id_assoc] at *,
    rw ←inv_eq_inv, refl,
  } }

end quotient

section ump

open subgroupoid

def of : C ⥤ quot_v S Sn :=
{ obj := λ v, quot_v_mk S Sn v,
  map := λ a b f, quot.mk _ $ by { use [a,rfl,b,rfl,f], },
  map_id' := λ a, by
  { letI := Sn.arrws_nonempty_setoid,
    apply quot.sound,
    let h := quotient.exact (quot.out_eq (quot_v_mk S Sn a)),
    use [inv h.some, S.inv' h.some_mem, h.some, h.some_mem],
    simp only [inv_eq_inv, category.id_comp, is_iso.inv_hom_id],
  },
  map_comp' := λ a b c f g, by
  { letI := Sn.arrws_nonempty_setoid,
    dsimp [category_struct.comp, quot_comp],
    apply quotient.sound, simp, dsimp,
    have h : (S.arrws b b).nonempty := subgroupoid.is_normal.arrws_nonempty_refl Sn b,
    symmetry,
    use [f ≫ h.some ≫ inv f, Sn.conj' f h.some h.some_mem, 𝟙 c, Sn.wide c],
    simp only [inv_eq_inv, category.assoc, category.comp_id, is_iso.inv_hom_id_assoc], refl, } }

def lift {D : Type v} [groupoid D] {S} {Sn} (φ : C ⥤ D)
  (hφ : S ≤ ker φ) : (quot_v S Sn) ⥤ D := sorry

lemma lift_spec {D : Type v} [groupoid D] {S} {Sn} (φ : C ⥤ D) -- strange: can't write `lift φ hφ`
  (hφ : S ≤ ker φ) : (of S Sn) ⋙ (lift φ sorry) = φ := sorry

lemma lift_spec_unique {D : Type v} [groupoid D] {S} {Sn} (φ : C ⥤ D) (hφ : S ≤ ker φ)
  (Φ : (quot_v S Sn) ⥤ D) (hΦ : (of S Sn) ⋙ Φ = φ) : Φ = (lift φ sorry) := sorry

end ump

end groupoid

end category_theory
