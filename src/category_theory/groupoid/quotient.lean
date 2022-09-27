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

lemma conj_congr_left {a b c d : C} (f₁ : a ⟶ c) (f₂ : b ⟶ c) (g : c ⟶ d) (h : S.conj f₁ f₂) :
  S.conj (f₁ ≫ g) (f₂ ≫ g) :=
let ⟨α, hα, β, hβ, he⟩ := h in ⟨α, hα, (inv g) ≫  β ≫ g, Sn.conj g β hβ, by simp [he]⟩

lemma conj_congr_right {a b c d : C} (f : a ⟶ b) (g₁ : b ⟶ c) (g₂ : b ⟶ d) (h : S.conj g₁ g₂) :
  S.conj (f ≫ g₁) (f ≫ g₂) :=
let ⟨α, hα, β, hβ, he⟩ := h in ⟨_, Sn.conj (groupoid.inv f) _ hα, β, hβ, by simp [he]⟩

@[instance]
def quotient_quiver : quiver (quot_v S Sn) := ⟨λ a b, quotient (conj_setoid S Sn a b)⟩

noncomputable def quot_id (c : quot_v S Sn) : (c ⟶ c)  :=
begin
  sorry
end

noncomputable def quot_comp {c d e : quot_v S Sn} : (c ⟶ d) → (d ⟶ e) → (c ⟶ e) :=
begin
  let sm := @nonempty.some_mem,
  refine quot.lift₂ (λ f g, quot.mk _ _) (λ f g₁ g₂ h, _) (λ f₁ f₂ g h, _),
  { letI := Sn.arrws_nonempty_setoid,
    exact ⟨_, _, f.2.2 ≫ (quotient.exact $ f.2.1.2.trans g.1.2.symm).some ≫ g.2.2⟩ },
  all_goals { apply quot.sound, dsimp only [conj_setoid] },
  { apply conj_congr_right S,
    rw [conj_comp' S _ _ (sm _), conj_comm, conj_comp' S _ _ (sm _), conj_comm],
    exact h },
  { simp only [← category.assoc],
    apply conj_congr_left S,
    rw [conj_comp S _ _ (sm _), conj_comm, conj_comp S _ _ (sm _), conj_comm],
    exact h },
end



end quotient

end groupoid

end category_theory
