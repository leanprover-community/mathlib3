import category_theory.filtered
import topology.category.Top.limits
import data.finset.basic
import category_theory.category.basic
import category_theory.full_subcategory
import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import set_theory.cardinal.basic
import data.fintype.basic
import data.opposite

import .mathlib

universes u v w

open classical
open category_theory

-- fis = fintype_inverse_system
noncomputable theory
local attribute [instance] prop_decidable


-- necessary lemma
lemma bInter_of_directed_nonempty {α : Type*} [fintype α] [nonempty α] (S : set (set α))
  (allsnempty : ∀ s ∈ S, set.nonempty s) (dir : directed_on (⊇) S) : set.nonempty (S.sInter) :=
begin

  let mcard : set α → ℕ := λs,  fintype.card s,

  by_cases Snempty : S.nonempty,
  { let s₀ := function.argmin_on (mcard) (nat.lt_wf) S Snempty,
    let hs₀ := function.argmin_on_mem (mcard) (nat.lt_wf) S Snempty,
    suffices : s₀ = S.sInter, {
      rw ←this,
      exact allsnempty s₀ hs₀,
    },
    apply set.ext,
    rintro x,
    split,
    { rintro xs₀,
      --rw set.mem_sInter,
      rintro s hs,
      rcases dir s₀ hs₀ s hs with ⟨t,ht,ts₀,ts⟩,
      suffices : t = s₀,{
        rw this at ts,
        exact ts xs₀,},
      have : mcard s₀ ≤ mcard t, from function.argmin_on_le (mcard) (nat.lt_wf) S ht,
      exact set.eq_of_subset_of_card_le ts₀ this,
    },
    { rintro xI, exact set.mem_sInter.mp xI s₀ hs₀, },
  },
  { rw set.not_nonempty_iff_eq_empty at Snempty,
    simp only [Snempty, set.sInter_empty, set.univ_nonempty],},
end







namespace inverse_system

variables {J : Type u} [preorder J] [Jdir : is_directed J ge] (F : J ⥤ Type v)

instance : preorder Jᵒᵖ := {
  le := λ jop jop', jop'.unop ≤ jop.unop,
  lt := λ jop jop', jop'.unop < jop.unop,
  le_refl := λ jop, preorder.le_refl jop.unop,
  le_trans := λ j₁ j₂ j₃, λ h₁₂ h₂₃, preorder.le_trans _ _ _ h₂₃ h₁₂,
  lt_iff_le_not_le := λ j₁ j₂, preorder.lt_iff_le_not_le j₂.unop j₁.unop
  }

instance Jopdir  : is_directed Jᵒᵖ has_le.le :=
  {directed := λ jop jop',
    let ⟨c, hj, hj'⟩ := @is_directed.directed _ _ Jdir jop.unop jop'.unop in
      ⟨opposite.op c, hj, hj'⟩}

#check inverse_system.Jopdir

theorem nonempty_sections_of_fintype_inverse_system'
(F : J ⥤ Type v) [Π (j : J), fintype (F.obj j)] [∀ (j : J), nonempty (F.obj j)] : F.sections.nonempty :=
begin
  let F' : (Jᵒᵖ)ᵒᵖ ⥤ Type v := (category_theory.op_op J).comp F,
  haveI : Π j : Jᵒᵖᵒᵖ, fintype (F'.obj j) := λ jopop, sorry,
  haveI : ∀ j : Jᵒᵖᵒᵖ, nonempty (F'.obj j) := by {
    intro jopop,
    dsimp [F'],
    sorry,
  },
  -- have F'sections_nempty := @nonempty_sections_of_fintype_inverse_system Jᵒᵖ _ _ F' _ _,
  admit,
end




def is_surjective : Prop := ∀ (i j : J) (h : i ≤ j) (x : F.obj j), x ∈ set.range (F.map (hom_of_le h))

def is_surjective_on (j : J) : Prop :=
  ∀ (i : J) (h : i ≤ j), function.surjective (F.map (hom_of_le h))

lemma is_surjective_iff :
  (is_surjective F) ↔ ∀ (i j : J) (h : i ≤ j), function.surjective (F.map (hom_of_le h)) := by refl

-- why do I need to make it an explicit argument
def to_surjective (F : J ⥤ Type v) : J ⥤ Type v :=
begin
  let Fsur_obj : Π (j : J), set (F.obj j) := λ j, ⋂ (i : {i | i ≤ j}), set.range (F.map  (hom_of_le i.prop)),
  have subfunctor : Π (i j : J) (hij : i ⟶ j), set.maps_to (F.map hij) (Fsur_obj i) (Fsur_obj j), by
  -- Thanks Andrew Yang
  { rintro i j hij,
    rintro x h s ⟨⟨k, _⟩, rfl⟩,
    obtain ⟨l,lk,li⟩ := directed_of ge k i,
    rw set.mem_Inter at h,
    obtain ⟨y,rfl⟩ := h ⟨l, li⟩,
    use F.map (hom_of_le lk) y,
    rw [← functor_to_types.map_comp_apply, ← functor_to_types.map_comp_apply],
    refl },

  refine_struct ⟨(λ j, subtype (Fsur_obj j)),_,_,_⟩,
  { rintro j' j m, exact set.maps_to.restrict _ _ _ (subfunctor j' j m)},
  { rintro j,
    apply funext,
    rintro ⟨x,xh⟩,
    rw ←subtype.coe_inj,
    simp only [category_theory.functor.map_id, set.maps_to.coe_restrict_apply, category_theory.types_id_apply],},
  { rintro j j' j'' m m',
    apply funext,
    rintro ⟨x,xh⟩,
    rw ←subtype.coe_inj,
    simp only [category_theory.functor.map_comp, set.maps_to.coe_restrict_apply, category_theory.types_comp_apply],},
end

lemma to_surjective.subfunctor :
  ∀ (i j : J) (ij : i ⟶ j), subtype.simps.coe ∘ (to_surjective F).map ij = (F.map ij) ∘ subtype.simps.coe :=
begin
  rintros, ext, refl,
end

lemma to_surjective.subfunctor_apply :
  ∀ (i j : J) (ij : i ⟶ j) (x : (to_surjective F).obj i), subtype.simps.coe ((to_surjective F).map ij x) = F.map ij (subtype.simps.coe x) :=
begin
  rintros, refl
end

instance to_surjective.fintype [Π (j : J), fintype (F.obj j)] :
  Π (j : J), fintype  ((to_surjective F).obj j) :=
begin
  rintro j,
  unfold to_surjective,
  simp only [set.mem_set_of_eq, set.Inter_coe_set],
  apply subtype.fintype,
end


instance to_surjective.nonempty [Π (j : J), fintype (F.obj j)] [nempties : Π (j : J), nonempty (F.obj j)] :
  Π (j : J), nonempty  ((to_surjective F).obj j) :=
begin
  rintro j,
  unfold to_surjective,
  simp only [nonempty_subtype],
  refine bInter_of_directed_nonempty _ _ _,
  { rintro s ⟨⟨i,ij⟩,rfl⟩,
    simp only [set.mem_set_of_eq] at ij,
    exact set.range_nonempty _,},
  { -- Probably heavily golfable
    rintro X ⟨⟨i,ij⟩,rfl⟩ Y ⟨⟨k,kj⟩,rfl⟩,
    rw set.mem_set_of_eq at ij kj,
    obtain ⟨l,lk,li⟩ := directed_of (≥) k i,
    have : hom_of_le lk ≫ hom_of_le kj = hom_of_le li ≫ hom_of_le ij, by reflexivity,
    use [set.range (F.map $ hom_of_le lk ≫ hom_of_le kj),l,lk.le.trans kj],
    { simp only, refl, },
    { simp only,
      split,
      { rw [this,functor.map_comp /-F hli hij-/,types_comp],
        apply set.range_comp_subset_range,},
      {
        rw [functor.map_comp /-F hlk hkj-/,types_comp],
        apply set.range_comp_subset_range,},},
  },
end

/-
This subfunctor is NOT surjective in general (i.e. if we drop the fintype assumption).
Here is an example when it isn't:
The preordered is ℕ, with F 0 = {0,1}, and F (succ n) = ℕ.
The map from F 1 to F 0 sends everything to 1.
The map from F 2 to F 1 is the identity
The map from F 3 to F 2 sends 0 and 1 to 0, and is the identity elsewhere
The map from F 4 to F 3 sends 0,1,2 to 0; and is the identity elsewhere
…
Then 1 ∈ F 0 is in all the ranges, but any preimage of 1 has no preimage "sufficiently high".

Btw, this is also a contrived example of a system with no section.
-/
lemma to_surjective.is_surjective
  [Π (j : J), fintype (F.obj j)] [nempties : Π (j : J), nonempty (F.obj j)] :
  is_surjective (to_surjective F) :=
begin
  unfold is_surjective,
  rintros i j ij ⟨x,xh⟩,


  let S := set.range
    (λ k : {k : J | k ≤ i},
      (set.range (F.map (hom_of_le k.prop))) ∩ set.preimage (F.map  $ hom_of_le ij) {x}),

  have Ssnempty : ∀ s ∈ S, set.nonempty s, by
  { rintro s hs,
    obtain ⟨⟨k,ki⟩,rfl⟩ := hs,
    simp only [set.mem_set_of_eq] at ki,
    have xh : x ∈ ⋂ (l : {l | l ≤ j}), set.range (F.map (hom_of_le l.prop)) := xh,
    rw set.mem_Inter at xh,
    obtain ⟨z,rfl⟩ := xh ⟨k,ki.trans ij⟩,
    --let y := F.map (hom_of_le ki) z,
    use F.map (hom_of_le ki) z,
    use ⟨z,rfl⟩,
    simp only [set.mem_preimage, set.mem_singleton_iff],
    rw ←functor_to_types.map_comp_apply,
    reflexivity,},

  have : (⋂₀ S).nonempty, by {
    refine bInter_of_directed_nonempty S Ssnempty _,
    unfold directed_on,
    -- only needs to show that S is directed
    rintros X ⟨⟨l,li⟩,rfl⟩ Y ⟨⟨k,ki⟩,rfl⟩,
    rw set.mem_set_of_eq at li ki,
    obtain ⟨m,mk,ml⟩ := directed_of (≥) k l,
    use set.range (F.map $ hom_of_le $ mk.le.trans ki) ∩ set.preimage (F.map  $ hom_of_le ij) {x},
    use [m,mk.le.trans ki,rfl],
    { simp only,
      split,
      { apply set.inter_subset_inter_left,
        have : hom_of_le (ml.le.trans li) = (hom_of_le ml.le) ≫ (hom_of_le li), by reflexivity,
        rw [this, functor.map_comp, types_comp],
        apply set.range_comp_subset_range,},
      {apply set.inter_subset_inter_left,
        have : hom_of_le (mk.le.trans ki) = (hom_of_le mk.le) ≫ (hom_of_le ki), by reflexivity,
        rw [this, functor.map_comp ,types_comp],
        apply set.range_comp_subset_range,},},},

  obtain ⟨y,y_mem⟩ := this,
  dsimp at y_mem,
  simp only [set.mem_Inter, set.mem_inter_eq, set.mem_range, set.mem_preimage, set.mem_singleton_iff, subtype.forall] at y_mem,
  use y,
  { rintro s ⟨⟨m,mi⟩,rfl⟩,
    obtain ⟨⟨z,ztoy⟩,ytox⟩ := y_mem m mi,
    use [z,ztoy],},
  { obtain ⟨⟨z,ztoy⟩,ytox⟩ := y_mem i (le_refl i),
    apply subtype.mk_eq_mk.mpr ytox,},
end

lemma sections_in_to_surjective (s : F.sections) (j : J) :
  (s.val j) ∈ set.range (subtype.simps.coe : ((to_surjective F).obj j) → F.obj j) :=
begin
  have : ∀ i : {i | i ≤ j}, s.val j ∈ set.range (F.map $ hom_of_le i.prop) :=
    λ ⟨i,ij⟩, ⟨s.val i, s.prop (hom_of_le ij)⟩,

  rw set.mem_range,
  simp only [set.mem_set_of_eq, set.Inter_coe_set, subtype.val_eq_coe, subtype.exists],
  use s.val j,
  split,
  { refl, },
  { rintro s ⟨i,rfl⟩, simp only [set.mem_Inter], intro ij, exact this ⟨i,ij⟩, },
end

lemma sections_in_surjective' (s : F.sections) (j : J) :
  (s.val j) ∈ ⋂ (i : { i | i ≤ j}), set.range (F.map  (hom_of_le i.prop)) :=
begin
  rw set.mem_Inter,
  rintro ⟨i,ij⟩,
  use s.val i,
  exact s.prop (hom_of_le ij),
end

def to_surjective.sections_equiv : F.sections ≃ (to_surjective F).sections :=
begin
  split, rotate 2,
  { rintro s,
    split, rotate,
    { exact λ j, ⟨s.val j, sections_in_surjective' F s j⟩,},
    { exact  λ i j ij, subtype.mk_eq_mk.mpr (s.prop ij),}
  },
  { rintro ⟨s,sec⟩,
    split, rotate,
    { exact λ j, (s j).val,},
    { rintro i j ij, -- not very pretty…
      have : ((s i).val : F.obj i) = subtype.simps.coe (s i), by reflexivity,
      rw [this,←to_surjective.subfunctor_apply],
      simp only [subtype.simps.coe, subtype.val_eq_coe],
      rw subtype.coe_inj,
      exact sec ij,},},
  { simp only [function.left_inverse, eq_self_iff_true, set_coe.forall, implies_true_iff], },
  { simp only [function.right_inverse, function.left_inverse, subtype.val_eq_coe, set_coe.forall, subtype.coe_mk, subtype.coe_eta,
  eq_self_iff_true, implies_true_iff],  },
end

def decomposition (j : J) :
  F.sections ≃ Σ (x : F.obj j), {s : F.sections | s.val j = x} :=
begin
  split, rotate 2,
  { intro s, use s.val j, use s, simp, },
  { rintro ⟨_, s, _⟩, use s,},
  { simp [function.left_inverse], },
  { simp [function.right_inverse, function.left_inverse], tidy, }
end


def sections_injective (j : J)
  (inj : ∀ i : {i | i ≤ j}, function.injective $ F.map (hom_of_le i.prop)) :
  function.injective (λ (s :F.sections), s.val j) :=
begin
  dsimp [function.injective],
  rintros ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ hyp,
  dsimp [functor.sections] at *,
  rw subtype.mk_eq_mk,
  suffices : ∀ i : {i | i ≤ j}, e₁ i.val = e₂ i.val,
  { apply funext,
    rintro k,
    obtain ⟨m,mk,mj⟩ := directed_of (≥) k j,
    rw  [←h₁ (hom_of_le mk), ←h₂ (hom_of_le mk), this ⟨m,mj⟩],},

    rintro ⟨i,ij⟩,
    apply inj ⟨i,ij⟩,
    dsimp,
    rw [h₁,h₂],
    exact hyp,
end

def sections_bijective (j : J)
  (bij : ∀ i : {i | i ≤ j}, function.bijective $ F.map (hom_of_le i.prop)) :
  function.bijective (λ (s :F.sections), s.val j) :=
begin
  let inj  := λ ii : {i | i ≤ j}, (bij ii).1,
  let surj := λ ii : {i | i ≤ j}, (bij ii).2,
  let eqv  := λ ii : {i | i ≤ j}, equiv.of_bijective (F.map (hom_of_le ii.prop)) (bij ii),
  split,
  exact sections_injective F j inj,

  rintro x,

  let s :  Π (i : J), {y : F.obj i | ∃ (k : J) (ik : k ≤ i) (jk : k ≤ j), F.map (hom_of_le ik) ((eqv ⟨k,jk⟩).inv_fun x) = y}, by {
    rintro i,
    let m := (directed_of (≥) i j).some,
    obtain ⟨mi,mj⟩ := (directed_of (≥) i j).some_spec,
    use F.map (hom_of_le mi) ((eqv ⟨m,mj⟩).inv_fun x),
    exact ⟨m,mi,mj,rfl⟩,
  },
  use (λ i, (s i).val),
  {
    rintro i k ik',
    let ik := le_of_hom ik',
    obtain ⟨m,mi,mj,meq⟩ := (s i).prop,
    obtain ⟨n,nk,nj,neq⟩ := (s k).prop,
    let l := (directed_of (≥) m n).some,
    obtain ⟨lm,ln⟩ := (directed_of (≥) m n).some_spec,

    have lmbij : function.bijective (F.map $ hom_of_le lm), by
    { refine (function.bijective.of_comp_iff' (bij ⟨m,mj⟩) (F.map $ hom_of_le lm)).mp _,
      rw [←category_theory.types_comp,←category_theory.functor.map_comp],
      exact bij ⟨l,lm.le.trans mj⟩, },
    have lnbij : function.bijective (F.map $ hom_of_le ln), by
    { refine (function.bijective.of_comp_iff' (bij ⟨n,nj⟩) (F.map $ hom_of_le ln)).mp _,
      rw [←category_theory.types_comp,←category_theory.functor.map_comp],
      exact bij ⟨l,ln.le.trans nj⟩, },

    simp only [subtype.val_eq_coe],
    rw [←meq,←neq],

    rw ←functor_to_types.map_comp_apply,
    --have : ∀ y, y = (F.map $ hom_of_le lm) ((equiv.of_bijective _ lmbij).inv_fun y),
    --{ rintro y, exact ((equiv.of_bijective _ lmbij).right_inv y).symm, },
    --rw this ((eqv ⟨m,mj⟩).inv_fun x),
    rw ←(equiv.right_inv (equiv.of_bijective _ lmbij) ((eqv ⟨m,mj⟩).inv_fun x)),
    --have : ∀ y, y = (F.map $ hom_of_le ln) ((equiv.of_bijective _ lnbij).inv_fun y), by
    --{ rintro y, exact ((equiv.of_bijective _ lnbij).right_inv y).symm,},
    --rw this ((eqv ⟨n,nj⟩).inv_fun x),
    rw ←(equiv.right_inv (equiv.of_bijective _ lnbij) ((eqv ⟨n,nj⟩).inv_fun x)),
    simp only [equiv.inv_fun_as_coe, equiv.to_fun_as_coe, equiv.of_bijective_apply, functor_to_types.map_comp_apply],
    rw ←functor_to_types.map_comp_apply,
    rw ←functor_to_types.map_comp_apply,
    rw ←functor_to_types.map_comp_apply,

    simp only [eqv],
    --simp only [equiv.inv_fun_as_coe],
    rw [←equiv.symm_trans_apply,←equiv.symm_trans_apply],
    rw [equiv.of_bijective_trans,equiv.of_bijective_trans],
    rw [←equiv.inv_fun_as_coe,←equiv.inv_fun_as_coe],
    simp_rw ←types_comp,
    simp_rw ←functor.map_comp',
    reflexivity, },
  { obtain ⟨m,mj,mj',meq⟩ := (s j).prop,
    simp only [subtype.val_eq_coe],
    simp only [equiv.inv_fun_as_coe] at meq,
    rw ←meq,
    dsimp [eqv],
    apply equiv.of_bijective_apply_symm_apply,},
end


-- Shitty terminology, but anyway
lemma directed_of_coinitial
  (I : set J) (Icof : ∀ j : J, ∃ i ∈ I, i ≤ j) : is_directed I ge :=
begin
  apply is_directed.mk,
  rintros ⟨i,iI⟩ ⟨k,kI⟩,
  obtain ⟨j,ij,kj⟩ := directed_of (ge) i k,
  obtain ⟨m,mI,jm⟩ := Icof j,
  use ⟨m,mI⟩,
  simp only [ge_iff_le, subtype.mk_le_mk],
  exact ⟨jm.trans ij.le, jm.trans kj.le⟩,
end

instance lower_directed
  (j : J) : is_directed {i : J | i ≤ j} ge :=
begin
  apply directed_of_coinitial,
  rintros i,
  obtain ⟨k,ik,jk⟩ := directed_of (ge) i j,
  exact ⟨k,jk,ik⟩,
end


def above_point
 (j : J) (x : F.obj j) : {i : J | i ≤ j} ⥤ Type v :=
begin
  let Fobj : Π (ii : {i : J | i ≤ j}), set (F.obj $  (ii).val) :=
    λ ii, set.preimage (F.map $ hom_of_le ii.prop) {x},

  have subfunctor : Π (ii kk : {i : J | i ≤ j}) (ik : ii ≤ kk),
    set.maps_to (F.map $ hom_of_le ik) (Fobj ii) (Fobj kk), by {
    rintro ii kk ik,
    dsimp only [Fobj],
    unfold set.maps_to,
    unfold set.preimage,
    rintro y hy,
    simp only [set.mem_singleton_iff] at hy,
    dsimp at hy,
    rcases hy with rfl,
    simp only [set.mem_singleton_iff, set.mem_set_of_eq],
    dsimp,
    rw ←functor_to_types.map_comp_apply,
    reflexivity,},

  refine ⟨λ ii, subtype (Fobj ii),_,_,_⟩,
  { rintros ii kk ik,
    exact set.maps_to.restrict _ _ _ (subfunctor ii kk $ le_of_hom ik),},
  { simp only [auto_param_eq],
    rintro ii,
    apply funext,
    rintro ⟨x,xh⟩,
    simp only [types_id_apply, set.maps_to.restrict, subtype.map, subtype.coe_mk, subtype.mk_eq_mk],
    nth_rewrite_rhs 0 ←functor_to_types.map_id_apply F x,
    reflexivity, },
  { simp only [auto_param_eq], rintro ii kk ll ik kl, apply funext, rintro ⟨x,xh⟩,
    simp only [types_comp_apply, set.maps_to.restrict, subtype.map, subtype.coe_mk, subtype.mk_eq_mk],
    rw ←functor_to_types.map_comp_apply,
    reflexivity, },
end


instance above_point.nonempty [Π (j : J), fintype (F.obj j)] [∀ (j : J), nonempty (F.obj j)]
  (j : J)
  (Fsurj : is_surjective_on F j)
  (x : F.obj j) :
  Π (i : {i : J | i ≤ j}), nonempty ((above_point F j x).obj i)  :=
begin
  rintro ii,
  dsimp [above_point],
  unfold is_surjective_on at Fsurj,
  specialize Fsurj ( (ii.val)) ii.prop x,
  unfold set.preimage,
  simp,
  obtain ⟨y,rfl⟩ := Fsurj,
  apply Exists.intro,
  rotate,
  { rw ←subtype.val_eq_coe, use y, },
  { dsimp only [subtype.val_eq_coe] at *, fsplit,  /-thanks tidy I don't know what I'm doing here-/},
end

instance above_point.fintype

  [Π (j : J), fintype (F.obj j)] [∀ (j : J), nonempty (F.obj j)]
  (j : J)
  (x : F.obj j) :
  Π (i : {i : J | i ≤ j}), fintype ((above_point F j x).obj i)  :=
begin
  rintros ii,
  obtain ⟨i,ij⟩ := ii,
  unfold above_point,
  simp,
  apply subtype.fintype,
end

lemma above_point.sections_nonempty (j : J) (Fsurj : is_surjective_on F j)
  [Π (j : J), fintype (F.obj j)] [∀ (j : J), nonempty (F.obj j)]
  (x : F.obj j) : nonempty (above_point F j x).sections :=
begin
  apply set.nonempty_coe_sort.mpr,
  exact @nonempty_sections_of_fintype_inverse_system' _ _ _ (above_point F j x) (above_point.fintype F j x)  (above_point.nonempty F j Fsurj x),
end

-- This should maybe be split into more basic components…
def sections_at_point (j : J) (x : F.obj j) :
  {s : F.sections | s.val j = x} ≃ (above_point F j x).sections :=
begin

  let fwd : {s : F.sections | s.val j = x} → (above_point F j x).sections, by
  { rintro ⟨⟨s,sec⟩,sjx⟩,
    simp only [set.mem_set_of_eq] at sjx,
    rcases sjx with rfl,
    split, rotate,
    { rintro ⟨i,ij⟩,
      exact ⟨s i,sec $ hom_of_le ij⟩, },
    { rintro ⟨i,ij⟩ ⟨k,kj⟩ ik,
      simp only [←subtype.coe_inj],
      simp only [set.maps_to.coe_restrict_apply, subtype.coe_mk],
      apply sec, },},


  let bwd_aux :  Π (s : (above_point F j x).sections) (i : J),
                 {y : F.obj i | ∃ (k : J) (ik : k ≤ i) (jk : k ≤ j),
                                y =  F.map (hom_of_le ik) (s.val $  ⟨k,jk⟩).val}, by
  { rintro ⟨s,sec⟩ i,
    let m := (directed_of (≥) i j).some,
    obtain ⟨mi,mj⟩ := (directed_of (≥) i j).some_spec,
    use F.map (hom_of_le mi) (s ⟨m,mj⟩).val,
    exact ⟨m,mi,mj,rfl⟩, },

  let bwd : (above_point F j x).sections → {s : F.sections | s.val j = x}, by
  { rintro ss,
    dsimp only [functor.sections],
    split, rotate,
    { split, rotate,
      { exact (λ i, (bwd_aux ss i).val) },
      { rintro i k ik',
        obtain ⟨m,mi,mj,meq⟩ := (bwd_aux ss i).prop,
        obtain ⟨n,nk,nj,neq⟩ := (bwd_aux ss k).prop,
        let l := (directed_of (≥) m n).some,
        obtain ⟨lm,ln⟩ := (directed_of (≥) m n).some_spec,
        obtain ⟨s,sec⟩ := ss,
        simp only [subtype.val_eq_coe,meq,neq],
        rw ←(@sec  ⟨l, lm.le.trans mj⟩ ⟨m, mj⟩ (hom_of_le $ lm)),
        rw ←(@sec  ⟨l, ln.le.trans nj⟩ ⟨n, nj⟩ (hom_of_le $ ln)),
        dsimp [above_point],
        simp only [←functor_to_types.map_comp_apply],
        reflexivity, },},
    { simp only [subtype.val_eq_coe, set.mem_set_of_eq, subtype.coe_mk],
      obtain ⟨y,k,jk,jk',rfl⟩ := bwd_aux ss j,
      simp only [subtype.val_eq_coe, subtype.coe_mk],
      dsimp [above_point,functor.sections] at ss,
      obtain ⟨s,sec⟩ := ss,
      simp only [subtype.coe_mk],
      obtain ⟨y,yh⟩ := s ⟨k,jk⟩,
      exact yh,}
  },

  split, rotate 2,
  exact fwd,
  exact bwd,
  { dsimp only [function.left_inverse],
    dsimp only [fwd,bwd],
    rintro ⟨⟨s,sec⟩,sjx⟩,
    simp only [set.mem_set_of_eq] at sjx,
    rcases sjx with rfl,
    dsimp only [id],
    apply subtype.mk_eq_mk.mpr,
    apply subtype.mk_eq_mk.mpr,
    apply funext,
    rintro i,
    obtain ⟨a,k,ki,kj,e⟩ := bwd_aux (fwd ⟨⟨s, λ _ _, sec⟩,rfl⟩) i,
    simp only,
    rw e,
    dsimp only [fwd],
    rw ←sec (hom_of_le ki),
   },
  { dsimp only [function.right_inverse,function.left_inverse],
    rintro ss,
    dsimp only [fwd,bwd],
    rcases ss with ⟨s,sec⟩,
    apply subtype.coe_eq_of_eq_mk,
    apply funext,
    rintro ⟨i,ij⟩,
    obtain ⟨a,k,ki,kj,e⟩ := bwd_aux (⟨s, λ _ _, sec⟩ : (above_point F j x).sections) i,
    rcases e with rfl,
    dsimp only [id],
    dsimp only [bwd_aux],
    sorry,
     },
end


lemma decomposition' [Π (j : J), fintype (F.obj j)] [∀ (j : J), nonempty (F.obj j)] (j : J) :
  F.sections ≃ Σ (x : F.obj j), (above_point F j x).sections :=
begin
  apply equiv.trans,
  rotate 2,
  {exact Σ (x : F.obj j), {s : F.sections | s.val j = x},},
  {exact decomposition F j,},
  {apply equiv.sigma_congr_right, exact sections_at_point F j,},
end


lemma sections_surjective [Π (j : J), fintype (F.obj j)]
  (j : J) (Fsurj : is_surjective_on F j) :
  function.surjective (λ (s : F.sections), s.val j) :=
begin
    rintro x,
    haveI : Π (j : J), nonempty (F.obj j), by
    { rintro i,
      let l := (directed_of (≥) i j).some,
      obtain ⟨li,lj⟩ := (directed_of (≥) i j).some_spec,
      obtain ⟨y,rfl⟩ :=  Fsurj l lj x,
      use F.map (hom_of_le li) y,},

    obtain ⟨s_above⟩ := above_point.sections_nonempty F j Fsurj x,
    obtain ⟨s,sgood⟩ := (sections_at_point F j x).inv_fun s_above,
    exact ⟨s,sgood⟩,
end

end inverse_system
