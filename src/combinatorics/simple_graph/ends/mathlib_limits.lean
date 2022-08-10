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

import .mathlib

universes u v w

open classical
open category_theory

-- fis = fintype_inverse_system
noncomputable theory
local attribute [instance] prop_decidable

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



def fis.is_surjective  {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) /- [Π (j : Jᵒᵖ), fintype (F.obj j)] [∀ (j : Jᵒᵖ), nonempty (F.obj j)] -/ : Prop :=
∀ (i j : Jᵒᵖ) (h : j.unop ≤ i.unop) (x : F.obj j), x ∈ set.range (F.map (op_hom_of_le h))

def fis.is_surjective_onto  {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) (j : Jᵒᵖ) : Prop :=
∀ (i : Jᵒᵖ) (h : j.unop ≤ i.unop), function.surjective (F.map (op_hom_of_le h))


def fis.is_surjective_iff  {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) /- [Π (j : Jᵒᵖ), fintype (F.obj j)] [∀ (j : Jᵒᵖ), nonempty (F.obj j)] -/ :
  (fis.is_surjective F) ↔ ∀ (i j : Jᵒᵖ) (h : j.unop ≤ i.unop), function.surjective (F.map (op_hom_of_le h)) := sorry


def bigger  {J : Type u} [preorder J] : Π (j : Jᵒᵖ), set Jᵒᵖ := λ j, {i : Jᵒᵖ | j.unop ≤ i.unop}

/-
I CAN'T prove that this subfunctor is surjective in general.
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
def fis.to_surjective  {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) /- [Π (j : Jᵒᵖ), fintype (F.obj j)] [∀ (j : Jᵒᵖ), nonempty (F.obj j)] -/ : Jᵒᵖ ⥤ Type v :=
begin
  let Fsur_obj : Π (j : Jᵒᵖ), set (F.obj j) := λ j, ⋂ (i : bigger j), set.range (F.map  (op_hom_of_le i.prop)),

  have subfunctor : Π (i j : Jᵒᵖ) (hij : i ⟶ j), set.maps_to (F.map hij) (Fsur_obj i) (Fsur_obj j), by
  -- Thanks Andrew Yang
  { rintro i j hij,
    rintro x h s ⟨⟨k, _⟩, rfl⟩,
    obtain ⟨l,lk,li⟩ := directed_of (≤) k.unop i.unop,
    rw set.mem_Inter at h,
    obtain ⟨y,rfl⟩ := h ⟨opposite.op l, li⟩,
    use F.map (hom_of_le lk).op y,
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

lemma fis.to_surjective.subfunctor {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) :
  ∀ (i j : Jᵒᵖ) (ij : i ⟶ j), subtype.simps.coe ∘ (fis.to_surjective F).map ij = (F.map ij) ∘ subtype.simps.coe :=
begin
  rintros i j ij,
  apply funext,
  rintros x,
  --simp [set.maps_to.coe_restrict_apply], -- Why don't we need this?
  refl,
end

lemma fis.to_surjective.subfunctor_apply {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) :
  ∀ (i j : Jᵒᵖ) (ij : i ⟶ j) (x : (fis.to_surjective F).obj i), subtype.simps.coe ((fis.to_surjective F).map ij x) = F.map ij (subtype.simps.coe x) :=
begin
  rintros i j ij,
  rintros x,
  --simp [set.maps_to.coe_restrict_apply], -- Why don't we need this?
  refl,
end



instance fis.to_surjective.fintype  {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) [Π (j : Jᵒᵖ), fintype (F.obj j)] :
  Π (j : Jᵒᵖ), fintype  ((fis.to_surjective F).obj j) :=
begin
  rintro j,
  unfold fis.to_surjective,
  simp,
  apply subtype.fintype,
end

instance fis.to_surjective.nonempty  {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) [Π (j : Jᵒᵖ), fintype (F.obj j)] [nempties : Π (j : Jᵒᵖ), nonempty (F.obj j)] :
  Π (j : Jᵒᵖ), nonempty  ((fis.to_surjective F).obj j) :=
begin
  rintro j,
  unfold fis.to_surjective,
  simp only [nonempty_subtype],
  refine bInter_of_directed_nonempty _ _ _,
  { rintro s ⟨⟨i,ij⟩,rfl⟩,
    unfold bigger at ij,
    simp only [set.mem_set_of_eq] at ij,
    exact set.range_nonempty _,},
  { -- Probably heavily golfable
    rintro X ⟨⟨i,ij⟩,rfl⟩ Y ⟨⟨k,kj⟩,rfl⟩,
    unfold bigger at ij, rw set.mem_set_of_eq at ij,
    unfold bigger at kj, rw set.mem_set_of_eq at kj,
    obtain ⟨l',lk',li'⟩ := directed_of (≤) k.unop i.unop,
    let l := opposite.op l',
    have lk : opposite.unop k ≤ opposite.unop l, by {simp only [opposite.unop_op],exact lk'},
    have li : opposite.unop i ≤ opposite.unop l, by {simp only [opposite.unop_op],exact li'},
    let hlk := op_hom_of_le lk,
    let hli := op_hom_of_le li,
    let hkj := op_hom_of_le kj,
    let hij := op_hom_of_le ij,
    let hkj := op_hom_of_le kj,
    have : hlk ≫ hkj = hli ≫ hij, by reflexivity,
    use set.range (F.map $ hlk ≫ hkj),
    use l,
    use kj.trans lk,
    { simp only, refl, },
    { --have : op_hom_of_le ij = hlk ≫ hkj, by {sorry},
      simp only,
      split,
      { rw [‹hlk ≫ hkj = hli ≫ hij›,functor.map_comp /-F hli hij-/,types_comp],
        apply set.range_comp_subset_range,},
      {
        rw [functor.map_comp /-F hlk hkj-/,types_comp],
        apply set.range_comp_subset_range,},
    },
  },
end


lemma fis.to_surjective.is_surjective {J : Type u} [preorder J]  [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) [Π (j : Jᵒᵖ), fintype (F.obj j)] [nempties : Π (j : Jᵒᵖ), nonempty (F.obj j)] : fis.is_surjective (fis.to_surjective F) :=
begin
  unfold fis.is_surjective,
  rintros i j ij ⟨x,xh⟩,


  let S := set.range (λ k : bigger i, (set.range (F.map (op_hom_of_le k.prop))) ∩ set.preimage (F.map  $op_hom_of_le ij) {x}),
  have Ssnempty : ∀ s ∈ S, set.nonempty s, by
  { rintro s hs,
    have : ∃ k : bigger i, (set.range (F.map (op_hom_of_le k.prop))) ∩ set.preimage (F.map  $op_hom_of_le ij) {x} = s, by
    { rw set.mem_range at hs, exact hs }, -- should be hs
    obtain ⟨⟨k,ki⟩,rfl⟩ := this,
    have ki : i.unop ≤ k.unop, from ki,
    have xh' : x ∈ ⋂ (l : (bigger j)), set.range (F.map (op_hom_of_le l.prop)) := xh,
    rw set.mem_Inter at xh',
    obtain ⟨z,rfl⟩ := xh' ⟨k,ij.trans ki⟩,
    let y := F.map (op_hom_of_le ki) z,
    use y,
    use ⟨z,rfl⟩,
    have : F.map (op_hom_of_le ij) y = F.map (op_hom_of_le (ij.trans ki)) z, by
    { have : F.map (op_hom_of_le ij) (F.map (op_hom_of_le ki) z) = F.map (op_hom_of_le (ij.trans ki)) z, by {
      rw ←functor_to_types.map_comp_apply,
      reflexivity,},
      exact this,},
    exact this,},

  have : (⋂₀ S).nonempty, by {
    refine bInter_of_directed_nonempty S Ssnempty _,
    unfold directed_on,
    -- only needs to show that S is directed
    rintros X ⟨⟨l,li⟩,rfl⟩ Y ⟨⟨k,ki⟩,rfl⟩,
    unfold bigger at li, rw set.mem_set_of_eq at li,
    unfold bigger at ki, rw set.mem_set_of_eq at ki,
    obtain ⟨m',mk',ml'⟩ := directed_of (≤) k.unop l.unop,
    let m := opposite.op m',
    have mk : opposite.unop k ≤ opposite.unop m, by {simp only [opposite.unop_op],exact mk'},
    have ml : opposite.unop l ≤ opposite.unop m, by {simp only [opposite.unop_op],exact ml'},
    use set.range (F.map $ op_hom_of_le $ ki.trans mk) ∩ set.preimage (F.map  $ op_hom_of_le ij) {x},
    use m,
    use ki.trans mk,
    { simp only, refl, },
    {
      simp only,
      split,
      { apply set.inter_subset_inter_left,
        have : op_hom_of_le (li.trans ml) = (op_hom_of_le ml) ≫ (op_hom_of_le li), by reflexivity,
        rw [this,functor.map_comp /-F hli hij-/,types_comp],
        apply set.range_comp_subset_range,},
      {apply set.inter_subset_inter_left,
        have : op_hom_of_le (ki.trans mk) = (op_hom_of_le mk) ≫ (op_hom_of_le ki), by reflexivity,
        rw [this,functor.map_comp /-F hli hij-/,types_comp],
        apply set.range_comp_subset_range,},
    },

  },

  obtain ⟨y,y_mem⟩ := this,
  dsimp at y_mem,simp at y_mem,
  use y,
  { rintro s ⟨⟨m,mi⟩,rfl⟩,
    simp only [set.mem_range],
    specialize y_mem m mi,
    obtain ⟨⟨z,ztoy⟩,ytox⟩ := y_mem,
    use [z,ztoy],},
  { specialize y_mem i (le_refl i.unop),
    obtain ⟨⟨z,ztoy⟩,ytox⟩ := y_mem,
    dsimp only [set.mem_range],
    apply subtype.mk_eq_mk.mpr,
    simp only [subtype.coe_mk],
    exact ytox,},
end



lemma fis.sections_in_surjective {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) (s : F.sections) (j : Jᵒᵖ) :
  (s.val j) ∈ set.range (subtype.simps.coe : ((fis.to_surjective F).obj j) → F.obj j) :=
begin
  let y := s.val j,
  have : ∀ (i : bigger j), y ∈ set.range (F.map $ op_hom_of_le i.prop), by {
    rintro ⟨i,ij⟩,
    use s.val i,
    exact s.prop (op_hom_of_le ij),},
  rw set.mem_range, simp,
  use y,
  split,
  { refl, },
  { rintro s ⟨i,rfl⟩, simp only [set.mem_Inter], intro ij, exact this ⟨i,ij⟩, },
end

lemma fis.sections_in_surjective' {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) (s : F.sections) (j : Jᵒᵖ) :
  (s.val j) ∈ ⋂ (i : bigger j), set.range (F.map  (op_hom_of_le i.prop)) :=
begin
  rw set.mem_Inter,
  rintro ⟨i,ij⟩,
  use s.val i,
  exact s.prop (op_hom_of_le ij),
end

def fis.sections_surjective_equiv_sections  {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) /-[Π (j : Jᵒᵖ), fintype (F.obj j)] [∀ (j : Jᵒᵖ), nonempty (F.obj j)]-/  :
  F.sections ≃ (fis.to_surjective F).sections :=
begin
  split, rotate 2,
  { rintro s,
    split, rotate,
    { rintro j,
      exact ⟨s.val j, fis.sections_in_surjective' F s j⟩,},
    { unfold category_theory.functor.sections,
      rintro i j ij,
      simp,
      apply subtype.mk_eq_mk.mpr,
      exact s.prop ij,}
  },
  { rintro ⟨s,sec⟩,
    split, rotate,
    { rintro j, exact (s j).val,},
    { rintro i j ij, -- not very pretty…
      have : ((s i).val : F.obj i) = subtype.simps.coe (s i), by reflexivity,
      rw [this,←fis.to_surjective.subfunctor_apply],
      simp [subtype.simps.coe],
      rw subtype.coe_inj,
      exact sec ij,},},
  { simp [function.left_inverse], },
  { simp [function.right_inverse, function.left_inverse],  },
end

/-
def fis.cofinal_subsystem {J : Type u} [preorder J] [is_directed J has_le.le]
  (J' : set J) (J'cof : ∀ j : J, ∃ j' ∈ J', j ≤ j')
  (F : Jᵒᵖ ⥤ Type v) : F.sections ≃ ((category_theory.full_subcategory_inclusion J').comp F).sections := sorry
-/

def fis.decomposition  {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) [Π (j : Jᵒᵖ), fintype (F.obj j)] [∀ (j : Jᵒᵖ), nonempty (F.obj j)] (j : Jᵒᵖ) :
  F.sections ≃ Σ (x : F.obj j), {s : F.sections | s.val j = x} :=
begin
  split, rotate 2,
  { intro s, use s.val j, use s, simp, },
  { rintro ⟨_, s, _⟩, use s,},
  { simp [function.left_inverse], },
  { simp [function.right_inverse, function.left_inverse], tidy, }
end


def fis.injective {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) (j : Jᵒᵖ)
  (inj : ∀ i ∈ bigger j, function.injective $ F.map (op_hom_of_le H)) :
  function.injective (λ (s :F.sections), s.val j) :=
begin
  dsimp [function.injective],
  rintros ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ hyp,
  dsimp [functor.sections] at *,
  rw subtype.mk_eq_mk,
  suffices : ∀ i ∈ bigger j, e₁ i = e₂ i,
  { apply funext,
    rintro k,
    obtain ⟨m',mk',mj'⟩ := directed_of (≤) k.unop j.unop,
    let m := opposite.op m',
    have mk : opposite.unop k ≤ opposite.unop m, by {simp only [opposite.unop_op],exact mk'},
    have mj : opposite.unop j ≤ opposite.unop m, by {simp only [opposite.unop_op],exact mj'},
    rw  [←h₁ (op_hom_of_le mk), ←h₂ (op_hom_of_le mk)],
    rw this m mj, },

    rintro i ij,
    apply inj i ij,
    rw  [h₁ (op_hom_of_le ij), h₂ (op_hom_of_le ij)],
    exact hyp,
end

def fis.bijective {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) (j : Jᵒᵖ)
  (bij : ∀ i ∈ bigger j, function.bijective $ F.map (op_hom_of_le H)) :
  function.bijective (λ (s :F.sections), s.val j) :=
begin
  let inj := λ i H, (bij i H).1,
  let surj := λ i H, (bij i H).2,
  let eqv := λ i H, equiv.of_bijective _ (bij i H),
  refine ⟨fis.injective F j inj,_⟩,

  rintro x,

  let s :  Π (i : Jᵒᵖ), {y : F.obj i | ∃ (k : Jᵒᵖ) (ik : i.unop ≤ k.unop) (jk : j.unop ≤ k.unop), F.map (op_hom_of_le ik) ((eqv k jk).inv_fun x) = y}, by {
    rintro i,
    let m' := (directed_of (≤) i.unop j.unop).some,
    obtain ⟨mi',mj'⟩ := (directed_of (≤) i.unop j.unop).some_spec,
    let m := opposite.op m',
    have mi : opposite.unop i ≤ opposite.unop m, by {simp only [opposite.unop_op],exact mi'},
    have mj : opposite.unop j ≤ opposite.unop m, by {simp only [opposite.unop_op],exact mj'},
    use F.map (op_hom_of_le mi) ((eqv m mj).inv_fun x),
    exact ⟨m,mi,mj,rfl⟩,
  },
  use (λ i, (s i).val),
  {
    rintro i k ik',
    let ik := le_of_op_hom ik',
    obtain ⟨m,mi,mj,meq⟩ := (s i).prop,
    obtain ⟨n,nk,nj,neq⟩ := (s k).prop,
    let l' := (directed_of (≤) m.unop n.unop).some,
    obtain ⟨lm',ln'⟩ := (directed_of (≤) m.unop n.unop).some_spec,
    let l := opposite.op l',
    have lm : opposite.unop m ≤ opposite.unop l, by {simp only [opposite.unop_op],exact lm'},
    have ln : opposite.unop n ≤ opposite.unop l, by {simp only [opposite.unop_op],exact ln'},

    have lmbij : function.bijective (F.map $ op_hom_of_le lm), by
    { refine (function.bijective.of_comp_iff' (bij m mj) (F.map $ op_hom_of_le lm)).mp _,
      rw [←category_theory.types_comp,←category_theory.functor.map_comp],
      exact bij l (mj.trans lm), },
    have lnbij : function.bijective (F.map $ op_hom_of_le ln), by
    { refine (function.bijective.of_comp_iff' (bij n nj) (F.map $ op_hom_of_le ln)).mp _,
      rw [←category_theory.types_comp,←category_theory.functor.map_comp],
      exact bij l (nj.trans ln), },

    simp only [subtype.val_eq_coe],
    rw [←meq,←neq],

    rw ←functor_to_types.map_comp_apply,
    have : ∀ y, y = (F.map $ op_hom_of_le lm) ((equiv.of_bijective _ lmbij).inv_fun y), by
    { rintro y, exact ((equiv.of_bijective _ lmbij).right_inv y).symm, },
    rw this ((eqv m mj).inv_fun x),
    rw ←functor_to_types.map_comp_apply,
    have : ∀ y, y = (F.map $ op_hom_of_le ln) ((equiv.of_bijective _ lnbij).inv_fun y), by
    { rintro y, exact ((equiv.of_bijective _ lnbij).right_inv y).symm,},
    rw this ((eqv n nj).inv_fun x),
    rw ←functor_to_types.map_comp_apply,

    simp only [eqv],
    simp only [equiv.inv_fun_as_coe],
    rw [←equiv.symm_trans_apply,←equiv.symm_trans_apply],
    rw [equiv.of_bijective_trans,equiv.of_bijective_trans],
    rw [←equiv.inv_fun_as_coe,←equiv.inv_fun_as_coe],
    simp_rw ←types_comp,
    simp_rw ←functor.map_comp',
    reflexivity, },
  { obtain ⟨m,mj,mj',meq⟩ := (s j).prop,
    simp, simp at meq, rw ←meq,
    dsimp [eqv],
    apply equiv.of_bijective_apply_symm_apply,},


end

instance directed_of_cofinal {J : Type u} [preorder J] [is_directed J has_le.le]
  (I : set J) (Icof : ∀ j : J, ∃ i ∈ I, j ≤ i) : is_directed I has_le.le :=
begin
  apply is_directed.mk,
  rintros ⟨i,iI⟩ ⟨k,kI⟩,
  obtain ⟨j,ij,kj⟩ := directed_of (has_le.le) i k,
  obtain ⟨m,mI,jm⟩ := Icof j,
  use ⟨m,mI⟩,simp,
  exact ⟨ij.trans jm, kj.trans jm⟩,
end

instance lower_directed {J : Type u} [preorder J] [is_directed J has_le.le]
  (j : J) : is_directed {i : J | j ≤ i} has_le.le :=
begin
  apply directed_of_cofinal,
  rintros i,
  obtain ⟨k,ik,jk⟩ := directed_of (has_le.le) i j,
  exact ⟨k,jk,ik⟩,
end

-- The functor mapping i.op to (F.map (op_hom_of_le _)) ⁻¹ {x}
def fis.above_point {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) (j : Jᵒᵖ) (x : F.obj j) : {i : J | j.unop ≤ i}ᵒᵖ ⥤ Type v :=
begin
  let Fobj : Π (ii : {i : J | j.unop ≤ i}ᵒᵖ), set (F.obj $ opposite.op (ii.unop).val) :=
    λ ii, set.preimage (F.map $ op_hom_of_le ii.unop.prop) {x},

  have subfunctor : Π (ii kk : {i : J | j.unop ≤ i}ᵒᵖ) (ik : kk.unop ≤ ii.unop),
    set.maps_to (F.map $ ((by { apply op_hom_of_le, simp only [subtype.val_eq_coe, opposite.unop_op, subtype.coe_le_coe], exact ik }) : opposite.op (ii.unop).val ⟶ opposite.op (kk.unop).val)) (Fobj ii) (Fobj kk), by {
    rintro ii kk ik,
    dsimp only [Fobj],
    unfold set.maps_to,
    unfold set.preimage,
    rintro y hy,
    simp only [set.mem_singleton_iff, set.mem_set_of_eq] at hy,
    rcases hy with rfl,
    simp only [set.mem_singleton_iff, set.mem_set_of_eq],
    rw ←functor_to_types.map_comp_apply,
    reflexivity,},

  refine ⟨λ ii, subtype (Fobj ii),_,_,_⟩,
  { rintros ii kk ik,
    exact set.maps_to.restrict _ _ _ (subfunctor ii kk $ le_of_op_hom ik),},
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


instance fis.above_point.nonempty {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v)
  [Π (j : Jᵒᵖ), fintype (F.obj j)] [∀ (j : Jᵒᵖ), nonempty (F.obj j)]
  (j : Jᵒᵖ)
  (Fsurj : fis.is_surjective_onto F j)
  (x : F.obj j) :
  Π (i : {i : J | j.unop ≤ i}ᵒᵖ), nonempty ((fis.above_point F j x).obj i)  :=
begin
  rintro ii,
  dsimp [fis.above_point],
  unfold fis.is_surjective_onto at Fsurj,
  specialize Fsurj (opposite.op (ii.unop.val)) ii.unop.prop x,
  unfold set.preimage,
  simp,
  obtain ⟨y,rfl⟩ := Fsurj,
  apply Exists.intro,
  rotate,
  { rw ←subtype.val_eq_coe, use y, },
  { dsimp only [subtype.val_eq_coe] at *, fsplit,  /-thanks tidy I don't know what I'm doing here-/},
end

instance fis.above_point.fintype {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v)
  [Π (j : Jᵒᵖ), fintype (F.obj j)] [∀ (j : Jᵒᵖ), nonempty (F.obj j)]
  (j : Jᵒᵖ)
  (x : F.obj j) :
  Π (i : {i : J | j.unop ≤ i}ᵒᵖ), fintype ((fis.above_point F j x).obj i)  :=
begin
  rintros ii,
  obtain ⟨i,ij⟩ := ii.unop,
  unfold fis.above_point,
  simp,
  apply subtype.fintype,
end


-- This should maybe be split into more basic components…
def fis.sections_at_point {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) (j : Jᵒᵖ) (x : F.obj j) :
  {s : F.sections | s.val j = x} ≃ (fis.above_point F j x).sections :=
begin

  let fwd : {s : F.sections | s.val j = x} → (fis.above_point F j x).sections, by
  { rintro ⟨⟨s,sec⟩,sjx⟩,
    simp only [set.mem_set_of_eq] at sjx,
    rcases sjx with rfl,
    split, rotate,
    { rintro ii, dsimp only [fis.above_point],
      refine ⟨s (opposite.op ii.unop.val),_⟩,
      unfold set.preimage,
      unfold category_theory.functor.sections at sec,
      let lol1 := (ii.unop.prop : j.unop ≤ ii.unop.val), simp only [set.mem_set_of_eq] at lol1, rw ←subtype.val_eq_coe at lol1,
      let lol2 := (opposite.unop_op ii.unop.val),
      rw ←lol2 at lol1,
      exact sec (op_hom_of_le $ lol1),
     },
    { rintro ii kk ik, simp only [id.def], dsimp only [fis.above_point], rw ←subtype.coe_inj, simp only [set.maps_to.coe_restrict_apply, subtype.coe_mk], apply sec,},},


  let bwd_aux :  Π (s : (fis.above_point F j x).sections) (i : Jᵒᵖ),
                 {y : F.obj i | ∃ (k : Jᵒᵖ) (ik : i.unop ≤ k.unop) (jk : j.unop ≤ k.unop),
                                y =  F.map (op_hom_of_le ik) (s.val $ opposite.op ⟨k.unop,jk⟩).val}, by
  { rintro ⟨s,sec⟩ i,
    let m' := (directed_of (≤) i.unop j.unop).some,
    obtain ⟨mi',mj'⟩ := (directed_of (≤) i.unop j.unop).some_spec,
    let m := opposite.op m',
    have mi : opposite.unop i ≤ opposite.unop m, by {simp only [opposite.unop_op],exact mi'},
    have mj : opposite.unop j ≤ opposite.unop m, by {simp only [opposite.unop_op],exact mj'},
    use F.map (op_hom_of_le mi) (s $ opposite.op ⟨m.unop,mj⟩).val,
    exact ⟨m,mi,mj,rfl⟩,},

  let bwd : (fis.above_point F j x).sections → {s : F.sections | s.val j = x}, by
  { rintro ss,
    dsimp only [functor.sections],
    split, rotate,
    { split, rotate,
      { exact (λ i, (bwd_aux ss i).val) },
      { rintro i k ik',
        obtain ⟨m,mi,mj,meq⟩ := (bwd_aux ss i).prop,
        obtain ⟨n,nk,nj,neq⟩ := (bwd_aux ss k).prop,
        let l' := (directed_of (≤) m.unop n.unop).some,
        obtain ⟨lm',ln'⟩ := (directed_of (≤) m.unop n.unop).some_spec,
        let l := opposite.op l',
        have lm : opposite.unop m ≤ opposite.unop l, by {simp only [opposite.unop_op],exact lm'},
        have ln : opposite.unop n ≤ opposite.unop l, by {simp only [opposite.unop_op],exact ln'},
        simp only [subtype.val_eq_coe],
        rw [meq,neq],
        obtain ⟨s,sec⟩ := ss,
        simp only [subtype.val_eq_coe],
        unfold functor.sections at sec, simp at sec, dsimp [fis.above_point] at sec,
        rw ←(@sec (opposite.op ⟨l.unop, mj.trans lm⟩) (opposite.op ⟨m.unop, mj⟩) (op_hom_of_le $ lm)),
        rw ←(@sec (opposite.op ⟨l.unop, nj.trans ln⟩) (opposite.op ⟨n.unop, nj⟩) (op_hom_of_le $ ln)),
        dsimp [fis.above_point],
        rw ←functor_to_types.map_comp_apply,
        rw ←functor_to_types.map_comp_apply,
        rw ←functor_to_types.map_comp_apply,
        reflexivity, },},
    { simp only [subtype.val_eq_coe, set.mem_set_of_eq, subtype.coe_mk],
      obtain ⟨y,k,jk,jk',rfl⟩ := bwd_aux ss j,
      simp only [subtype.val_eq_coe, subtype.coe_mk],
      dsimp [fis.above_point,functor.sections] at ss,
      obtain ⟨s,sec⟩ := ss,
      simp only [subtype.coe_mk],
      obtain ⟨y,yh⟩ := s (opposite.op ⟨k.unop,jk⟩),
      dsimp only [set.preimage] at yh,
      simp only [subtype.coe_mk],
      exact yh,}
  },

  split, rotate 2,
  exact fwd,
  exact bwd,
  -- refine ⟨fwd,bwd,_,_⟩, -- I get timeouts trying to work from here :(
  { dsimp [function.left_inverse],
    rintro ⟨⟨s, sec⟩,sjx⟩,
    dsimp only [fwd],
    sorry -- maybe `dsimp fwd` will work
   },
  { dsimp [function.right_inverse,function.left_inverse],
    --rintro ⟨x,y⟩,
    --dsimp only [fwd,bwd],
    --obtain ⟨a,k,ki,kj,e⟩ := bwd_aux
    --simp,
    sorry, },
end

lemma fis.above_point.sections_nonempty  {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v)
  (j : Jᵒᵖ)
  (Fsurj : fis.is_surjective_onto F j)
  [Π (j : Jᵒᵖ), fintype (F.obj j)] [∀ (j : Jᵒᵖ), nonempty (F.obj j)]
  (x : F.obj j) : nonempty (fis.above_point F j x).sections :=
begin
  apply set.nonempty_coe_sort.mpr,
  exact @nonempty_sections_of_fintype_inverse_system _ _ _ (fis.above_point F j x) (fis.above_point.fintype F j x)  (fis.above_point.nonempty F j Fsurj x),
end

lemma fis.decomposition'  {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) [Π (j : Jᵒᵖ), fintype (F.obj j)] [∀ (j : Jᵒᵖ), nonempty (F.obj j)] (j : Jᵒᵖ) :
  F.sections ≃ Σ (x : F.obj j), (fis.above_point F j x).sections :=
begin
  apply equiv.trans,
  rotate 2,
  {exact Σ (x : F.obj j), {s : F.sections | s.val j = x},},
  {exact fis.decomposition F j,},
  {apply equiv.sigma_congr_right, exact fis.sections_at_point F j,},
end


lemma fis.sections_surjective {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) [Π (j : Jᵒᵖ), fintype (F.obj j)]
   (j : Jᵒᵖ) (Fsurj : fis.is_surjective_onto F j) : function.surjective (λ (s : F.sections), s.val j) :=
begin
    rintro x,
    haveI : Π (j : Jᵒᵖ), nonempty (F.obj j), by
    { rintro i,
      let l' := (directed_of (≤) i.unop j.unop).some,
      obtain ⟨li',lj'⟩ := (directed_of (≤) i.unop j.unop).some_spec,
      let l := opposite.op l',
      have li : opposite.unop i ≤ opposite.unop l, by {simp only [opposite.unop_op],exact li'},
      have lj : opposite.unop j ≤ opposite.unop l, by {simp only [opposite.unop_op],exact lj'},
      obtain ⟨y,rfl⟩ :=  Fsurj l lj x,
      use F.map (op_hom_of_le li) y,},

    obtain ⟨s_above⟩ := fis.above_point.sections_nonempty F j Fsurj x,
    obtain ⟨s,sgood⟩ := (fis.sections_at_point F j x).inv_fun s_above,
    exact ⟨s,sgood⟩,
end
