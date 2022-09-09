import category_theory.filtered
import topology.category.Top.limits
import data.finset.basic
import category_theory.category.basic
import category_theory.full_subcategory
import data.set.finite
import data.fintype.basic

import .misc
import .subfunctors

universes u v w

open classical
open category_theory

noncomputable theory
local attribute [instance] prop_decidable










namespace inverse_system

variables {J : Type u} [preorder J] [is_directed J ge] (F : J ⥤ Type v)


-- Thanks Junyan Xu
theorem nonempty_sections_of_fintype_inverse_system'
 [fin : Π (j : J), fintype (F.obj j)] [nempty : ∀ (j : J), nonempty (F.obj j)] : F.sections.nonempty :=
begin
  casesI is_empty_or_nonempty J,
  { exact ⟨is_empty_elim, is_empty_elim⟩, },
  { exact nonempty_sections_of_fintype_cofiltered_system _, },
end



/-- `F.is_surjective` means that all `F.map …` are surjective -/
def is_surjective : Prop := ∀ (i j : J) (h : i ≤ j) (x : F.obj j), x ∈ set.range (F.map (hom_of_le h))

/-- `F.is_surjective_on j` means that all `F.map` with codomain `j` are surjective-/
def is_surjective_on (j : J) : Prop :=
  ∀ (i : J) (h : i ≤ j), function.surjective (F.map (hom_of_le h))

lemma is_surjective_iff :
  (is_surjective F) ↔ ∀ (i j : J) (h : i ≤ j), function.surjective (F.map (hom_of_le h)) := by refl

/--
`F.to_surjective` is the “surjective” part of `F`, in the sense that only the elements `x : F.obj j`
that have preimages through all `F.map` with codomain `F.obj j` are kept.
  -/
def to_surjective (F : J ⥤ Type v) : J ⥤ Type v :=
  F.subfunctor
  (λ j, ⋂ (i : {i | i ≤ j}), set.range (F.map  (hom_of_le i.prop)))
  (by { rintro i j hij,
    rintro x h s ⟨⟨k, _⟩, rfl⟩,
    obtain ⟨l,lk,li⟩ := directed_of ge k i,
    rw set.mem_Inter at h,
    obtain ⟨y,rfl⟩ := h ⟨l, li⟩,
    use F.map (hom_of_le lk) y,
    rw [← functor_to_types.map_comp_apply, ← functor_to_types.map_comp_apply],
    refl, })


lemma to_surjective.subfunctor  (i j : J) (ij : i ⟶ j) :
  subtype.simps.coe ∘ (to_surjective F).map ij = (F.map ij) ∘ subtype.simps.coe := by
{ rintros, ext, refl, }

lemma to_surjective.subfunctor_apply (i j : J) (ij : i ⟶ j) (x : (to_surjective F).obj i) :
 subtype.simps.coe ((to_surjective F).map ij x) = F.map ij (subtype.simps.coe x) := by
{ rintros, refl, }

instance to_surjective.fintype [Π (j : J), fintype (F.obj j)] :
  Π (j : J), fintype  ((to_surjective F).obj j) :=
begin
  rintro j,
  apply subtype.fintype,
end



instance to_surjective.nonempty
  [Π (j : J), fintype (F.obj j)] [Π (j : J), nonempty (F.obj j)] :
  Π (j : J), nonempty  ((to_surjective F).obj j) :=
begin
  rintro j,
  dsimp only [to_surjective,functor.subfunctor],
  rw nonempty_subtype,
  refine sInter_of_directed_nonempty _ _ _,
  { rintro s ⟨⟨i,ij⟩,rfl⟩,
    exact set.range_nonempty _,},
  { -- Probably heavily golfable
    rintro X ⟨⟨i,ij⟩,rfl⟩ Y ⟨⟨k,kj⟩,rfl⟩,
    obtain ⟨l,lk,li⟩ := directed_of (≥) k i,
    have : hom_of_le lk ≫ hom_of_le kj = hom_of_le li ≫ hom_of_le ij, by reflexivity,
    use [set.range (F.map $ hom_of_le lk ≫ hom_of_le kj),l,lk.le.trans kj],
    { refl, },
    { split,
      { rw [this,functor.map_comp /-F hli hij-/,types_comp],
        apply set.range_comp_subset_range,},
      { rw [functor.map_comp /-F hlk hkj-/,types_comp],
        apply set.range_comp_subset_range,},},},
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
  --unfold is_surjective,
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
    refine sInter_of_directed_nonempty S Ssnempty _,
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
  simp only [set.mem_range,set.mem_set_of_eq, set.Inter_coe_set, subtype.val_eq_coe, subtype.exists],
  use s.val j,
  split,
  { refl, },
  { rintro s ⟨i,rfl⟩,
    simp only [set.mem_Inter], intro ij,
    exact ⟨s.val i, s.prop (hom_of_le ij)⟩, },
end

lemma sections_in_surjective' (s : F.sections) (j : J) :
  (s.val j) ∈ ⋂ (i : { i | i ≤ j}), set.range (F.map (hom_of_le i.prop)) :=
begin
  rw set.mem_Inter,
  rintro ⟨i,ij⟩,
  use s.val i,
  exact s.prop (hom_of_le ij),
end

def to_surjective.sections_equiv : F.sections ≃ (to_surjective F).sections :=
begin
  fsplit,
  { rintro s,
    exact ⟨λ j, ⟨s.val j, sections_in_surjective' F s j⟩,λ i j ij, subtype.mk_eq_mk.mpr (s.prop ij)⟩,
  },
  { rintro ⟨s,sec⟩,
    refine ⟨λ j, (s j).val,_⟩,
    rintro i j ij,
    let := sec ij,
    --dsimp [to_surjective,functor.subfunctor,set.maps_to.restrict,subtype.map] at this,
    simp only [←subtype.coe_inj, subtype.coe_mk] at this,
    exact this, },
  { simp only [function.left_inverse, eq_self_iff_true, set_coe.forall, implies_true_iff], },
  { simp only [function.right_inverse, function.left_inverse, subtype.val_eq_coe, set_coe.forall,
               subtype.coe_mk, subtype.coe_eta, eq_self_iff_true, implies_true_iff], },
end

def decomposition (j : J) :
  F.sections ≃ Σ (x : F.obj j), {s : F.sections | s.val j = x} :=
begin
  fsplit,
  { intro s, use s.val j, use s, simp, },
  { rintro ⟨_, s, _⟩, use s,},
  { simp [function.left_inverse], },
  { simp [function.right_inverse, function.left_inverse], tidy, }
end


def sections_injective (j : J)
  (inj : ∀ i : {i | i ≤ j}, function.injective $ F.map (hom_of_le i.prop)) :
  function.injective (λ (s :F.sections), s.val j) :=
begin
  rintros ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ hyp,
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
  --let surj := λ ii : {i | i ≤ j}, (bij ii).2,
  let eqv  := λ ii : {i | i ≤ j}, equiv.of_bijective (F.map (hom_of_le ii.prop)) (bij ii),
  refine ⟨sections_injective F j inj,_⟩,

  rintro x,

  let s :  Π (i : J), {y : F.obj i | ∃ (k : J) (ik : k ≤ i) (jk : k ≤ j),
                                       F.map (hom_of_le ik) ((eqv ⟨k,jk⟩).inv_fun x) = y}, by
  { rintro i,
    let m := (directed_of (≥) i j).some,
    obtain ⟨mi,mj⟩ := (directed_of (≥) i j).some_spec, -- can't `obtain ⟨m,mi,mj⟩` ??
    use F.map (hom_of_le mi) ((eqv ⟨m,mj⟩).inv_fun x),
    exact ⟨m,mi,mj,rfl⟩,},
  use (λ i, (s i).val),
  { rintro i k ik',
    let ik := le_of_hom ik',
    obtain ⟨m,mi,mj,meq⟩ := (s i).prop,
    obtain ⟨n,nk,nj,neq⟩ := (s k).prop,
    obtain ⟨l,lm,ln⟩ := (directed_of (≥) m n),

    have lmbij : function.bijective (F.map $ hom_of_le lm), by
    { refine (function.bijective.of_comp_iff' (bij ⟨m,mj⟩) (F.map $ hom_of_le lm)).mp _,
      rw [←category_theory.types_comp,←category_theory.functor.map_comp],
      exact bij ⟨l,lm.le.trans mj⟩, },
    have lnbij : function.bijective (F.map $ hom_of_le ln), by
    { refine (function.bijective.of_comp_iff' (bij ⟨n,nj⟩) (F.map $ hom_of_le ln)).mp _,
      rw [←category_theory.types_comp,←category_theory.functor.map_comp],
      exact bij ⟨l,ln.le.trans nj⟩, },

    simp only [subtype.val_eq_coe],
    rw [←meq,←neq,
        ←functor_to_types.map_comp_apply,
        ←(equiv.right_inv (equiv.of_bijective _ lmbij) ((eqv ⟨m,mj⟩).inv_fun x)),
        ←(equiv.right_inv (equiv.of_bijective _ lnbij) ((eqv ⟨n,nj⟩).inv_fun x))],
    simp only [equiv.inv_fun_as_coe, equiv.to_fun_as_coe, equiv.of_bijective_apply, functor_to_types.map_comp_apply],
    simp only [←functor_to_types.map_comp_apply],
    rw [←equiv.symm_trans_apply,←equiv.symm_trans_apply],
    rw [equiv.of_bijective_trans,equiv.of_bijective_trans],
    rw [←equiv.inv_fun_as_coe,←equiv.inv_fun_as_coe],
    simp_rw ←types_comp,
    simp_rw ←functor.map_comp',
    reflexivity, },
  { obtain ⟨m,mj,mj',meq⟩ := (s j).prop,
    simp only [subtype.val_eq_coe,←equiv.inv_fun_as_coe,←meq],
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


def above_point (j : J) (x : F.obj j) : {i : J | i ≤ j} ⥤ Type v :=
begin
  let Fobj : Π (ii : {i : J | i ≤ j}), set (F.obj $  (ii).val) :=
    λ ii, set.preimage (F.map $ hom_of_le ii.prop) {x},

  have subfunctor : Π (ii kk : {i : J | i ≤ j}) (ik : ii ≤ kk),
                    set.maps_to (F.map $ hom_of_le ik) (Fobj ii) (Fobj kk), by
  { rintro ii kk ik,
    rintro y hy,
    simp only [Fobj,set.mem_singleton_iff] at hy ⊢,
    dsimp at hy,
    rcases hy with rfl,
    simp only [set.mem_preimage, set.mem_singleton_iff],
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
  obtain ⟨y,rfl⟩ := Fsurj ( (ii.val)) ii.prop x,
  fapply nonempty.intro,
  use y,
  fsplit,  /-thanks tidy I don't know what I'm doing here-/
end

instance above_point.fintype [Π (j : J), fintype (F.obj j)] [∀ (j : J), nonempty (F.obj j)]
  (j : J) (x : F.obj j) :
  Π (i : {i : J | i ≤ j}), fintype ((above_point F j x).obj i)  :=
begin
  rintros ii,
  apply subtype.fintype,
end

lemma above_point.sections_nonempty (j : J) (Fsurj : is_surjective_on F j)
  [Π (j : J), fintype (F.obj j)] [∀ (j : J), nonempty (F.obj j)]
  (x : F.obj j) : nonempty (above_point F j x).sections :=
begin
  apply set.nonempty_coe_sort.mpr,
  exact @nonempty_sections_of_fintype_inverse_system' _ _ _ (above_point F j x)
    (above_point.fintype F j x)  (above_point.nonempty F j Fsurj x),
end

private def sections_at_point_fwd  (j : J) (x : F.obj j) :
  {s : F.sections | s.val j = x} → (above_point F j x).sections :=
λ ⟨⟨s,sec⟩,sjx⟩,
  ⟨(λ ii, ⟨s ii.val, eq.rec_on sjx $ sec $ hom_of_le ii.prop⟩),
    ( by
      { subst_vars,
        rintro ii kk ik,
        simp only [←subtype.coe_inj, set.maps_to.coe_restrict_apply, subtype.coe_mk],
        apply sec,})⟩

private def sections_at_point_bwd_aux (j : J) (x : F.obj j) :
  Π (s : (above_point F j x).sections) (i : J),
                 {y : F.obj i | ∃ (k : J) (ik : k ≤ i) (jk : k ≤ j),
                                y =  F.map (hom_of_le ik) (s.val $  ⟨k,jk⟩).val} :=
begin
  rintro ⟨s,sec⟩ i,
  let m := (directed_of (≥) i j).some,
  obtain ⟨mi,mj⟩ := (directed_of (≥) i j).some_spec,
  use F.map (hom_of_le mi) (s ⟨m,mj⟩).val,
  exact ⟨m,mi,mj,rfl⟩,
end

private def sections_at_point_bwd  (j : J) (x : F.obj j) :
  (above_point F j x).sections → {s : F.sections | s.val j = x} :=
λ ss,
⟨ ⟨ (λ i,  (sections_at_point_bwd_aux F j x ss i).val)
  , by
    { rintro i k ik',
      obtain ⟨m,mi,mj,meq⟩ := (sections_at_point_bwd_aux F j x ss i).prop,
      obtain ⟨n,nk,nj,neq⟩ := (sections_at_point_bwd_aux F j x ss k).prop,
      obtain ⟨l,lm,ln⟩ := (directed_of (≥) m n),
      obtain ⟨s,sec⟩ := ss,
      simp only [subtype.val_eq_coe,meq,neq],
      rw ←(@sec  ⟨l, lm.le.trans mj⟩ ⟨m, mj⟩ (hom_of_le $ lm)),
      rw ←(@sec  ⟨l, ln.le.trans nj⟩ ⟨n, nj⟩ (hom_of_le $ ln)),
      dsimp [above_point],
      simp only [←functor_to_types.map_comp_apply],
      reflexivity,} ⟩
, by
  { simp only [subtype.val_eq_coe, set.mem_set_of_eq, subtype.coe_mk],
    obtain ⟨y,k,jk,jk',rfl⟩ := sections_at_point_bwd_aux F j x ss j,
    simp only [subtype.val_eq_coe, subtype.coe_mk],
    dsimp [above_point,functor.sections] at ss,
    obtain ⟨s,sec⟩ := ss,
    simp only [subtype.coe_mk],
    obtain ⟨y,yh⟩ := s ⟨k,jk⟩,
    exact yh,}⟩


def sections_at_point (j : J) (x : F.obj j) :
  {s : F.sections | s.val j = x} ≃ (above_point F j x).sections :=
begin
  refine_struct ⟨sections_at_point_fwd F j x, sections_at_point_bwd F j x,_,_⟩,
  { dsimp only [function.left_inverse,sections_at_point_fwd,sections_at_point_bwd],
    rintro ⟨⟨s,sec⟩,sjx⟩,
    simp only [set.mem_set_of_eq] at sjx, rcases sjx with rfl,
    apply subtype.mk_eq_mk.mpr,
    apply subtype.mk_eq_mk.mpr,
    funext i,
    obtain ⟨a,k,ki,kj,e⟩ := sections_at_point_bwd_aux F j (s j) (sections_at_point_fwd F j (s j) ⟨⟨s, λ _ _, sec⟩,rfl⟩) i,
    rw ←sec (hom_of_le ki),
    dsimp only [sections_at_point_fwd] at e,
    simp only [e],},
  { dsimp only [function.right_inverse,function.left_inverse,
               sections_at_point_fwd,sections_at_point_bwd],
    rintro ⟨s,sec⟩,
    simp only [subtype.val_eq_coe, subtype.mk_eq_mk],
    funext i,
    obtain ⟨k,ki,kj,e⟩ := (sections_at_point_bwd_aux F j x (⟨s, @sec⟩ : (above_point F j x).sections) i).prop,
    rw ←sec (hom_of_le (by { exact ki} : (⟨k,kj⟩ : {i | i ≤ j}) ≤ i)),
    simp only [subtype.val_eq_coe] at e ⊢,
    -- ideally we'd do `rw e` here, but lean doesn't want that
    dsimp only [above_point],
    rcases s ⟨k,kj⟩ with ⟨y,y'⟩,-- magic going on here: deconstructing `s ⟨k,kj⟩` reverts `e`, which is actually nice for us
    simp only [←subtype.coe_inj,set.maps_to.coe_restrict_apply],
    rintro e, exact e,},
end


lemma decomposition' [Π (j : J), fintype (F.obj j)] [∀ (j : J), nonempty (F.obj j)] (j : J) :
  F.sections ≃ Σ (x : F.obj j), (above_point F j x).sections :=
begin
  transitivity Σ (x : F.obj j), {s : F.sections | s.val j = x},
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

lemma sections_surjective' [Π (j : J), fintype (F.obj j)]
  (j : J) (Fsurj : is_surjective F) :
  function.surjective (λ (s : F.sections), s.val j) :=
begin
  apply sections_surjective F j,
  rintro i ij, exact Fsurj i j ij,
end

lemma sections_fintype_to_injective
  [nonempty J] [Π (j : J), fintype (F.obj j)] [fintype F.sections]
  (Fsur : is_surjective F) :
  ∃ j : J, ∀ ii : {i | i ≤ j}, function.injective (F.map $ hom_of_le ii.prop) :=
begin
  have : Π (j : J), fintype.card (F.obj j) ≤ fintype.card F.sections, from
    λ j, fintype.card_le_of_surjective _ (sections_surjective' F j Fsur),
  let cards := set.range (λ j, fintype.card $ F.obj j),
  haveI cardsnem : cards.nonempty := set.range_nonempty (λ (j : J), fintype.card (F.obj j)),
  haveI cardsfin : cards.finite := by
  { apply set.finite.subset,
    exact {n : ℕ | n ≤ fintype.card ↥(functor.sections F)}.to_finite,
    rintro jm ⟨j,rfl⟩,
    exact this j,},
  let cards' := cardsfin.to_finset,
  have cards'nem : cards'.nonempty, by {finish,},
  let m := cards'.max' cards'nem,
  obtain mmem := cards'.max'_mem cards'nem,
  simp only [set.finite.mem_to_finset, set.mem_range] at mmem,
  obtain ⟨j,jm⟩ := mmem,

  use j,
  rintro ⟨i,ij⟩,
  apply function.bijective.injective,
  rw fintype.bijective_iff_surjective_and_card,
  split,
  { apply (is_surjective_iff F).mp Fsur,},
  { apply has_le.le.antisymm,
    { rw jm,
      apply cards'.le_max' (fintype.card $ F.obj i),
      simp only [set.finite.mem_to_finset, set.mem_range, exists_apply_eq_apply], },
    { apply fintype.card_le_of_surjective _ ((is_surjective_iff F).mp Fsur i j ij), },
  },
end



end inverse_system
