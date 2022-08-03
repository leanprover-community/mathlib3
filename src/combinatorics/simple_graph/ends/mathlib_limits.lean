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

universes u v w

open classical

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
      rw set.mem_sInter,
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
∀ (j j' : Jᵒᵖ) (m : j' ⟶ j) (x : F.obj j), x ∈ set.range (F.map m)

def fis.to_surjective  {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) /- [Π (j : Jᵒᵖ), fintype (F.obj j)] [∀ (j : Jᵒᵖ), nonempty (F.obj j)] -/ : Jᵒᵖ ⥤ Type v :=
begin
  let Fsur_obj : Π (j : Jᵒᵖ), set (F.obj j) := λ j, ⋂ (j' : Jᵒᵖ) (m : j' ⟶ j), set.range (F.map m),
  --have allnempty : Π (j : Jᵒᵖ), (Fsur_obj j).nonempty, by sorry,
  --have allfinite : Π (j : Jᵒᵖ), (Fsur_obj j).finite, by sorry,
  --have surjective : Π (j j' : Jᵒᵖ) (m : j' ⟶ j), Fsur_obj j ⊆ (F.map m) '' (Fsur_obj j'), by sorry,

  have subfunctor : Π (i j : Jᵒᵖ) (ij : i ⟶ j), set.maps_to (F.map ij) (Fsur_obj i) (Fsur_obj j), by
  { rintro i j ij,
    rintro x h,
    /-
    Assume x ∈ Fsur_obj i. Need to show F.map ij x ∈ Fsur_obj j.
    This amounts to showing that for all kj : k ⟶ j, x ∈ set.range (F.map kj)
    -/
    suffices h : ∀ (k : Jᵒᵖ) (kj : k ⟶ j), F.map ij x ∈ set.range (F.map kj),
    { rw set.mem_Inter₂,
      exact h, },
    rintros k kj,
    obtain ⟨l',lk',li'⟩ := directed_of (≤) k.unop i.unop,
    let l := opposite.op l',
    let lk := lk'.hom.op, rw opposite.op_unop at lk,
    let li := li'.hom.op, rw opposite.op_unop at li,
    simp only [set.mem_Inter, set.mem_range] at h,
    obtain ⟨y,rfl⟩ := h l li,
    simp only [set.mem_range],
    use F.map lk y,
    rw [ ←category_theory.types_comp_apply (F.map lk) (F.map kj) y,
         ←category_theory.types_comp_apply (F.map li) (F.map ij) y,
         ←category_theory.functor.map_comp,
         ←category_theory.functor.map_comp],
    have : lk ≫ kj = li ≫ ij, by { simp only [eq_iff_true_of_subsingleton], },
    rw this,
  },
  refine ⟨(λ j, subtype (Fsur_obj j)),_,_,_⟩,
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

lemma fis.to_surjective.is_surjective {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v)  : fis.is_surjective (fis.to_surjective F) :=
begin

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
