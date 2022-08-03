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


/-
I CAN'T prove that this subfunctor is surjective in general.
Here is an example when it isn't:
The preordered is ℕ, with F 0 = {0,1}, and F (succ n) = ℕ.
The map from F 1 to F 0 sends everything to 1.
The map from F 2 to F 1 is the identity
The map from F 3 to F 2 sends 0 and 1 to 0, and is the identity elsewhere
The map from F 4 to F 3 sends 0,1,2 to 0; and is the identity elsewhere
…
Then 1 ∈ F 0 is in all the ranges, but any preimage of 1 has no preimage "sufficiently high"
-/
def fis.to_surjective  {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) /- [Π (j : Jᵒᵖ), fintype (F.obj j)] [∀ (j : Jᵒᵖ), nonempty (F.obj j)] -/ : Jᵒᵖ ⥤ Type v :=
begin
  let bigger : Π (j : Jᵒᵖ), set Jᵒᵖ := λ j, {i : Jᵒᵖ | j.unop ≤ i.unop},
  let Fsur_obj : Π (j : Jᵒᵖ), set (F.obj j) := λ j, ⋂ (i : bigger j), set.range (F.map  (op_hom_of_le i.prop)),

  --have allnempty : Π (j : Jᵒᵖ), (Fsur_obj j).nonempty, by sorry,
  --have allfinite : Π (j : Jᵒᵖ), (Fsur_obj j).finite, by sorry,
  --have surjective : Π (j j' : Jᵒᵖ) (m : j' ⟶ j), Fsur_obj j ⊆ (F.map m) '' (Fsur_obj j'), by sorry,

  have subfunctor : Π (i j : Jᵒᵖ) (hij : i ⟶ j), set.maps_to (F.map hij) (Fsur_obj i) (Fsur_obj j), by
  { rintro i j hij,
    rintro x h,
    /-
    Assume x ∈ Fsur_obj i. Need to show F.map hij x ∈ Fsur_obj j.
    This amounts to showing that for all kj : k ⟶ j, F.map hij x ∈ set.range (F.map kj)
    -/
    suffices h : ∀ (k : bigger j), F.map hij x ∈ set.range (F.map (op_hom_of_le k.prop)),
    { rw set.mem_Inter,
      exact h, },
    rintros ⟨k,kj⟩,
    simp only [set.mem_set_of_eq] at kj,
    obtain ⟨l',lk',li'⟩ := directed_of (≤) k.unop i.unop,
    let l := opposite.op l',
    have lk : opposite.unop k ≤ opposite.unop l, by {simp,exact lk'},
    have li : opposite.unop i ≤ opposite.unop l, by {simp,exact li'},
    let hlk := op_hom_of_le lk,
    let hli := op_hom_of_le li,
    let hkj := op_hom_of_le kj,
    simp only [set.mem_Inter, set.mem_range] at h,
    obtain ⟨y,rfl⟩ := h ⟨l,li⟩,
    simp only [set.mem_range],
    use F.map hlk y,
    simp *,
    refine @eq.trans _ _ (F.map (hlk ≫ hkj) y) _ _ _,
    { simp *,
      dsimp,sorry,
    },
    { have : hlk ≫ hkj = hli ≫ hij, by { simp only [eq_iff_true_of_subsingleton], },
      rw this,
      simp,
      sorry,
    },
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

lemma fis.to_surjective.subfunctor {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) :
  ∀ (i j : Jᵒᵖ) (ij : i ⟶ j), subtype.simps.coe ∘ (fis.to_surjective F).map ij = (F.map ij) ∘ subtype.simps.coe :=
begin
  rintros i j ij,
  apply funext,
  rintros x,
  simp [set.maps_to.coe_restrict_apply],
  unfold subtype.simps.coe,
  dsimp,
  sorry,
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
    simp only [set.mem_set_of_eq] at ij,
    exact set.range_nonempty _,},
  { rintro X ⟨⟨i,ij⟩,rfl⟩ Y ⟨⟨k,kj⟩,rfl⟩,
    simp only [set.mem_set_of_eq] at ij, simp only [set.mem_set_of_eq] at kj,
    obtain ⟨l',lk',li'⟩ := directed_of (≤) k.unop i.unop,
    let l := opposite.op l',
    have lk : opposite.unop k ≤ opposite.unop l, by {simp only [opposite.unop_op],exact lk'},
    have li : opposite.unop i ≤ opposite.unop l, by {simp only [opposite.unop_op],exact li'},
    let hlk := op_hom_of_le lk,
    let hli := op_hom_of_le li,
    let hkj := op_hom_of_le kj,
    let hij := op_hom_of_le ij,
    let hkj := op_hom_of_le kj,
    have : hlk ≫ hkj = hli ≫ hij, by { simp only [eq_iff_true_of_subsingleton], },
    use set.range (F.map $ hlk ≫ hkj),
    use l,
    use kj.trans lk,
    simp only [functor.map_comp],
    {sorry},
    {sorry},
  },
end


lemma fis.to_surjective.is_surjective {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v)  : fis.is_surjective (fis.to_surjective F) :=
begin
  unfold fis.is_surjective,
  rintros i j ji ⟨x,xh⟩,
  have xh : x ∈ (⋂ (j' : Jᵒᵖ) (m : j' ⟶ i), set.range (F.map m)), by {exact xh},

  /-obtain ⟨y,rfl⟩ := set.mem_Inter₂.mp xh j ji,
  simp,
  use y,
  { suffices : y ∈ (⋂ (j' : Jᵒᵖ) (m : j' ⟶ j), set.range (F.map m)),
    { exact this },
    rw set.mem_Inter₂,
    rintro k kj,
    obtain ⟨z,ztox⟩ := set.mem_Inter₂.mp xh k (kj ≫ ji),
    induction ztox,
    simp,
    use z,

    sorry,
  },

  { rw ←subtype.coe_inj, simp only [subtype.coe_mk], simpa only, }-/
  sorry
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
