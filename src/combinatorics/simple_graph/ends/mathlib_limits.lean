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



universes u v w

-- fis = fintype_inverse_system

def fis.is_surjective  {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) [Π (j : Jᵒᵖ), fintype (F.obj j)] [∀ (j : Jᵒᵖ), nonempty (F.obj j)] : Prop :=
∀ (j j' : Jᵒᵖ) (m : j' ⟶ j) (x : F.obj j), x ∈ set.range (F.map m)

def fis.to_surjective  {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) [Π (j : Jᵒᵖ), fintype (F.obj j)] [∀ (j : Jᵒᵖ), nonempty (F.obj j)] : Jᵒᵖ ⥤ Type v := sorry




/-
def fis.cofinal_subsystem {J : Type u} [preorder J] [is_directed J has_le.le]
  (J' : set J) (J'cof : ∀ j : J, ∃ j' ∈ J', j ≤ j')
  (F : Jᵒᵖ ⥤ Type v) : F.sections ≃ ((category_theory.full_subcategory_inclusion J').comp F).sections := sorry
-/

/-
def fis.decomposition  {J : Type u} [preorder J] [is_directed J has_le.le]
  (F : Jᵒᵖ ⥤ Type v) [Π (j : Jᵒᵖ), fintype (F.obj j)] [∀ (j : Jᵒᵖ), nonempty (F.obj j)] (j : Jᵒᵖ) :
  F.sections ≃ Σ (x : F.obj j), {s : F.sections | s.val j = x} :=
begin

  rintro ⟨f,fs⟩,
  use f j,
  use f,
  let lol := eq.refl (f j),
  sorry,
end
-/
