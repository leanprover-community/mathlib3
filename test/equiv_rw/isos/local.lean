import equiv_rw.isos.basic


-- We want to prove `is_local_ring` is "hygienic"

set_option pp.proofs true
theorem is_local_ring_hygienic (R S : CommRing) (i : R ≅ S) (h : is_local_ring R) : is_local_ring S :=
begin
  tactic.whnf_target,
  split,

  { equiv_rw i.symm,
    simp,
    exact h.1, },
  { sorry
    --equiv_rw i.symm,  -- not there yet
    }
end

-- Okay, that didn't go so well. Let's do some work on `units` and `is_unit` first,
-- but remembering that this eventually needs to be automated!

@[reducible]
def Units : Mon → Group :=
(λ R, Group.of (units R))


@[functoriality]
lemma Mon.coe_as_forget (R : Mon.{u}) : (R : Type u) = (forget Mon.{u}).obj R := rfl

-- #print category_theory.iso.symm_hom
-- universes v
-- lemma category_theory.iso.symm_hom {C : Type u} [category.{v} C] {X Y : C} (i : X ≅ Y) : i.symm.hom = i.inv := rfl

-- again, our goal is to define an iso_functorial instance (or at least the fields thereof, for now)
def iso_functorial.map.to_fun' {R S : Mon.{u}} (i : R ≅ S) : Units R → Units S :=
begin
  intro S,
  tactic.whnf_target,

  refine_struct {..},
  { have val := units.val S,
    equiv_rw i at val,
    exact val, },
  { have inv := units.inv S,
    equiv_rw i at inv,
    exact inv, },
  { have val_inv := units.val_inv S,
    dsimp,
    apply i.symm.injective,
    simp,
    dsimp,
    simp,
    exact val_inv, },
  { have inv_val := units.inv_val S,
    dsimp,
    apply i.symm.injective,
    simp,
    dsimp,
    simp,
    exact inv_val, }
end
