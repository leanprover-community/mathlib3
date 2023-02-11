/-
Copyright (c) 2022 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/

import topology.constructions
import measure_theory.constructions.borel_space

local attribute [-instance] quotient.measurable_space

lemma measurable_of_coinduced {X Y : Type*} (f : X → Y)
  [iX : topological_space X] [measurable_space X] [borel_space X]
  [measurable_space Y] [@borel_space Y (topological_space.coinduced f iX) _] :
  measurable f :=
begin
  intros t t_meas,
  let p : set Y → Prop := λ t',
    measurable_set (f ⁻¹' t'),
  apply @measurable_set.induction_on_open _ (topological_space.coinduced f iX) _ _ p,
  { intros U U_open,
    dsimp [p],
    exact (is_open_coinduced.mp U_open).measurable_set, },
  { dsimp [p],
    intros t' ht' ht'',
    exact ht''.compl, },
  { dsimp [p],
    intros f pf mf mf',
    rw set.preimage_Union,
    apply measurable_set.Union,
    exact mf', },
  { exact t_meas, },
end

lemma measurable_quotient_mk_of_borel_space {X : Type*} {s : setoid X} [topological_space X] [measurable_space X]
  [iX : borel_space X] [measurable_space (quotient s)] [borel_space (quotient s)] :
  measurable (quotient.mk' : X → quotient s) := measurable_of_coinduced _

example {X : Type*} {s : setoid X} [topological_space X] [measurable_space X]
  [iX : borel_space X] [measurable_space (quotient s)] [borel_space (quotient s)]
  (t : set (quotient s)) (ht : measurable_set ((quotient.mk' : X → quotient s) ⁻¹' t)) :
  measurable_set t :=
begin
  set π := (quotient.mk' : X → quotient s),
  let p : set X → Prop := λ u, π ⁻¹' (π '' u) = u →
    ∀ v : set (quotient s), π ⁻¹' v = u → measurable_set v,
  apply @measurable_set.induction_on_open _ _ _ _ p,
  {
    dsimp [p],
    rintros U U_open - v hv,
    apply is_open.measurable_set,
    rw is_open_coinduced,
    convert U_open,
  },
  {
    dsimp [p],
    rintros u u_meas hu hu' v hv,
    convert (hu _ vᶜ _).compl,
    { exact (compl_compl _).symm, },
    {
      sorry,
--      rw set.image_compl_eq at hu',
  --    rw set.preimage_compl at hu',
    },
    { rw set.preimage_compl,
      rw hv,
      exact (compl_compl _), },
  },
  {
    dsimp [p],
    intros f hf hf' hf'' hu v hv,
    have := congr_arg (λ (w : set X), π '' w) hv,
    simp only at this,
    rw set.image_Union at this,
    rw set.image_preimage_eq at this,
    {
      rw this,
      apply measurable_set.Union,
      intros i,
      apply hf'' i,

    },
  },
  {
    exact ht,
  },
  refl,
end

#exit

example {X : Type*} {s : setoid X} [topological_space X] [measurable_space X]
  [iX : borel_space X] :
  borel_space (quotient s) :=
{ measurable_eq :=
  begin
    rw borel,
    rw quotient.measurable_space,
    set π : X → quotient s := quotient.mk',
    ext t,
    change measurable_set (π ⁻¹' t) ↔ _, --measurable_space.generate_measurable _ t,
    -- transitivity @measurable_set X (borel X) (π ⁻¹' t),
    -- { apply iff_of_eq,
    --   congr,
    --   exact iX.measurable_eq, },
   {
      --change measurable_space.generate_measurable _ (π ⁻¹' t) ↔ _,
      split,
      {
        intros h,

        --refine @measurable_space.generate_from_induction (quotient s) _ _ _ _ _ _ _ _,
        sorry,
      },
      { intros h,
        refine measurable_space.generate_from_induction _ _ _ _ _ _ h,
        { intros t' ht',
          simp only [set.mem_set_of_eq] at ht',
          exact (is_open_coinduced.mp ht').measurable_set, },
        repeat {sorry},
      },
    },
  end
  }
