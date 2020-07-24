-- import algebra.category.CommRing.limits
import topology.sheaves.presheaf_of_functions
import topology.sheaves.sheaf

open category_theory
open category_theory.limits
open topological_space

noncomputable theory

universe u

variables (X : Top.{u})

open Top

example (T : Type u) : sheaf_condition (presheaf_to_Type X T) :=
λ ι U,
begin
  refine fork.is_limit.mk _ _ _ _,
  { intros s f,
    change fork _ _ at s,
    dsimp only [sheaf_condition.fork, fork.of_ι],
    rintro ⟨x, mem⟩,
    -- dsimp at mem,
    change x ∈ supr U at mem, -- needs some lemmas!
    choose Ui H using mem,
    simp only [set.mem_range, set.mem_image, exists_exists_eq_and] at H,
    choose i hi using H.1, -- it would be nice to be able to write `rfl` instead of `hi`
    exact ((s.ι ≫ pi.π _ i) f) ⟨x, by { subst hi, exact  H.2, }⟩, },
  { intros s,
    dsimp,
    dsimp only [sheaf_condition.res],

    ext1 i,
    simp only [exists_prop, set.mem_range, set.mem_image, exists_exists_eq_and, category.assoc],
    ext1 f,
    ext1 x,
    simp only [limit.lift_π, types_comp_apply, fan.mk_π_app],
    rcases x with ⟨x, mem⟩,
    dsimp at mem,
    dsimp [presheaf_to_Type],
    let j : ι := _,
    have s₀ := s.condition =≫ pi.π _ (j, i),
    -- TODO make proper simp lemmas
    simp [sheaf_condition.left_res, sheaf_condition.right_res] at s₀,
    have s₁ := congr_fun s₀ f,
    have s₂ := congr_fun s₁ ⟨x, _⟩,

    simp [presheaf_to_Type] at s₂,
    convert s₂, -- We did not deserve that.
    (do [g₁, g₂] ← tactic.get_goals, tactic.set_goals [g₁]),
    refine ⟨_, mem⟩,
    dsimp,
    obtain ⟨_, x_mem⟩ := classical.spec_of_eq_some (subtype.val_prop _ : j ∈ _), -- ninja!
    exact x_mem, },
  { intros s m w,
    dsimp,
    ext1 f,
    ext1 ⟨x, mem⟩,
    dsimp,
    specialize w walking_parallel_pair.zero,
    let j : ι := _,
    replace w := w =≫ pi.π _ j,
    dsimp at w,
    have w' := congr_fun w f,
    have w'' := congr_fun w' ⟨x, _⟩,
    convert w'',
     }
end


-- example (T : Top.{u}) : sheaf_condition (presheaf_to_Top X T) :=
-- λ ι U,
-- { lift := λ s f,
--   begin
--     change fork _ _ at s,
--     dsimp [sheaf_condition.fork, fork.of_ι],
--     fsplit,
--     { rintro ⟨x, mem⟩,
--       dsimp at mem,
--       change x ∈ supr U at mem, -- needs some lemmas!
--       choose Ui H using mem,
--       simp at H,
--       cases H with H₁ H,
--       choose i hi using H₁, -- it would be nice to be able to write `rfl` instead of `hi`
--       subst hi,
--       change x ∈ U i at H,
--       exact ((s.ι ≫ pi.π _ i) f).to_fun ⟨x, H⟩, },
--     { rw [continuous_iff_continuous_at],
--       rintro ⟨x, mem⟩,
--       dsimp at mem,
--       sorry, },
--   end,
--   fac' := sorry,
--   uniq' := sorry, }
