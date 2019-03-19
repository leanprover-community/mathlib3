import category_theory.isomorphism
import category_theory.types
import category_theory.core
import category_theory.instances.rings

open category_theory

universes u₁ v₁ u₂ v₂

namespace tactic
open tactic
open interactive
open interactive.types
open lean.parser

def nonempty_functor : Type ⥤ Prop :=
{ obj := λ X, nonempty X,
  map := λ X Y f ⟨h⟩, ⟨f h⟩ }

@[extensionality]
lemma has_mul.ext {α : Type u₁} {m m' : has_mul α}
  (w : ∀ a b : α, begin haveI := m, exact a * b end = begin haveI := m', exact a * b end) : m = m' :=
begin
  unfreeze_local_instances,
  induction m,
  induction m',
  congr,
  ext a b,
  exact w a b
end

def has_mul_functor : (core Type) ⥤ Type :=
{ obj := λ X, has_mul X,
  map := λ X Y f m,
  begin
    resetI,
    exact { mul := λ a b, f.hom (f.inv a * f.inv b) }
  end }

open category_theory.instances

def submodule_functor : (core CommRing) ⥤ Type :=
begin
  refine ⟨λ R, submodule R.α R.α ,_,_,_⟩, -- We assume that obj is given
  -- Let's first get rid of the auto_param mess
  all_goals {dsimp},
  -- Running intros doesn't hurt
  all_goals {intros},
  -- Let's try to define map
  work_on_goal 0 {
    -- I have no idea what to do. What do I need to do, to build a submodule?
    constructor,
    -- Let's work on the data first
    -- The only goal with data is the last one
    work_on_goal 3 {
      -- Well, were trying to transfer something, and now I need a set
      -- Where is the corresponding set on the other side?
      -- No sets in my assumptions
      -- Let's blast that submodule to pieces
      try {auto_cases}, -- fails
      cases a_1,
      -- Aah, now we have a set!
      -- Let's transfer it!
      -- cool_transfer a a_1_carrier
        -- this ↑ currently doesn't work, probably needs set_functor or so
      -- I'll fill it in manually:
      exact a.hom.val '' ‹_›
    },
    -- Wow, those remaining goals are massive
    -- Anyway, let's do some intros first
    all_goals {intros},
    -- We have to prove that things are elements of images
    all_goals {try {erw set.mem_image at *}}, -- Hmm, this doesn't do anything
    -- Ooh, we should have blasted the submodule to pieces in all our goals
    all_goals {cases a_1, dsimp at *},
    -- Let's try the rw again
    all_goals {erw set.mem_image at *}, -- Cool, now it worked
    -- Let's go goal by goal now
    { -- I need to prove that something exists,
      -- But I have no idea what to do
      -- Let's pretend we know
      let foo : _ := _,
      refine ⟨foo, _⟩,
      split, -- It's always good to split
      -- We could kill the first goal by
      -- assumption
      -- but that might be dangerous
      -- I don't know exactly why,
      -- but it is better to look at the second goal first
      work_on_goal 1 {
        -- Now I have no clue. But I need to prove some thing about that a
        try {auto_cases}, -- fails
        -- Blast it to pieces
        cases a,
        -- Get rid of the auto_param mess
        dsimp at *,
        -- Aah, I need to prove something about a_hom
        cases a_hom,
        dsimp,
        -- Ok, so now I need to prove something about a_hom_val
        try {cases a_hom_val}, -- That didn't work (Mathematician says: duh)
        -- Hey, but I've got another assumption that mentions a_hom_val
        -- Now would be a good time to update the instance cache
        resetI,
        try {simp *}, -- Too bad that simp doesn't trigger on ring homs
        convert is_add_monoid_hom.map_zero _, -- This will probably be a back lemma
      },
      work_on_goal 1 {
        -- Look! We have figured out foo
        try {refl}, -- fails
        -- I don't know why it fails. That's too bad
      },
      all_goals {
        try {assumption},
        try {apply_instance}
      },
      refl, -- Now it does work, of course
    },
  -- We can apply the exact same strategy for the other two goals
  work_on_goal 0 {
    -- Because we have to prove some existential,
    -- it feels safe to also do cases on some existentials
    cases a_2,
    cases a_3,
  },
  work_on_goal 1 {
    cases a_2,
  },
  all_goals {
    let foo : _ := _,
    refine ⟨foo, _⟩,
    split,
    work_on_goal 1 {
        cases a,
        dsimp at *,
        cases a_hom,
        dsimp,
        resetI,
        try {simp *},
    },
  },
  work_on_goal 1 {
    convert is_add_monoid_hom.map_add _,
  },
  -- Let's clean up some easy and innocent goals
  all_goals {
    try {apply_instance}
  },
  work_on_goal 2 {
    -- This is in our assumption list (modulo splitting and symmetry)
    dsimp at *,
    symmetry,
    exact a_2_h.2, -- Somehow this can't be closed by tauto or finish
  },
  work_on_goal 2 {
    dsimp at *,
    symmetry,
    exact a_3_h.2,
  },
  work_on_goal 1 {
    -- Once again, we can't close this by refl
    -- That is really disappointing, because I feel that should be the way to figure out foo.
    try {refl},
    -- The problem is probably that Lean can't figure out why `foo` is allowed to be defined as
    -- has.add blablah because it knows that `foo` may depend on X but it isn't aware of
    -- the fact that X is a ring, because that's hidden in the bundled structure.
  },
  all_goals {sorry}
  },

  all_goals {sorry}
end

def ideal_functor : (core CommRing) ⥤ Type :=
{ obj := λ R, ideal R.α,
  map := λ X Y f, begin dsimp [ideal], sorry end }

def is_local_functor : (core CommRing) ⥤ Prop :=
{ obj := λ R, is_local_ring R.α,
  map := λ X Y f, begin dsimp [is_local_ring], intro h, cases h with I uniq, fsplit, sorry end }


----------------Feeble attempts at writing the actual tactics below------------------------

#check reflected
meta def check_equal (a b : ℕ) : tactic unit :=
do let a' := reflected.to_expr `(a),
   let b' := reflected.to_expr `(b),
   trace a',
   trace b',
   failed

example : false :=
begin
check_equal 3 7
end

section
variables {D : Type (u₁+1)} [𝒟 : large_category D]
include 𝒟

set_option pp.universes true

structure functorial_preimage (e : D) :=
(E : Type (u₁+1) )
[ℰ : large_category E]
(F : E ⥤ D)
(e' : E)
(w : F.obj e' = e)
end


-- namespace functorial_preimage
-- variables {D : Type (u₁+1)} [𝒟 : large_category D]
-- include 𝒟

-- def comp
--   {e : D}
--   (p : functorial_preimage e)
--   (q : functorial_preimage p.e') :
--   functorial_preimage e

-- end functorial_preimage

variables {C : Type (u₁+1)} [𝒞 : large_category C]
include 𝒞


meta def make_more_functorial (X : C) (e : Type u₁) (p : functorial_preimage e) :
  tactic (list (functorial_preimage e)) := sorry

meta def make_functorial_aux (X : C) (e : Type u₁) (p : functorial_preimage e) :
  tactic (functorial_preimage e) :=
do
  -- Check if X = p.e' (as expressions?!)
  -- If so, just return p, it's what we want.
  -- Otherwise, call make_more_functorial X e p, and invoke make_functorial_aux on each element of that list.
  fail ""

meta def make_functorial' (X : C) (e : Type u₁) :
  tactic (functorial_preimage e) :=
let p : functorial_preimage e :=
{ E := Type u₁,
  F := functor.id (Type u₁),
  e' := e,
  w := by refl } in
do make_functorial_aux X e p

meta def make_functorial (X : C) (e : Type u₁) :
  tactic { F : C ⥤ Type u₁ // F.obj X = e } :=
-- We do the final step without "do" blocks, because the universe levels need to change.
λ s,
match make_functorial' X e s with
| (interaction_monad.result.success q s') := interaction_monad.result.success ⟨ unchecked_cast q.F, unchecked_cast q.w ⟩ s'
| _ := sorry -- TODO handle exceptions!
end


namespace interactive
/--
`iso_rw e`, where `e : X ≅ Y`, `X Y : C` should try to replace all instances of `X` in the goal with `Y`.
To do this, it attempts to:
1. Re-expresses the goal as some functor `F : C ⥤ Type` applied to the object `X`.
2. Invokes `apply F.map (e.inv)`, to obtain the goal `F.obj Y`.
3. Substitute back in the definition of `F`, and definitionally simplify.
-/
meta def iso_rw (e : parse texpr) : tactic unit := sorry
end interactive
end tactic

variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

example (X Y Z : C) (α : X ≅ Y) (f : Y ⟶ Z) : X ⟶ Z :=
begin
  iso_rw α,
  exact f,
end

variables (D : Type u) [𝒟 : category.{u v} D]
include 𝒟

example (F G : C ⥤ D) (α : F ≅ G) (X : C) (Y : D) (f : G X ⟶ Y) : F X ⟶ Y :=
begin
  iso_rw α,
  exact f,
end

example
