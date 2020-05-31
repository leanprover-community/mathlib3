import algebra.category.CommRing.basic
import category_theory.hygienic

universes v u

open category_theory

-- We want to automate as much as possible the observation that
-- if R ≅ S as rings, then 0 = 1 in R implies 0 = 1 in S.

def zero_ring (R : Ring) : Prop := (0 : R) = (1 : R)

-- Ideally we'd like to just be able to write `@[derive hygienic]` there!

-- instance : hygienic.{v} zero_ring.{v} :=
-- { map := λ R S φ h,
--   begin sorry end }


section

variables {C : Type u} [category.{v} C]

class canonical_generalized_element {X : C} (x : Π Y, X ⟶ Y) :=
(comp_iso : ∀ {Y Y' : C} (φ : Y ≅ Y'), x Y ≫ φ.hom = x Y')

end

section

variables {C : Type (u+1)} [large_category C] [concrete_category C]

local attribute [instance] concrete_category.has_coe_to_sort
local attribute [instance] concrete_category.has_coe_to_fun

meta def canonical_auto_param : tactic unit := `[intros, simp]

class canonical (x : Π (Y : C), (Y : Type u)) :=
(iso_apply : ∀ {Y Y' : C} (φ : Y ≅ Y'), (φ.hom : Y → Y') (x Y) = x Y' . canonical_auto_param)

attribute [simp] canonical.iso_apply

end

-- instance canonical_zero : canonical (λ R : Ring, (0 : R)) := { }
-- instance canonical_one : canonical (λ R : Ring, (1 : R)) := { }

section

variables {C : Type (u+1)} [large_category C] [concrete_category C]

local attribute [instance] concrete_category.has_coe_to_sort
local attribute [instance] concrete_category.has_coe_to_fun

instance hygienic_canonical_eq_canonical
  (x y : Π (Y : C), (Y : Type u)) [canonical x] [canonical y] :
  hygienic.{u} (λ Y : C, x Y = y Y) :=
{ map := λ X Y φ,
  begin
    intro h,
    replace h := congr_arg (φ.hom : X → Y) h,
    simpa using h,
  end }

end

-- instance hygienic_zero_ring_2 : hygienic.{v} zero_ring.{v} :=
-- begin
--   change hygienic.{v} (λ R, zero_ring.{v} R),
--   dsimp only [zero_ring] { eta := ff },
--   apply hygienic_canonical_eq_canonical,
-- end

open tactic

meta def backtrack_aux (tactics : list (tactic unit)) : ℕ → tactic unit
| 0 := done <|> failed
| (n+1) := done <|> (tactics.map (λ t : tactic unit, t >> backtrack_aux n)).mfirst id

meta def backtrack (tactics : list (tactic unit)) : tactic unit :=
backtrack_aux tactics 5

example : ∃ n : ℕ, n = 2 :=
begin
  backtrack [`[fsplit], `[refl], `[exact 1], `[exact 2]],
end

meta def apply_no_instances (n : name) : tactic unit :=
do
  e ← mk_const n,
  tactic.apply e {instances := ff},
  skip

meta def synthesize_canonical : tactic unit :=
do
  t ← target,
  `(canonical _) ← pure t,
  `[exact {}],
  t ← pp t,
  tactic.trace format!"synthesized: {t}"

instance hygienic_zero_ring_3 : hygienic.{v} zero_ring.{v} :=
begin
  backtrack [apply_no_instances `hygienic_canonical_eq_canonical, `[apply_instance], synthesize_canonical],
end

/-- Given a tactic `tac` that can solve an application of `cls` in the right context,
    `tactic_derive_handler` uses it to build an instance declaration of `cls n`. -/
meta def tactic_derive_handler (cls : name) (tac : tactic unit) : derive_handler :=
λ p n,
if p.is_constant_of cls then
do decl ← get_decl n,
   cls_decl ← get_decl cls,
   env ← get_env,
   let ls := decl.univ_params.map level.param,
   let tgt : expr := expr.const n ls,
   tgt ← mk_app cls [tgt],
   (_, val) ← tactic.solve_aux tgt (intros >> tac),
   val ← instantiate_mvars val,
   let trusted := decl.is_trusted ∧ cls_decl.is_trusted,
   add_protected_decl
     (declaration.defn (n ++ cls)
             decl.univ_params
             tgt val reducibility_hints.abbrev trusted),
   set_basic_attribute `instance (n ++ cls) tt,
   pure true
else pure false

@[derive_handler, priority 2000] meta def hygienic_instance : derive_handler :=
tactic_derive_handler ``hygienic $
backtrack [apply_no_instances `hygienic_canonical_eq_canonical, `[apply_instance], synthesize_canonical]

@[derive hygienic]
def zero_ring' (R : Ring) : Prop := (0 : R) = (1 : R)
