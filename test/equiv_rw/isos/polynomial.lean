import .basic
import algebra.category.CommRing.basic
import data.polynomial

universes u

open category_theory

noncomputable theory

@[reducible]
def Polynomial : CommRing → CommRing :=
(λ R, CommRing.of (polynomial R))

-- We want to build an instance of the (not-yet-written)
-- `iso_functorial Polynomial`.

-- How are we going to do that?
-- The only way is brute force: we're going to start at type level.

@[simp]
lemma refl_symm {α : Type*} : (equiv.refl α).symm = equiv.refl α := rfl

@[simp]
lemma polynomial.to_fun_as_coeff {α : Type*} [comm_semiring α] (p : polynomial α) (n : ℕ) :
  p.to_fun n = polynomial.coeff p n :=
begin
  refl,
end


lemma coeff_one_zero {α : Type*} [comm_semiring α] : polynomial.coeff (1 : polynomial α) 0 = (1 : α) :=
begin
  simp,
end

@[simp]
lemma zero_eq_succ_iff_false (n : ℕ) : 0 = n + 1 ↔ false := by tidy

lemma coeff_one_succ {α : Type*} [comm_semiring α] (n : ℕ) :
  polynomial.coeff (1 : polynomial α) (n+1) = (0 : α) :=
begin
  simp,
end

example {R S : CommRing.{u}} (i : R ⟶ S) (r : R) (h : r = 0) : i r = 0 :=
begin
  simp [h],
end

-- TODO make sure that if this lemma is missing, transport still mostly works.
@[simp]
lemma eq_zero_iff {R S : CommRing.{u}} (i : R ≅ S) (r : R) : i.hom r = 0 ↔ r = 0 :=
begin
  split,
  { intro h,
    replace h := congr_arg i.inv h,
    simpa using h, },
  { intro h, simp [h] }
end

-- set_option pp.all true
def iso_functorial.map.to_fun {R S : CommRing.{u}} (i : R ≅ S) : Polynomial R → Polynomial S :=
begin
  intro X,
  -- This certainly doesn't work yet, but we may be reasonably close.
  -- transport X with i,
  -- Let's try to do it by hand to see how it's meant to go.

  -- dsimp [Polynomial, polynomial, add_monoid_algebra],
  tactic.whnf_target,

  refine_struct { .. } ,

  have support := finsupp.support X,
  try { equiv_rw i at support }, -- who cares, it didn't even depend on R
  exact support,

  have to_fun := finsupp.to_fun X,
  have i' := (forget CommRing).map_iso i,
  equiv_rw i' at to_fun, -- but we need this to work without us constructing i' by hand
  exact to_fun,

  have mem_support_to_fun := finsupp.mem_support_to_fun X,
  dsimp,
  intros,
  simp,
  simp at mem_support_to_fun,
  apply mem_support_to_fun,
end.

-- Now we need to hope that all the algebraic axioms work out!

-- set_option pp.all true
def iso_functorial.map.map_one {R S : CommRing.{u}} (i : R ≅ S) :
  iso_functorial.map.to_fun i 1 = 1 :=
begin
  dsimp [iso_functorial.map.to_fun],
  ext,
  simp,
  split_ifs,
  { subst h,
    simp, },
  { simp, }
end

def iso_functorial.map.map_mul {R S : CommRing.{u}} (i : R ≅ S) (x y : Polynomial R) :
  iso_functorial.map.to_fun i (x * y) =
    iso_functorial.map.to_fun i x * iso_functorial.map.to_fun i y :=
begin
  dsimp [iso_functorial.map.to_fun],
  ext,
  simp,

end
-- etc

-- We can now put those facts together as

def iso_functorial.map {R S : CommRing} (i : R ≅ S) : Polynomial R ⟶ Polynomial S :=
{ to_fun := iso_functorial.map.to_fun i,
  map_one' := iso_functorial.map.map_one i,
  map_mul' := iso_functorial.map.map_mul i,
  map_zero' := sorry,
  map_add' := sorry, }

-- And then we need to prove `iso_functorial.map_id` and `iso_functorial.map_comp`,
-- which should be consequences of the behaviour of `transport`.
-- (Note that means "practical" rather than "logical" consequences, since `transport` is meta.)

def iso_functorial.map_id (R : CommRing) : iso_functorial.map (iso.refl R) = 𝟙 (Polynomial R) :=
begin
  ext,
  simp,
  dsimp [iso_functorial.map, iso_functorial.map.to_fun],
  simp,
  dsimp,
  simp,
end
def iso_functorial.map_comp : sorry := sorry
