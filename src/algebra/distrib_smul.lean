import data.polynomial.coeff
import group_theory.group_action.basic
import linear_algebra.quotient

open_locale big_operators
open_locale polynomial

-- TODO: we can't extend `has_smul α β`, due to diamonds with `distrib_mul_action`
-- I think it goes away with definitional structure eta, or if `distrib_mul_action` extends this class.
class _root_.smul_zero_class (α β : Type*) [has_zero β] [has_smul α β] : Prop :=
(smul_zero : ∀ (a : α), a • (0 : β) = 0)

instance smul_with_zero.smul_zero_class
  {α β : Type*} [has_zero α] [add_zero_class β] [smul_with_zero α β] : smul_zero_class α β :=
{ smul_zero := smul_with_zero.smul_zero }

class _root_.distrib_smul (α β : Type*) [add_zero_class β] [has_smul α β]
  extends smul_zero_class α β : Prop :=
(smul_add : ∀ (a : α) (x y : β), a • (x + y) = a • x + a • y)

def distrib_smul.to_add_monoid_hom {α : Type*} (β : Type*) [add_monoid β] [has_smul α β]
  [distrib_smul α β] (x : α) : β →+ β :=
{ to_fun := (•) x,
  map_zero' := smul_zero_class.smul_zero x,
  map_add' := distrib_smul.smul_add x }

/-- Pushforward a distributive action along a surjective additive monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.distrib_smul {α β γ : Type*} [add_zero_class β] [add_zero_class γ]
  [has_smul α β] [distrib_smul α β] [has_smul α γ] (f : β →+ γ) (hf : function.surjective f)
  (smul : ∀ (c : α) x, f (c • x) = c • f x) :
  distrib_smul α γ :=
{ smul_add := λ c x y, by { rcases hf x with ⟨x, rfl⟩, rcases hf y with ⟨y, rfl⟩,
    simp only [← map_add f, ← smul, distrib_smul.smul_add] },
  smul_zero := λ c, by rw [← f.map_zero, ← smul, smul_zero_class.smul_zero] }

instance distrib_mul_action.distrib_smul
  {α β : Type*} [monoid α] [add_monoid β] [distrib_mul_action α β] : distrib_smul α β :=
{ smul_zero := smul_zero,
  smul_add := smul_add }

-- TODO: replace the existing finsupp.has_smul instance
noncomputable instance finsupp.has_smul' {α β γ : Type*} [has_zero γ] [has_smul α γ] [smul_zero_class α γ] :
  has_smul α (β →₀ γ) :=
{ smul := λ a v, finsupp.map_range ((•) a) (smul_zero_class.smul_zero a) v }

instance finsupp.smul_zero_class {α β γ : Type*} [has_zero γ] [has_smul α γ] [smul_zero_class α γ] :
  smul_zero_class α (β →₀ γ) :=
{ smul_zero := λ a, by { ext, exact smul_zero_class.smul_zero a } }

instance finsupp.distrib_smul {α β γ : Type*} [add_zero_class γ] [has_smul α γ] [distrib_smul α γ] :
  distrib_smul α (β →₀ γ) :=
{ smul_add := λ a x y, by { ext i, exact distrib_smul.smul_add a (x i) (y i) },
  .. finsupp.smul_zero_class }

-- TODO: replace the existing add_monoid_algebra.has_smul instance
noncomputable instance add_monoid_algebra.has_smul' {α K k : Type*} [semiring K] [has_smul α K] [smul_zero_class α K] :
  has_smul α (add_monoid_algebra K k) :=
finsupp.has_smul'

instance add_monoid_algebra.smul_zero_class {α K k : Type*} [semiring K] [has_smul α K] [smul_zero_class α K] :
  smul_zero_class α (add_monoid_algebra K k) :=
finsupp.smul_zero_class

instance add_monoid_algebra.distrib_smul {α K k : Type*} [semiring K] [has_smul α K] [distrib_smul α K] :
  distrib_smul α (add_monoid_algebra K k) :=
finsupp.distrib_smul

-- TODO: replace the existing polynomial.has_smul instance
noncomputable instance polynomial.has_smul' {α K : Type*} [semiring K] [has_smul α K] [smul_zero_class α K] : has_smul α K[X] :=
{ smul := λ a x, polynomial.of_finsupp (a • x.to_finsupp) }

-- TODO: replace the existing polynomial.coeff_smul lemma
lemma polynomial.coeff_smul' {α K : Type*} [semiring K] [has_smul α K] [smul_zero_class α K] (a : α) (x : K[X]) (n : ℕ) :
  (a • x).coeff n = a • x.coeff n :=
by { cases x, refl }

-- TODO: replace the existing polynomial.smul_C lemma
lemma polynomial.smul_C' {α K : Type*} [semiring K] [has_smul α K] [smul_zero_class α K] (a : α) (x : K) :
  a • polynomial.C x = polynomial.C (a • x) :=
begin
  ext i,
  rw [polynomial.coeff_smul', polynomial.coeff_C, polynomial.coeff_C],
  split_ifs; simp [smul_zero_class.smul_zero]
end

instance polynomial.smul_zero_class {α K : Type*} [semiring K] [has_smul α K] [smul_zero_class α K] :
  smul_zero_class α K[X] :=
{ smul_zero := λ a, by { ext, exact smul_zero_class.smul_zero a } }

instance polynomial.distrib_smul {α K : Type*} [semiring K] [has_smul α K] [distrib_smul α K] :
  distrib_smul α K[X] :=
{ smul_add := λ a x y, by { ext i, simp only [polynomial.coeff_smul', polynomial.coeff_add, distrib_smul.smul_add] },
  .. polynomial.smul_zero_class }

-- TODO: replace the existing `finset.smul_sum'` lemma
lemma finset.smul_sum' {α β γ : Type*} [add_comm_monoid β] [has_smul α β] [distrib_smul α β]
  (r : α) (f : γ → β) (s : finset γ) :
  r • ∑ x in s, f x = ∑ x in s, r • f x :=
(distrib_smul.to_add_monoid_hom β r).map_sum f s

instance polynomial.is_scalar_tower_right {α K : Type*} [semiring K] [has_smul α K] [distrib_smul α K]
  [is_scalar_tower α K K] : is_scalar_tower α K[X] K[X] :=
⟨λ a f g, by ext;
  simp_rw [smul_eq_mul, polynomial.coeff_mul, polynomial.coeff_smul', polynomial.coeff_mul, smul_mul_assoc, finset.smul_sum']⟩

instance submodule.quotient.distrib_smul' {R M : Type*} [ring R] [add_comm_group M] [md : module R M]
  {S : Type*} [has_smul S R] [has_smul S M] [distrib_smul S M] [is_scalar_tower S R M]
  (P : submodule R M) :
  distrib_smul S (M ⧸ P) :=
function.surjective.distrib_smul -- S M (M ⧸ P) _ _ _ _
  ⟨submodule.quotient.mk, rfl, λ _ _, rfl⟩ (surjective_quot_mk _) P^.quotient.mk_smul

instance submodule.quotient.distrib_smul {R M : Type*} [ring R] [add_comm_group M] [module R M]
  (P : submodule R M) : distrib_smul R (M ⧸ P) :=
submodule.quotient.distrib_smul' P

instance rat.distrib_smul {K : Type*} [division_ring K] : distrib_smul ℚ K :=
{ smul_zero := λ a, by rw [rat.smul_def, mul_zero],
  smul_add := λ a x y, by simp only [rat.smul_def, mul_add, rat.cast_add] }

instance rat.is_scalar_tower_right {K : Type*} [division_ring K] : is_scalar_tower ℚ K K :=
⟨λ a x y, by simp only [rat.smul_def, smul_eq_mul, mul_assoc]⟩

lemma polynomial.rat_smul_eq_C_mul {K : Type*} [division_ring K] (a : ℚ) (f : K[X]) :
  a • f = polynomial.C ↑a * f :=
begin
  ext i,
  rw [polynomial.coeff_smul', polynomial.coeff_C_mul, rat.smul_def],
end
