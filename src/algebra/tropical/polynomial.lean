import algebra.tropical.basic
import algebra.ordered_ring
import topology.algebra.polynomial
import analysis.convex.basic

universes u v
variables {R : Type u}

lemma ne_top_iff_exists {R : Type*} {x : with_top R} : x ≠ ⊤ ↔ ∃ (a : R), ↑a = x :=
option.ne_none_iff_exists

@[simp] lemma pow_succ_eq_zero_iff [monoid_with_zero R] [no_zero_divisors R]
  {a : R} {n : ℕ} :
  a ^ (n + 1) = 0 ↔ a = 0 :=
pow_eq_zero_iff (nat.zero_lt_succ _)

namespace tropical

section linear

section sub_neg

variable [add_group R]

instance : sub_neg_monoid (with_top R) :=
{ neg := λ x, x.map (λ a, -a),
  ..with_top.add_monoid }

@[simp] lemma with_top.neg_top : - (⊤ : with_top R) = ⊤ := rfl

lemma with_top.neg_coe (x : R) : (-x : with_top R) = ((-x : R) : with_top R) := rfl

@[simp] lemma with_top.neg_zero : (-0 : with_top R) = 0 :=
by rw [←with_top.coe_zero, with_top.neg_coe, neg_zero]

@[simp] lemma with_top.neg_neg (x : with_top R) : -(-x) = x :=
begin
  induction x using with_top.rec_top_coe;
  simp [with_top.neg_coe]
end

end sub_neg

section nsmul

section add_monoid

variables [add_monoid R] (n : ℕ) (x : with_top R)

lemma with_top.nsmul_coe (x : R) :
  n • (x : with_top R) = ((n • x : R) : with_top R) :=
(with_bot.coe_nsmul _ _).symm

@[simp] lemma with_top.succ_nsmul_eq_top_iff (n : ℕ) {x : with_top R} :
  (n + 1) • x = ⊤ ↔ x = ⊤ :=
begin
  induction x using with_top.rec_top_coe,
  { rw [succ_nsmul', with_top.add_top] },
  { simp only [with_top.nsmul_coe, with_top.coe_ne_top] }
end

lemma with_top.nsmul_top_of_ne_zero (hx : 0 < n) :
  n • (⊤ : with_top R) = ⊤ :=
begin
  obtain ⟨k, rfl⟩ := nat.exists_eq_succ_of_ne_zero hx.ne',
  simp
end

@[simp] lemma with_top.succ_nsmul_top (n : ℕ) :
  (n + 1) • (⊤ : with_top R) = ⊤ :=
by simp

end add_monoid

lemma with_top.nsmul_neg [add_group R] (n : ℕ) (x : with_top R) :
  n • - x = - (n • x) :=
begin
  induction x using with_top.rec_top_coe,
  { cases n,
    { simp },
    { simp } },
  { rw [with_top.neg_coe, with_top.nsmul_coe, neg_nsmul, with_top.nsmul_coe,
        with_top.neg_coe] }
end

end nsmul

section gsmul

section

variable [add_group R]

lemma with_top.gsmul_coe (r : ℤ) (x : R) :
  r • (x : with_top R) = ((r • x : R) : with_top R) :=
begin
  induction r using int.induction_on with r IH r IH,
  { simp },
  { simp [←int.coe_nat_succ] },
  { simp [←int.neg_succ_of_nat_coe', ←with_top.neg_coe] }
end

@[simp] lemma with_top.gsmul_zero (r : ℤ) :
  r • (0 : with_top R) = 0 :=
by rw [←with_top.coe_zero, with_top.gsmul_coe, gsmul_zero]

lemma with_top.zero_gsmul (x : with_top R) :
  (0 : ℤ) • x = 0 :=
by simp

@[simp] lemma with_top.gsmul_coe_succ_top (r : ℕ) :
  (r + 1 : ℤ) • (⊤ : with_top R) = ⊤ :=
by simp [←int.coe_nat_succ]

@[simp] lemma with_top.gsmul_neg_pred_top (r : ℕ) :
  (-(r : ℤ) - 1 : ℤ) • (⊤ : with_top R) = ⊤ :=
by simp [←int.neg_succ_of_nat_coe', ←with_top.neg_coe]

@[simp] lemma with_top.gsmul_top_of_ne_zero {r : ℤ} (hr : r ≠ 0) :
  r • (⊤ : with_top R) = ⊤ :=
begin
  induction r using int.induction_on with r IH r IH,
  { exact absurd rfl hr },
  { simp },
  { simp }
end

lemma with_top.mul_gsmul (x y : ℤ) (b : with_top R) :
  (x * y) • b = x • y • b :=
begin
  induction b using with_top.rec_top_coe,
  { by_cases hxy : x * y = 0,
    { rcases mul_eq_zero.mp hxy with rfl|rfl;
      simp [hxy] },
    { rw with_top.gsmul_top_of_ne_zero hxy,
      simp only [not_or_distrib, mul_eq_zero] at hxy,
      simp [hxy.left, hxy.right] } },
  { simp_rw [with_top.gsmul_coe, mul_gsmul] }
end

end

variable [add_comm_group R]

lemma with_top.gsmul_add (r : ℤ) (x y : with_top R) :
  r • (x + y) = r • x + r • y :=
begin
  rcases eq_or_ne r 0 with rfl|hr,
  { simp },
  induction x using with_top.rec_top_coe,
  { simp [hr] },
  induction y using with_top.rec_top_coe,
  { simp [hr] },
  { simp [with_top.gsmul_coe, ←with_top.coe_add] }
end

instance with_top.distrib_mul_action_int : distrib_mul_action ℤ (with_top R) :=
{ one_smul := by simp,
  mul_smul := with_top.mul_gsmul,
  smul_add := with_top.gsmul_add,
  smul_zero := with_top.gsmul_zero }

-- While we have `with_top.zero_gsmul`, we cannot have `module ℤ (with_top R)` due to missing
-- `add_smul`, with a counterexample of `0 = 0 • ⊤ = (1 + -1) • ⊤ = ⊤ + -⊤ = ⊤ ≠ 0`

end gsmul

variable [decidable_eq R]

instance [has_zero R] [has_mul R] : has_scalar R (with_top R) :=
⟨λ k x, (k : with_top R) * x⟩

lemma with_top.smul_def [has_zero R] [has_mul R] (k : R) (x : with_top R) :
  k • x = (k : with_top R) * x := rfl

@[simp] lemma with_top.smul_coe [has_zero R] [has_mul R] (k x : R) :
  k • (x : with_top R) = (k : with_top R) * x := rfl

@[simp] lemma with_top.zero_smul [has_zero R] [has_mul R] (x : with_top R) :
  (0 : R) • x = 0 := zero_mul x

@[simp] lemma with_top.smul_zero [has_zero R] [has_mul R] (k : R) :
  k • (0 : with_top R) = 0 := mul_zero k

lemma with_top.smul_top_of_ne_zero [has_zero R] [has_mul R] {k : R} (hk : k ≠ 0) :
  k • (⊤ : with_top R) = ⊤ :=
begin
  by_cases H : (⊤ : with_top R) = 0,
  { simp [H] },
  { refine if_neg _,
    simpa using hk }
end

@[simp] lemma with_top.coe_smul [mul_zero_class R] (k x : R) :
  ((k • x : R) : with_top R) = k * x :=
by simp [with_top.coe_mul]

instance [monoid_with_zero R] [no_zero_divisors R] [nontrivial R] : mul_action R (with_top R) :=
{ one_smul := by simp [with_top.smul_def],
  mul_smul := by simp [with_top.smul_def, with_top.coe_mul, mul_assoc],
  ..with_top.has_scalar }

instance (R : Type*) [decidable_eq R] [semiring R] [no_zero_divisors R] [nontrivial R] :
  distrib_mul_action R (with_top R) :=
{ smul_add := λ r x y, by {
    rcases eq_or_ne r 0 with rfl|hr,
    { simp },
    induction x using with_top.rec_top_coe,
    { simp [with_top.smul_top_of_ne_zero hr] },
    induction y using with_top.rec_top_coe,
    { simp [with_top.smul_top_of_ne_zero hr] },
    { rw [←with_top.coe_add, with_top.smul_coe, ←with_top.coe_mul, mul_add],
      simp [with_top.coe_mul, with_top.coe_add] } },
  smul_zero := λ _, mul_zero _,
  ..with_top.mul_action }

instance [add_monoid R] : monoid_with_zero (tropical (with_top R)) :=
{ zero_mul := λ x, untrop_injective (@with_top.top_add _ _ (untrop x)),
  mul_zero := λ x, untrop_injective (@with_top.add_top _ _ (untrop x)),
  ..tropical.has_zero,
  ..tropical.monoid }

instance [add_comm_monoid R] : comm_monoid_with_zero (tropical (with_top R)) :=
{ ..tropical.comm_semigroup, ..tropical.monoid_with_zero }

instance [add_group R] : group_with_zero (tropical (with_top R)) :=
{ inv_zero := untrop_injective (by simp),
  mul_inv_cancel := λ x, begin
    induction x using tropical.trop_rec,
    rw [ne.def, trop_eq_iff_eq_untrop, untrop_zero, ←ne.def, ne_top_iff_exists,
        ←untrop_inj_iff],
    rintro ⟨x, rfl⟩,
    simp [←with_top.coe_add, with_top.neg_coe]
  end,
  ..tropical.has_inv,
  ..tropical.has_div,
  ..tropical.nontrivial,
  ..tropical.monoid_with_zero }

instance [add_comm_group R] : comm_group_with_zero (tropical (with_top R)) :=
{ ..tropical.comm_semigroup, ..tropical.group_with_zero }

/--
An ordered module is an ordered additive commutative monoid
with a partial order in which the scalar multiplication is compatible with the order.
-/
@[protect_proj]
class ordered_module (R M : Type*)
  [ordered_semiring R] [ordered_add_comm_monoid M] [distrib_mul_action R M] : Prop :=
(smul_lt_smul_of_pos : ∀ {a b : M}, ∀ {c : R}, a < b → 0 < c → c • a < c • b)
(lt_of_smul_lt_smul_of_pos : ∀ {a b : M}, ∀ {c : R}, c • a < c • b → 0 < c → a < b)

section semiring

variables [linear_ordered_semiring R]

open polynomial

@[simp] lemma polynomial.add_eq_zero_iff {p q : polynomial (tropical (with_top R))} :
  p + q = 0 ↔ p = 0 ∧ q = 0 :=
by simp [polynomial.ext_iff, forall_and_distrib]

@[simp] def _root_.polynomial.eval_tropical_aux (p : polynomial (tropical (with_top R))) (x : R) :
  tropical (with_top R) :=
  eval (trop (x : with_top R)) p

/-- The tropical monomial induces a linear function. -/
lemma eval_tropical_aux_monomial_trop_coe (t x : R) (n : ℕ) :
  untrop ((monomial n (trop (t : with_top R))).eval_tropical_aux x) =
  t + n • x :=
by simp

@[simp] lemma pow_eq_zero_iff {R : Type*} [linear_ordered_add_comm_monoid R]
  {a : tropical (with_top R)} {n : ℕ} :
  a ^ n = 0 ↔ a = 0 ∧ 0 < n :=
by { cases n; simp }

lemma eval_tropical_aux_monomial_eq_zero_iff {n : ℕ} {t : tropical (with_top R)} {x : R} :
  (monomial n t).eval_tropical_aux x = 0 ↔ t = 0 :=
by simp

lemma eval_tropical_aux_monomial_trop_coe_ne_zero (x t : R) (n : ℕ) :
  (monomial n (trop (t : with_top R))).eval_tropical_aux x ≠ 0 :=
by simp

@[simp] lemma eval_trop_coe_eq_zero_iff {p : polynomial (tropical (with_top R))} {x : R} :
  eval (trop (x : with_top R)) p = 0 ↔ p = 0 :=
begin
  induction p using polynomial.induction_on' with p q hp hq n p,
  { simp [hp, hq, add_eq_zero_iff, eval_add] },
  { simp }
end

lemma eval_tropical_aux_eq_zero_iff {p : polynomial (tropical (with_top R))} {x : R} :
  p.eval_tropical_aux x = 0 ↔ p = 0 :=
by rw [polynomial.eval_tropical_aux, eval_trop_coe_eq_zero_iff]

def _root_.polynomial.eval_tropical (p : polynomial (tropical (with_top R))) (hp : p ≠ 0) (x : R) :
  R :=
with_top.untop (untrop (p.eval_tropical_aux x)) $
  mt (eval_tropical_aux_eq_zero_iff.mp ∘ congr_arg trop) hp

def _root_.polynomial.eval_tropical' (p : polynomial (tropical (with_top R))) (x : R) :
  with_top R :=
untrop (p.eval_tropical_aux x)

lemma eval_tropical'_eq_of_ne_zero (p : polynomial (tropical (with_top R))) (hp : p ≠ 0) :
  p.eval_tropical' = coe ∘ p.eval_tropical hp :=
begin
  ext1 x,
  obtain ⟨px, hpx⟩ : ∃ (px : R), (px : with_top R) = untrop (eval (trop x) p),
  { simpa [←ne_top_iff_exists, untrop_eq_iff_eq_trop] using hp },
  simp [polynomial.eval_tropical, polynomial.eval_tropical', ←hpx]
end

lemma eval_tropical'_apply_eq_of_ne_zero (p : polynomial (tropical (with_top R))) (hp : p ≠ 0)
  (x : R) : p.eval_tropical' x = p.eval_tropical hp x :=
by rw eval_tropical'_eq_of_ne_zero

lemma eval_tropical'_add (p q : polynomial (tropical (with_top R)))  :
  (p + q).eval_tropical' = p.eval_tropical' ⊓ q.eval_tropical' :=
funext $ λ _, by { simp only [polynomial.eval_tropical',
  inf_apply, untrop_add, eval_add, polynomial.eval_tropical_aux],
  convert inf_eq_min.symm,
  refine semilattice_inf.ext _,
  simp }

lemma eval_tropical_add (p q : polynomial (tropical (with_top R)))
  (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p + q ≠ 0) :
  (p + q).eval_tropical hpq = (p.eval_tropical hp) ⊓ (q.eval_tropical hq) :=
begin
  ext,
  rw [←with_top.coe_eq_coe, ←eval_tropical'_apply_eq_of_ne_zero, inf_apply, with_top.coe_inf,
      ←eval_tropical'_apply_eq_of_ne_zero, ←eval_tropical'_apply_eq_of_ne_zero,
      eval_tropical'_add p q, inf_apply]
end

@[simp] lemma eval_tropical'_zero  :
  polynomial.eval_tropical' (0 : polynomial (tropical (with_top R))) = ⊤ :=
begin
  ext1,
  simp [polynomial.eval_tropical']
end

end semiring

end linear

section concave

variables [linear_ordered_semiring R] (p : polynomial (tropical (with_top R)))

open polynomial

section convex

variables {E S β : Type*} [add_comm_monoid E] [ordered_add_comm_monoid β]

variable (S)

def convex' [linear_ordered_semiring S] [distrib_mul_action S E] (s : set E) :=
∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : S⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
  a • x + b • y ∈ s

/-- Concavity of functions -/
def concave_on' [linear_ordered_semiring S] [distrib_mul_action S E] [distrib_mul_action S β]
  (s : set E) (f : E → β) : Prop :=
  convex' S s ∧
  ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : S⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    a • f x + b • f y ≤ f (a • x + b • y)

variables {S} [linear_ordered_semiring S] [distrib_mul_action S E] [distrib_mul_action S β]

lemma convex'_univ : convex' S (set.univ : set E) :=
λ _ _ _ _ _ _ _ _ _, trivial

lemma concave_on'.inf {E S β : Type*} [add_comm_monoid E] [linear_ordered_add_comm_monoid β]
  [linear_ordered_semiring S] [distrib_mul_action S E] [distrib_mul_action S β]
  {s : set E} {f g : E → β} (hf : concave_on' S s f) (hg : concave_on' S s g) :
  concave_on' S s (f ⊓ g) :=
begin
  sorry
end

variables [decidable_eq R] [nontrivial R] [no_zero_divisors R]

attribute [semireducible] with_zero

lemma concave_on_eval_tropical_monomial (p : tropical (with_top R)) (n : ℕ) (hp : p ≠ 0)
  (hp' : monomial n p ≠ 0 := mt (monomial_eq_zero_iff _ _).mp hp) :
  concave_on' R set.univ ((monomial n p).eval_tropical hp') :=
begin
  refine ⟨convex'_univ, λ x y _ _ a b posa posb hab, _⟩,
  induction p using tropical.trop_rec,
  induction p using with_top.rec_top_coe,
  { simpa using hp },
  simp only [eval_tropical, eval_tropical_aux, smul_eq_mul, with_top.nsmul_coe, untrop_trop,
             with_top.coe_nat, untrop_mul, eval_monomial, untrop_pow,
             ←with_top.coe_mul, ←with_top.coe_add, with_top.untop_coe],
  rw [mul_add, add_right_comm, mul_add, ←add_assoc, ←add_mul, hab, one_mul, add_right_comm,
      add_assoc, add_le_add_iff_left, ←smul_eq_mul, ←smul_eq_mul, ←smul_eq_mul, ←smul_eq_mul,
      smul_comm a, smul_comm b, ←smul_add];
  apply_instance
end

lemma concave_on_eval_tropical'_monomial (p : tropical (with_top R)) (n : ℕ) :
  concave_on' R set.univ ((monomial n p).eval_tropical') :=
begin
  refine ⟨convex'_univ, λ x y hx hy a b posa posb hab, _⟩,
  rcases eq_or_ne p 0 with rfl|hp,
  { simp },
  { convert with_top.coe_le_coe.mpr
      ((concave_on_eval_tropical_monomial p n hp).right hx hy posa posb hab),
    { rw [eval_tropical'_eq_of_ne_zero _ (mt (monomial_eq_zero_iff _ _).mp hp),
          function.comp_apply, function.comp_apply, with_top.smul_def,
          with_top.smul_def, ←with_top.coe_mul, ←with_top.coe_mul, ←with_top.coe_add,
          with_top.coe_eq_coe, smul_eq_mul, smul_eq_mul] },
    { rw eval_tropical'_eq_of_ne_zero _ (mt (monomial_eq_zero_iff _ _).mp hp) } }
end

lemma concave_on_eval_tropical (p : polynomial (tropical (with_top R))) (hp : p ≠ 0) :
  concave_on' R set.univ (p.eval_tropical hp) :=
begin
  induction p using polynomial.induction_on' with p q IH IH' n p,
  { rcases eq_or_ne p 0 with rfl|hp',
    { rw [ne.def, zero_add] at hp,
      simpa using IH' hp },
    rcases eq_or_ne q 0 with rfl|hq',
    { rw [ne.def, add_zero] at hp,
      simpa using IH hp },
    rw eval_tropical_add _ _ hp' hq',
    exact concave_on'.inf (IH hp') (IH' hq') },
  { simp only [monomial_eq_zero_iff, ne.def] at hp,
    exact concave_on_eval_tropical_monomial _ _ hp }
end

local attribute [ext] has_inf

lemma concave_on_eval_tropical' (p : polynomial (tropical (with_top R))) :
  concave_on' R set.univ p.eval_tropical' :=
begin
  induction p using polynomial.induction_on' with p q hp hq n p,
  { rw eval_tropical'_add,
    convert concave_on'.inf hp hq,
    ext x y z : 4,
    convert rfl,
    refine lattice.ext _,
    simp },
  { exact concave_on_eval_tropical'_monomial p _ }
end

end convex

end concave

section topology

variables [topological_space R]

instance : topological_space (tropical R) :=
topological_space.coinduced trop infer_instance

lemma is_open_iff {s : set (tropical R)} :
  is_open s ↔ is_open (trop ⁻¹' s) := iff.rfl

lemma inducing_trop : inducing (trop : R → tropical R) :=
⟨begin
  ext s,
  refine ⟨λ hs, ⟨trop '' s, is_open_iff.mp _, s.preimage_image_eq injective_trop⟩,
          λ ⟨s', hs, h⟩, h ▸ hs⟩,
  rw [is_open_iff, s.preimage_image_eq injective_trop],
  exact hs
end⟩

lemma inducing_untrop : inducing (untrop : tropical R → R) :=
⟨begin
  ext s,
  refine ⟨λ hs, ⟨untrop '' s, _, s.preimage_image_eq injective_untrop⟩,
          λ ⟨s', hs, h⟩, h ▸ hs⟩,
  convert hs,
  rw set.image_eq_preimage_of_inverse (left_inverse_trop) (right_inverse_trop)
end⟩

lemma continuous_trop : continuous (trop : R → tropical R) := inducing_trop.continuous
lemma continuous_untrop : continuous (untrop : tropical R → R) := inducing_untrop.continuous

lemma embedding_trop : embedding (trop : R → tropical R) := ⟨inducing_trop, injective_trop⟩
lemma embedding_untrop : embedding (untrop : tropical R → R) := ⟨inducing_untrop, injective_untrop⟩

lemma open_embedding_trop : open_embedding (trop : R → tropical R) :=
⟨embedding_trop, by simp [is_open_iff]⟩

lemma open_embedding_untrop : open_embedding (untrop : tropical R → R) :=
⟨embedding_untrop, by {
  convert is_open_univ,
  ext x,
  simp only [set.mem_range, set.mem_univ, iff_true],
  use trop x,
  simp }⟩

instance [has_add R] [topological_space R] [h : has_continuous_add R] :
  has_continuous_mul (tropical R) :=
{ continuous_mul := by {
  simp_rw trop_mul_def,
  exact continuous_trop.comp (
    (continuous_untrop.comp continuous_fst).add (continuous_untrop.comp continuous_snd)) } }

end topology

end tropical
