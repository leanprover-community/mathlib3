import algebra ring_theory.ideals data.real.basic data.polynomial data.finset

universe u

namespace valuation

/-- A *valued ring* is an integral domain `α` together with a valuation `val : α → ℝ`,
which is positive definite, multiplicative, and satisfies the (weak) triangle inequality. -/
class valued_ring (α : Type u) [integral_domain α] :=
(val : α → ℝ)
(non_neg : ∀ a, val a ≥ 0)
(definite : ∀ a, val a = 0 ↔ a = 0)
(val_mul : ∀ a b, val (a * b) = val a * val b)
(val_add : ∀ a b, val (a + b) ≤ val a + val b)

/-- A *nonarchimedian valued ring* is a valued ring satisfying the strong (i.e nonarchimedian)
triangle inequality. -/
class nonarch_valued_ring (α : Type u) [integral_domain α] extends valued_ring α :=
(nonarch : ∀ a b, val (a + b) ≤ max (val a) (val b))

section valued_ring

open valued_ring

variables {α : Type u} [integral_domain α] [valued_ring α]

/-- Shows that the valuation of a nonzero element is nonzero. -/
lemma val_ne_zero {x : α} (h : x ≠ 0) : val x ≠ 0 := (mt (definite x).mp) h

/-- Shows that the valuation of a nonzero element is > 0. -/
lemma val_pos {x : α} (h : x ≠ 0) : val x > 0 := lt_of_le_of_ne (non_neg x) (ne.symm $ val_ne_zero h)

/-- Shows that the valuation of 1 equals 1. -/
lemma val_one : val (1 : α) = 1 :=
have h : val (1 : α) * val (1 : α) = val (1 : α), by rw[←val_mul, mul_one],
(domain.mul_left_inj (val_ne_zero (one_ne_zero : (1 : α) ≠ 0))).mp (by rw [h, mul_one])

/-- Shows that the valuation of -1 equals -1. -/
lemma val_neg_one : val (-1 : α) = 1 :=
have val (-1 : α) * val (-1 : α) = 1, by rw[←val_mul, neg_one_mul, neg_neg, val_one],
or.resolve_right
  ((mul_self_eq_one_iff _).mp this)
  (ne_of_gt (lt_of_lt_of_le zero_gt_neg_one (non_neg (-1 : α))))

/-- Shows that the valuation of -x equals x. -/
lemma val_neg (x : α) : val (-x) = val x := by rw[←mul_neg_one, val_mul, val_neg_one, mul_one]

end valued_ring

/-- The *valuation ring* of a nonarchimedien valued field is the subring of all
elements of valuation ≤ 1. -/
def valuation_ring (α : Type u) [discrete_field α] [nonarch_valued_ring α] :=
    {x : α // valued_ring.val x ≤ 1}

section valuation_ring

variables {α : Type u} [discrete_field α] [nonarch_valued_ring α]

/-- The addition on a valuation ring. -/
def add : valuation_ring α → valuation_ring α → valuation_ring α
| ⟨x, hx⟩ ⟨y, hy⟩ := ⟨x+y,
    le_trans (nonarch_valued_ring.nonarch _ _) (max_le_iff.2 ⟨hx,hy⟩)⟩

/-- The multiplication on a valuation ring. -/
def mul : valuation_ring α → valuation_ring α → valuation_ring α
| ⟨x, hx⟩ ⟨y, hy⟩ := ⟨x*y,
    begin rw valued_ring.val_mul, apply mul_le_one; {assumption <|> apply valued_ring.non_neg} end⟩

/-- The subtraction on a valuation ring. -/
def neg : valuation_ring α → valuation_ring α
| ⟨x, hx⟩ := ⟨-x, by rw[val_neg]; exact hx⟩

/-- The valuation ring is indeed a ring. -/
instance : ring (valuation_ring α) :=
begin
  refine { add := add,
           mul := mul,
           neg := neg,
           zero := ⟨0,
           begin
             rw [(valued_ring.definite (0:α)).2 rfl], exact zero_le_one,
           end
        ⟩,
           one := ⟨1, by rw[val_one]⟩,
           .. };
  {repeat {rintro ⟨_, _⟩}, simp [mul_assoc, left_distrib, right_distrib, add, mul, neg]}
end

lemma zero_def : ∀ x : valuation_ring α, x = 0 ↔ x.val = 0
| ⟨x, _⟩ := ⟨subtype.mk.inj, λ h, by simp at h; simp only [h]; refl⟩

@[simp] lemma add_def : ∀ (x y : valuation_ring α), (x+y).val = x.val + y.val
| ⟨x, hx⟩ ⟨y, hy⟩ := rfl

@[simp] lemma mul_def : ∀ (x y : valuation_ring α), (x*y).val = x.val * y.val
| ⟨x, hx⟩ ⟨y, hy⟩ := rfl

@[simp] lemma mk_zero {h} : (⟨0, h⟩ : valuation_ring α) = (0 : valuation_ring α) := rfl


-- There is a coercion from the valuation ring of α to α; these lemmas below prove that the
-- coercion has some natural properties.
instance : has_coe (valuation_ring α) α := ⟨subtype.val⟩

@[simp] lemma val_eq_coe (z : valuation_ring α) : z.val = ↑z := rfl

@[simp, move_cast] lemma coe_add : ∀ (z1 z2 : valuation_ring α), (↑(z1 + z2) : α) = ↑z1 + ↑z2
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp, move_cast] lemma coe_mul : ∀ (z1 z2 : valuation_ring α), (↑(z1 * z2) : α) = ↑z1 * ↑z2
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp, move_cast] lemma coe_neg : ∀ (z1 : valuation_ring α), (↑(-z1) : α) = -↑z1
| ⟨_, _⟩ := rfl

@[simp, move_cast] lemma coe_sub : ∀ (z1 z2 : valuation_ring α), (↑(z1 - z2) : α) = ↑z1 - ↑z2
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp, squash_cast] lemma coe_one : (↑(1 : valuation_ring α) : α) = 1 := rfl

@[simp, squash_cast] lemma coe_coe : ∀ n : ℕ, (↑(↑n : valuation_ring α) : α) = (↑n : α)
| 0 := rfl
| (k+1) := by simp [coe_coe]

@[simp, squash_cast] lemma coe_zero : (↑(0 : valuation_ring α) : α) = 0 := rfl

@[simp, move_cast] lemma cast_pow (x : valuation_ring α) : ∀ (n : ℕ), (↑(x^n) : α) = (↑x : α)^n
| 0 := by simp
| (k+1) := by simp [monoid.pow, pow]; congr; apply cast_pow

lemma mk_coe : ∀ (k : valuation_ring α), (⟨↑k, k.2⟩ : valuation_ring α) = k
| ⟨_, _⟩ := rfl

/-- Shows that the multiplication on the valuation ring is commutative -/
protected lemma vmul_comm : ∀ x y : valuation_ring α, x * y = y * x
| ⟨q1, h1⟩ ⟨q2, h2⟩ := show (⟨q1*q2, _⟩ : valuation_ring α) = ⟨q2*q1, _⟩,
  by simp[mul_comm]

/-- The valuation ring is a commutative ring -/
instance : comm_ring (valuation_ring α) :=
{ mul_comm := valuation.vmul_comm,
  ..valuation.ring }

/-- The valuation ring is an integral domain-/
instance : integral_domain (valuation_ring α) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero :=
    λ a b, begin
      repeat {rw[subtype.ext, val_eq_coe, val_eq_coe]},
      rw[coe_mul];
      exact eq_zero_or_eq_zero_of_mul_eq_zero
    end,
  zero_ne_one := by simp[subtype.ext]; exact zero_ne_one,
  ..valuation.comm_ring }

/-- The valuation ring is itself a valued ring -/
instance : nonarch_valued_ring (valuation_ring α) :=
{ val := λ x, valued_ring.val (x : α),
  non_neg := λ x, valued_ring.non_neg x,
  definite := λ x, by rw[subtype.ext]; simp; exact valued_ring.definite x,
  val_mul := λ x y, by rw[coe_mul]; exact valued_ring.val_mul x y,
  val_add := λ x y, by rw[coe_add]; exact valued_ring.val_add x y,
  nonarch := λ x y, by simp only [val_eq_coe, coe_add]; exact nonarch_valued_ring.nonarch x y }

end valuation_ring

end valuation

namespace henselian

open valuation polynomial

/-- A *henselian field* is a valued field `α` such that any irreducible polyomial
over this field . -/
class henselian_field (α : Type u) [discrete_field α] [valued_ring α] :=
(henselian : ∀ p : polynomial α, irreducible p →
    ∀ k ≤ nat_degree p, valued_ring.val (p.coeff k) ≤ max (valued_ring.val (p.coeff 0)) (valued_ring.val (p.leading_coeff)))


end henselian
