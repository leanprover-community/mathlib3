#exit
import algebra.monoid_algebra.basic

def hm {k : Type*} [semiring k] {G : Type*} {M : Type*}
  [add_comm_monoid M] [has_scalar G M] [module k M] :
  has_scalar (monoid_algebra k G) M :=
⟨λ g m, finsupp.total G M k (λ g, g • m) g⟩

def hm2 {k : Type*} [semiring k] :
  has_scalar (monoid_algebra k k) (monoid_algebra k k) :=
⟨λ g m, g * m⟩

example {k : Type*} [semiring k] (x y : monoid_algebra k k) :
  @hm k _ k (monoid_algebra k k) _ _ _ = @hm2 k _ :=
begin
  ext1, ext1 x, ext1 y,
  show finsupp.total k _ k _ _ = x * y,
  refine x.induction_on _ _ _,
  intro r,
  refine y.induction_on _ _ _,
  intro s,
  simp only [monoid_algebra.of_apply, finsupp.smul_single', mul_one, finsupp.total_single, one_mul,
  monoid_algebra.single_mul_single],
  rw monoid_algebra.mul_def,

end

def X : ℕ := 5
def Y : ℕ := 5

variables (R : Type*) [ring R]

def zero := (1 : R) - 1
instance ermmm : has_zero R := ⟨zero R⟩
#check heq
def copy := R
instance : ring (copy R) := infer_instance --fails
instance : has_zero (copy R) := ⟨1⟩
example : (0 : copy R) = 1 := rfl
example : (0 : R) = 1 := rfl --fails
--example (n : ℕ) : n + 1 - 1 = n := rfl
instance : has_zero (copy R) :=
⟨((1 : R) - 1 : R)⟩
instance ermm : add_zero_class R :=
{ zero := zero R,
  add := (+),
  zero_add := λ a, by {show (1 : R) - 1 + a = a, simp },
  add_zero := λ a, by {show a + ((1 : R) - 1) = a, simp} }




lemma huh : ermm R = @add_monoid.to_add_zero_class R _ :=
begin
  ext, sorry,
end

lemma jhhjh (x : R) : x + zero R = x :=
@add_zero (@add_monoid.to_add_)


example (a : ℕ) : a + 0 = a := rfl
example (a : ℕ) : 0 + a = a := -- rfl fails
begin
  induction a with a ha,
  { refl }, -- 0 + 0 is defeq to 0
  { show nat.succ (0 + a) = nat.succ a, -- (0 + (a + 1)) is defined to be (0 + a) + 1
    rw ha --
    }
end
