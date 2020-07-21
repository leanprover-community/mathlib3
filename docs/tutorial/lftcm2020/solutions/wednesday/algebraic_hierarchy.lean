/-
This is a sorry-free file covering the material on Wednesday afternoon
at LFTCM2020. It's how to build some algebraic structures in Lean
-/

import data.rat.basic -- we'll need the rationals at the end of this file

/-
As a mathematician I essentially always start my Lean files with the following line:
-/
import tactic

/- That gives me access to all Lean's tactics
(see https://leanprover-community.github.io/mathlib_docs/tactics.html)
-/

/-

## The point of this file

The idea of this file is to show how to build in Lean what the computer scientists call
"an algebraic heirarchy", and what mathematicians call "groups, rings, fields, modules etc".

Firstly, we will define groups, and develop a basic interface for groups.

Then we will define rings, fields, modules, vector spaces, and just demonstrate
that they are usable, rather than making a complete interface for all of them.

Let's start with the theory of groups. Unfortunately Lean has groups already,
so we will have to do everything in a namespace
-/


namespace lftcm

/-

... which means that now when we define `group`, it will actually be called `lftcm.group`.

## Notation typeclasses

To make a term of type `has_mul G`, you need to give a map G^2 → G (or
more precisely, a map `has_mul.mul : G → G → G`. Lean's notation `g * h`
is notation for `has_mul.mul g h`. Furthermore, `has_mul` is a class.

In short, this means that if you write `[has_mul G]` then `G` will
magically have a multiplication called `*` (satisfying no axioms).

Similarly `[has_one G]` gives you `has_one.one : G` with notation `1 : G`,
and `[has_inv G]` gives you `has_inv.inv : G → G` with notation `g⁻¹ : G`

## Definition of a group

If `G` is a type, equipped with `* : G^2 → G`, `1 : G` and `⁻¹ : G → G`
then it's a group if it satisfies the group axioms.

-/

-- `group G` is the type of group structures on a type `G`.
-- first we ask for the structure
class group (G : Type) extends has_mul G, has_one G, has_inv G :=
-- and then we ask for the axioms
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

/-

Advantages of this approach: axioms look lovely.

Disadvantage: what if I want the group law to be `+`?? I have embedded `has_mul`
in the definition.

Lean's solution: develop a `to_additive` metaprogram which translates all theorems about
`group`s (with group law `*`) to theorems about `add_group`s (with group law `+`). We will
not go into details here.

-/

namespace group

-- let G be a group

variables {G : Type} [group G]

/-
Lemmas about groups are proved in this namespace. We already have some!
All the group axioms are theorems in this namespace. Indeed we have just defined

`group.mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c)`
`group.one_mul : ∀ (a : G), 1 * a = a`
`group.mul_left_inv : ∀ (a : G), a⁻¹ * a = 1`

Because we are in the `group` namespace, we don't need to write `group.`
everywhere.

Let's put some more theorems into the `group` namespace.

We definitely need `mul_one` and `mul_right_inv`, and it's a fun exercise to
get them. Here is a route:

`mul_left_cancel : ∀ (a b c : G), a * b = a * c → b = c`
`mul_eq_of_eq_inv_mul {a x y : G} : x = a⁻¹ * y → a * x = y`
`mul_one (a : G) : a * 1 = a`
`mul_right_inv (a : G) : a * a⁻¹ = 1`
-/

lemma mul_left_cancel (a b c : G) (Habac : a * b = a * c) : b = c :=
 calc b = 1 * b         : by rw one_mul
    ... = (a⁻¹ * a) * b : by rw mul_left_inv
    ... = a⁻¹ * (a * b) : by rw mul_assoc
    ... = a⁻¹ * (a * c) : by rw Habac
    ... = (a⁻¹ * a) * c : by rw mul_assoc
    ... = 1 * c         : by rw mul_left_inv
    ... = c             : by rw one_mul

-- more mathlib-ish proof:
lemma mul_left_cancel' (a b c : G) (Habac : a * b = a * c) : b = c :=
begin
  rw [←one_mul b, ←mul_left_inv a, mul_assoc, Habac, ←mul_assoc, mul_left_inv, one_mul],
end

lemma mul_eq_of_eq_inv_mul {a x y : G} (h : x = a⁻¹ * y) : a * x = y :=
begin
  apply mul_left_cancel a⁻¹,
  -- ⊢ a⁻¹ * (a * x) = a⁻¹ * y
  rw ←mul_assoc,
  -- ⊢ a⁻¹ * a * x = a⁻¹ * y (remember this means (a⁻¹ * a) * x = ...)
  rw mul_left_inv,
  -- ⊢ 1 * x = a⁻¹ * y
  rw one_mul,
  -- ⊢ x = a⁻¹ * y
  exact h
end

-- The same proof
lemma mul_eq_of_eq_inv_mul' {a x y : G} (h : x = a⁻¹ * y) : a * x = y :=
mul_left_cancel a⁻¹ _ _ $ by rwa [←mul_assoc, mul_left_inv, one_mul]

/-

So now we can finally prove `mul_one` and `mul_right_inv`.

But before we start, let's learn a little bit about the simplifier.

## The `simp` tactic -- Lean's simplifier

We have the theorems (axioms) `one_mul g : 1 * g = g` and
`mul_left_inv g : g⁻¹ * g = 1`. Both of these theorems are of
the form `A = B`, with `A` more complicated than `B`. This means
that they are *perfect* theorems for the simplifier. Let's teach
those theorems to the simplifier, by adding the `@[simp]` attribute to them.
An "attribute" is just a tag which we attach to a theorem (or definition).
-/

attribute [simp] one_mul mul_left_inv

/-

Now let's prove `mul_one` using the simplifier. This also a perfect
`simp` lemma, so let's also add the `simp` tag to it.

-/

@[simp] theorem mul_one (a : G) : a * 1 = a :=
begin
  apply mul_eq_of_eq_inv_mul,
  -- ⊢ 1 = a⁻¹ * a
  simp,
end

/-
The simplifier solved `1 = a⁻¹ * a` because it knew `mul_left_inv`.
Feel free to comment out the `attribute [simp] one_mul mul_left_inv` line
above, and observe that the proof breaks.

-/

-- term mode proof
theorem mul_one' (a : G) : a * 1 = a :=
mul_eq_of_eq_inv_mul $ by simp

-- see if you can get the simplifier to do this one too
@[simp] theorem mul_right_inv (a : G) : a * a⁻¹ = 1 :=
begin
  apply mul_eq_of_eq_inv_mul,
  -- ⊢ a⁻¹ = a⁻¹ * 1
  simp
end

-- Now here's a question. Can we train the simplifier to solve the following problem:

--example (a b c d : G) :
--  ((a * b)⁻¹ * a * 1⁻¹⁻¹⁻¹ * b⁻¹ * b * b * 1 * 1⁻¹)⁻¹ = (c⁻¹⁻¹ * d * d⁻¹ * 1⁻¹⁻¹ * c⁻¹⁻¹⁻¹)⁻¹⁻¹ :=
--by simp

-- Remove the --'s and see that it fails. Let's see if we can get it to work.

-- We start with two very natural `simp` lemmas.

@[simp] lemma one_inv : (1 : G)⁻¹ = 1 :=
begin
  apply mul_left_cancel (1 : G),
  simp,
end

@[simp] lemma inv_inv (a : G) : a⁻¹⁻¹ = a :=
begin
  apply mul_left_cancel a⁻¹,
  simp,
end

-- Here is a riskier looking `[simp]` lemma.

attribute [simp] mul_assoc -- recall this says (a * b) * c = a * (b * c)

-- The simplifier will now push all brackets to the right, which means
-- that it's worth proving the following two lemmas and tagging
-- them `[simp]`, so that we can still cancel a with a⁻¹ in these situations.

@[simp] lemma inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b :=
begin
  rw ←mul_assoc,
  simp,
end

@[simp] lemma mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b :=
begin
  rw ←mul_assoc,
  simp
end

-- Finally, let's make a `simp` lemma which enables us to
-- reduce all inverses to inverses of variables
@[simp] lemma mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply mul_left_cancel (a * b),
  rw mul_right_inv,
  simp,
end

/-

If you solved them all -- congratulations!
You have just turned Lean's simplifier into a normalising confluent
rewriting system for groups, following Knuth-Bendix.

https://en.wikipedia.org/wiki/Confluence_(abstract_rewriting)#Motivating_examples

In other words, the simplifier will now put any element of a free group
into a canonical normal form, and can hence solve the word problem
for free groups.

-/
example (a b c d : G) :
  ((a * b)⁻¹ * a * 1⁻¹⁻¹⁻¹ * b⁻¹ * b * b * 1 * 1⁻¹)⁻¹ = (c⁻¹⁻¹ * d * d⁻¹ * 1⁻¹⁻¹ * c⁻¹⁻¹⁻¹)⁻¹⁻¹ :=
by simp

-- Abstract example of the power of classes: we can define products of groups with instances

instance (G : Type) [group G] (H : Type) [group H] : group (G × H) :=
{ mul := λ k l, (k.1*l.1, k.2*l.2),
  one := (1,1),
  inv := λ k, (k.1⁻¹, k.2⁻¹),
  mul_assoc := begin
    intros a b c,
    cases a, cases b, cases c,
    ext;
    simp,
  end,
  one_mul := begin
    intro a,
    cases a,
    ext;
    simp,
  end,
  mul_left_inv := begin
    intro a,
    cases a,
    ext;
    simp
  end }

-- the type class inference system now knows that products of groups are groups
example (G H K : Type) [group G] [group H] [group K] : group (G × H × K) :=
by apply_instance

end group

-- let's make a group of order two.

-- First the elements {+1, -1}
inductive mu2
| p1 : mu2
| m1 : mu2

namespace mu2

-- Now let's do some CS stuff:

-- 1) prove it has decidable equality
attribute [derive decidable_eq] mu2

-- 2) prove it is finite
instance : fintype mu2 := ⟨⟨[mu2.p1, mu2.m1], by simp⟩, λ x, by cases x; simp⟩

-- now back to the maths.

-- Define multiplication by doing all cases
def mul : mu2 → mu2 → mu2
| p1 p1 := p1
| p1 m1 := m1
| m1 p1 := m1
| m1 m1 := p1

instance : has_mul mu2 := ⟨mul⟩

-- identity
def one : mu2 := p1

-- notation
instance : has_one mu2 := ⟨one⟩

-- inverse
def inv : mu2 → mu2 := id

-- notation
instance : has_inv mu2 := ⟨inv⟩

-- currently we have notation but no axioms

example : p1 * m1 * m1 = p1⁻¹ * p1 := rfl -- all true by definition

-- now let's make it a group
instance : group mu2 :=
begin
  -- first define the structure
  refine_struct { mul := mul, one := one, inv := inv },
  -- now we have three goals (the axioms)
  all_goals {exact dec_trivial}
end

end mu2


-- Now let's build rings and modules and stuff (via monoids and add_comm_groups)

-- a monoid is a group without inverses
class monoid (M : Type) extends has_mul M, has_one M :=
(mul_assoc : ∀ (a b c : M), a * b * c = a * (b * c))
(one_mul : ∀ (a : M), 1 * a = a)
(mul_one : ∀ (a : M), a * 1 = a)

-- additive commutative groups from first principles
class add_comm_group (A : Type) extends has_add A, has_zero A, has_neg A :=
(add_assoc : ∀ (a b c : A), a + b + c = a + (b + c))
(zero_add : ∀ (a : A), 0 + a = a)
(add_left_neg : ∀ (a : A), -a + a = 0)
(add_comm : ∀ a b : A, a + b = b + a)

-- Notation for subtraction is handy to have; define a - b to be a + (-b)
instance (A : Type) [add_comm_group A] : has_sub A := ⟨λ a b, a + -b⟩

-- rings are additive abelian groups and multiplicative monoids,
-- with distributivity
class ring (R : Type) extends monoid R, add_comm_group R :=
(mul_add : ∀ (a b c : R), a * (b + c) = a * b + a * c)
(add_mul : ∀ (a b c : R), (a + b) * c = a * c + b * c)

-- for commutative rings, add commutativity of multiplication
class comm_ring (R : Type) extends ring R :=
(mul_comm : ∀ a b : R, a * b = b * a)

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class has_scalar (R : Type) (M : Type) := (smul : R → M → M)

infixr ` • `:73 := has_scalar.smul

-- modules for a ring
class module (R : Type) [ring R] (M : Type) [add_comm_group M]
extends has_scalar R M :=
(smul_add : ∀(r : R) (x y : M), r • (x + y) = r • x + r • y)
(add_smul : ∀(r s : R) (x : M), (r + s) • x = r • x + s • x)
(mul_smul : ∀ (r s : R) (x : M), (r * s) • x = r • s • x)
(one_smul : ∀ x : M, (1 : R) • x = x)

-- for fields we let ⁻¹ be defined on the entire field, and demand 0⁻¹ = 0
-- and that a⁻¹ * a = 1 for non-zero a. This is merely for convenience;
-- one can easily check that it's mathematically equivalent to the usual
-- definition of a field.
class field (K : Type) extends comm_ring K, has_inv K :=
(zero_ne_one : (0 : K) ≠ 1)
(mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * a⁻¹ = 1)
(inv_zero : (0 : K)⁻¹ = 0)

-- the type of vector spaces
def vector_space (K : Type) [field K] (V : Type) [add_comm_group V] := module K V

/-
Exercise for the reader: define manifolds, schemes, perfectoid spaces in Lean.
All have been done! As you can see, it is clearly *feasible*, although it does
sometimes take time to get it right. It is all very much work in progress.

The extraordinary thing is that although these computer theorem
provers have been around for about 50 years, there has never been a serious
effort to make the standard definitions used all over modern mathematics in
one of them, and this is why these systems are rarely used in mathematics departments.
Changing this is one of the goals of the Leanprover community.
-/

/-

Let's check that we can make the rational numbers into a field. Of course
they are already a field in Lean, but remember that when we say `field`
below, we mean our just-defined structure `lftcm.field`.

-/

-- the rationals are a field (easy because all the work is done in the import)
instance : field ℚ :=
{ mul := (*),
  one := 1,
  mul_assoc := rat.mul_assoc,
  one_mul := rat.one_mul,
  mul_one := rat.mul_one,
  add := (+),
  zero := 0,
  neg := has_neg.neg, -- no () trickery for unary operators
  add_assoc := rat.add_assoc,
  zero_add := rat.zero_add,
  add_left_neg := rat.add_left_neg,
  add_comm := rat.add_comm,
  mul_add := rat.mul_add,
  add_mul := rat.add_mul,
  mul_comm := rat.mul_comm,
  inv := has_inv.inv, -- see neg
  zero_ne_one := rat.zero_ne_one,
  mul_inv_cancel := rat.mul_inv_cancel,
  inv_zero := inv_zero -- I don't know why rat.inv_zero was never explicitly defined
  }

/-
Below is evidence that we can prove basic theorems about these structures.
Note however that it is a *complete pain* because we are *re-implementing*
everything; `add_comm` defaults to Lean's version for Lean's `add_comm_group`s, so we
have to explicitly write `add_comm_group.add_comm` to use our own version.
The mathlib versions of these proofs are less ugly.
-/

variables {A : Type} [add_comm_group A]

lemma add_comm_group.add_left_cancel (a b c : A) (Habac : a + b = a + c) : b = c :=
begin
  rw ←add_comm_group.zero_add b,
  rw ←add_comm_group.add_left_neg a,
  rw add_comm_group.add_assoc,
  rw Habac,
  rw ←add_comm_group.add_assoc,
  rw add_comm_group.add_left_neg,
  rw add_comm_group.zero_add,
end

lemma add_comm_group.add_right_neg (a : A) : a + -a = 0 :=
begin
  rw add_comm_group.add_comm,
  rw add_comm_group.add_left_neg,
end

lemma add_comm_group.sub_eq_add_neg (a b : A) :
  a - b = a + -b :=
begin
  -- this is just our definition of subtraction
  refl
end

lemma add_comm_group.sub_self (a : A) : a - a = 0 :=
begin
  rw add_comm_group.sub_eq_add_neg,
  rw add_comm_group.add_comm,
  rw add_comm_group.add_left_neg,
end

lemma add_comm_group.neg_eq_of_add_eq_zero (a b : A) (h : a + b = 0) : -a = b :=
begin
  apply add_comm_group.add_left_cancel a,
  rw h,
  rw add_comm_group.add_right_neg,
end

lemma add_comm_group.add_zero (a : A) : a + 0 = a :=
begin
  rw add_comm_group.add_comm,
  rw add_comm_group.zero_add,
end

variables {R : Type} [ring R]

lemma ring.mul_zero (r : R) : r * 0 = 0 :=
begin
  apply add_comm_group.add_left_cancel (r * 0),
  rw ←ring.mul_add,
  rw add_comm_group.add_zero,
  rw add_comm_group.add_zero,
end

lemma ring.mul_neg (a b : R) : a * -b = -(a * b) :=
begin
  symmetry,
  apply add_comm_group.neg_eq_of_add_eq_zero,
  rw ←ring.mul_add,
  rw add_comm_group.add_right_neg,
  rw ring.mul_zero
end

lemma ring.mul_sub (R : Type) [comm_ring R] (r a b : R) : r * (a - b) = r * a - r * b :=
begin
  rw add_comm_group.sub_eq_add_neg,
  rw ring.mul_add,
  rw ring.mul_neg,
  refl,
end

lemma comm_ring.sub_mul (R : Type) [comm_ring R] (r a b : R) : (a - b) * r = a * r - b * r :=
begin
  rw comm_ring.mul_comm (a - b),
  rw comm_ring.mul_comm a,
  rw comm_ring.mul_comm b,
  apply ring.mul_sub
end


-- etc etc, for thousands of lines of mathlib, which develop the interface
-- abelian groups, rings, commutative rings, modules, fields, vector spaces etc.

end lftcm

/-

## Advertisement

Finished the natural number game? Have Lean installed? Want more games/exercises?
Take a look at the following projects, many of which are ongoing but
the first three of which are pretty much ready:

*) The complex number game (complete, needs to be played within VS Code)

https://github.com/ImperialCollegeLondon/complex-number-game

To install, type
`leanproject get ImperialCollegeLondon/complex-number-game`
and then just open the levels in `src/complex`.

*) Undergraduate level mathematics Lean puzzles (plenty of stuff here,
and more appearing over the summer):

https://github.com/ImperialCollegeLondon/Example-Lean-Projects

`leanproject get ImperialCollegeLondon/Example-Lean-Projects`

*) The max mini-game (a simple browser game like the natural number game)

http://wwwf.imperial.ac.uk/~buzzard/xena/max_minigame/

(this is part of what will become the real number game, a game to teach
series, sequences and limits etc like the natural number game):

`leanproject get ImperialCollegeLondon/real-number-game`

*) Some commutative algebra experiments (ongoing work to prove the Nullstellensatz,
going slowly because I'm busy):

https://github.com/ImperialCollegeLondon/M4P33/blob/1a179372db71ad6802d11eacbc1f02f327d55f8f/src/for_mathlib/commutative_algebra/Zariski_lemma.lean#L80-L81

`leanproject get ImperialCollegeLondon/M4P33`

*) The group theory game (work in progress, expect more progress over the summer,
as a couple of undergraduates are working on it)

https://github.com/ImperialCollegeLondon/group-theory-game

`leanproject get ImperialCollegeLondon/group-theory-game`

*) Galois theory experiments

https://github.com/ImperialCollegeLondon/P11-Galois-Theory

`leanproject get ImperialCollegeLondon/P11-Galois-Theory`

*) Beginnings of the theory of condensed sets (currently on hold because
we need a good interface for abelian categories in mathlib)

https://github.com/ImperialCollegeLondon/condensed-sets

`leanproject get ImperialCollegeLondon/condensed-sets`

## The Xena Project

Why do these projects exist? I (Kevin Buzzard) am interested in teaching
undergraduates how to use Lean. I have been running a club at Imperial College London
called the Xena Project for the last three years, I am proud that many Imperial
mathematics undegraduates have contributed to Lean's maths library, and three of them
(Chris Hughes, Kenny Lau, Amelia Livingston) have each contributed over 5,000 lines of
code. It is non-trivial to get your work into such a polished state that it
is acceptable to the mathlib maintainers. It is also very good practice.

I am running Lean summer projects this summer, on a Discord server. If you
know of any undergraduates who you think might be interested in Lean, please
direct them to the Xena Project Discord!

https://discord.gg/BgyVYgJ

Undergraduates use Discord for lots of things, and seem to be more likely
to use a Discord server than the Zulip chat. The Discord server is chaotic and
full of off-topic material -- quite unlike the Lean Zulip server, which is
professional and focussed. If you have a serious question about Lean,
ask it on the Zulip chat! But if you know an undergraduate who is interested
in Lean, they might be interested in the Discord server. We have meetings
every Thursday evening (UK time), with live Lean coding and streaming, speedruns,
there is music, people posting pictures of cats, Haikus, and so on. To a large
extent it is run by undergraduates and PhD students. Over the summer (July
and August 2020) there are also live Twitch talks at https://www.twitch.tv/kbuzzard ,
on Tuesdays 10am and Thursdays 4pm UK time (UTC+1), aimed at mathematics
undergraduates. It is an informal place for undergraduates to hang out and
meet other undergraduates who are interested in Lean.

I believe that it is crucial to make undergraduates aware of computer proof
verification systems, because one day (possibly a long time in the future,
but one day) these things will cause a paradigm shift in the way mathematics
is done, and the sooner young mathematicians learn about them, the sooner it will happen.

Prove a theorem. Write a function. @XenaProject

https://twitter.com/XenaProject

-/
