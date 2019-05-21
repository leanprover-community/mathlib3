/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import tactic.basic

import data.nat.basic data.nat.prime data.multiset data.int.basic data.int.gcd
 algebra.group algebra.group_power algebra.ordered_ring

/-- `ℕ+` is the type of positive natural numbers. It is defined as a subtype,
  and the VM representation of `ℕ+` is the same as `ℕ` because the proof
  is not stored. -/
def pnat := {n : ℕ // n > 0}
notation `ℕ+` := pnat

instance coe_pnat_nat : has_coe ℕ+ ℕ := ⟨subtype.val⟩
instance : has_repr ℕ+ := ⟨λ n, repr n.1⟩

namespace nat

/-- Convert a natural number to a positive natural number. The
  positivity assumption is inferred by `dec_trivial`. -/
def to_pnat (n : ℕ) (h : n > 0 . tactic.exact_dec_trivial) : ℕ+ := ⟨n, h⟩

/-- Write a successor as an element of `ℕ+`. -/
def succ_pnat (n : ℕ) : ℕ+ := ⟨succ n, succ_pos n⟩

@[simp] theorem succ_pnat_coe (n : ℕ) : (succ_pnat n : ℕ) = succ n := rfl

theorem succ_pnat_inj {n m : ℕ} : succ_pnat n = succ_pnat m → n = m :=
λ h, by {let h' := congr_arg (coe : ℕ+ → ℕ) h, exact nat.succ_inj h'}

/-- Convert a natural number to a pnat. `n+1` is mapped to itself,
  and `0` becomes `1`. -/
def to_pnat' (n : ℕ) : ℕ+ := succ_pnat (pred n)

@[simp] theorem to_pnat'_coe : ∀ (n : ℕ),
 ((to_pnat' n) : ℕ) = ite (n > 0) n 1
| 0 := rfl
| (m + 1) := by {rw[if_pos (succ_pos m)],refl}

end nat

namespace pnat

open nat

/-- We now define a long list of structures on ℕ+ induced by
 similar structures on ℕ. Most of these behave in a completely
 obvious way, but there are a few things to be said about
 subtraction, division and powers.
-/

instance : decidable_eq ℕ+ := λ (a b : ℕ+), by apply_instance

instance : decidable_linear_order ℕ+ :=
 subtype.decidable_linear_order _

@[simp] theorem pos (n : ℕ+) : (n : ℕ) > 0 := n.2

theorem eq {m n : ℕ+} : (m : ℕ) = n → m = n := subtype.eq

@[simp] theorem mk_coe (n h) : ((⟨n, h⟩ : ℕ+) : ℕ) = n := rfl

instance : add_comm_semigroup ℕ+ := {
  add := λ a b, ⟨a.val + b.val,add_pos a.property b.property⟩,
  add_comm := λ a b,subtype.eq (add_comm a.val b.val),
  add_assoc := λ a b c,subtype.eq (add_assoc a.val b.val c.val)
}

@[simp] theorem add_coe (m n : ℕ+) : ((m + n : ℕ+) : ℕ) = m + n := rfl
instance coe_add_hom : is_add_hom (coe : ℕ+ → ℕ) := ⟨add_coe⟩

instance : add_left_cancel_semigroup ℕ+ := {
  add_left_cancel := λ a b c h, by {
    replace h := congr_arg (coe : ℕ+ → ℕ) h,
    rw[add_coe,add_coe] at h,
    exact eq ((add_left_inj a.val).mp h)},
  .. (pnat.add_comm_semigroup)
}

instance : add_right_cancel_semigroup ℕ+ := {
  add_right_cancel := λ a b c h, by {
    replace h := congr_arg (coe : ℕ+ → ℕ) h,
    rw[add_coe,add_coe] at h,
    exact eq ((add_right_inj b.val).mp h)},
  .. (pnat.add_comm_semigroup)
}

@[simp] theorem ne_zero (n : ℕ+) : (n : ℕ) ≠ 0 := ne_of_gt n.2

@[simp] theorem to_pnat'_coe {n : ℕ} : n > 0 → (n.to_pnat' : ℕ) = n := succ_pred_eq_of_pos

@[simp] theorem coe_to_pnat' (n : ℕ+) : (n : ℕ).to_pnat' = n := eq (to_pnat'_coe n.pos)

instance : comm_monoid ℕ+ := {
  mul       := λ m n, ⟨m.1 * n.1, mul_pos m.2 n.2⟩,
  mul_assoc := λ a b c, subtype.eq (mul_assoc _ _ _),
  one       := succ_pnat 0,
  one_mul   := λ a, subtype.eq (one_mul _),
  mul_one   := λ a, subtype.eq (mul_one _),
  mul_comm  := λ a b, subtype.eq (mul_comm _ _)
}

/-- Recall that ℕ has its own specific power operation (which is
 preferred, probably for reasons of efficiency) as well as the
 general power operation that exists for any monoid.  We define
 the power operation on ℕ+ by restricting the one on ℕ, but
 this means that we need to give proofs that would be free if
 we used the general monoid version.
-/
instance : has_pow ℕ+ ℕ := ⟨λ n m, ⟨n.1 ^ m, nat.pow_pos n.2 m⟩⟩

@[simp] theorem one_coe : ((1 : ℕ+) : ℕ) = 1 := rfl
@[simp] theorem mul_coe (m n : ℕ+) : ((m * n : ℕ+) : ℕ) = m * n := rfl
instance coe_mul_hom : is_monoid_hom (coe : ℕ+ → ℕ) :=
 {map_one := one_coe, map_mul := mul_coe}

@[simp] theorem pow_coe (m : ℕ+) (n : ℕ) : ((m ^ n : ℕ+) : ℕ) = (m : ℕ) ^ n := rfl

@[simp] theorem pow_succ (m : ℕ+) (n : ℕ) : m ^ (n + 1) = m ^ n * m :=
eq (nat.pow_succ m n)

@[simp] theorem pow_add (m : ℕ+) (n p : ℕ) : m ^ (n + p) = m ^ n * m ^ p :=
eq (nat.pow_add m n p)

@[simp] theorem pow_mul (n p : ℕ) (m : ℕ+) : m ^ (n * p) = (m ^ n) ^ p :=
eq (nat.pow_mul n p m)

theorem pow_eq_pow (n : ℕ+) (m : ℕ) :
 @has_pow.pow _ _ monoid.has_pow n m = n ^ m :=
by induction m with m ih; [refl, rw [pnat.pow_succ, _root_.pow_succ, mul_comm, ih]]

instance : left_cancel_semigroup ℕ+ := {
  mul_left_cancel := λ a b c h, by {
   replace h := congr_arg (coe : ℕ+ → ℕ) h,
   exact eq ((nat.mul_left_inj a.pos).mp h),},
  .. (pnat.comm_monoid)
}

instance : right_cancel_semigroup ℕ+ := {
  mul_right_cancel := λ a b c h, by {
   replace h := congr_arg (coe : ℕ+ → ℕ) h,
   exact eq ((nat.mul_right_inj b.pos).mp h),},
  .. (pnat.comm_monoid)
}

instance : distrib ℕ+ := {
  left_distrib  := λ a b c, eq (mul_add a.val b.val c.val),
  right_distrib := λ a b c, eq (add_mul a.val b.val c.val),
  ..(pnat.add_comm_semigroup),..(pnat.comm_monoid)
}

/-- Subtraction a - b is defined in the obvious way when
  a > b, and by a - b = 1 if a ≤ b.
-/
instance : has_sub ℕ+ := ⟨λ a b,to_pnat' (a.val - b.val)⟩

theorem sub_coe (a b : ℕ+) : (((a - b) : ℕ+) : ℕ) = ite (a > b) ((a : ℕ) - (b : ℕ)) 1 :=
begin
  change ((to_pnat' (a.val - b.val)) : ℕ) = ite (a.val > b.val) (a.val - b.val) 1,
  split_ifs with h,
  {exact to_pnat'_coe (nat.sub_pos_of_lt h)},
  {rw[nat.sub_eq_zero_iff_le.mpr (le_of_not_gt h)],refl}
end

theorem add_sub_of_lt {a b : ℕ+} : a < b → a + (b - a) = b :=
 λ h, eq $ by {rw[add_coe,sub_coe,if_pos h],exact nat.add_sub_of_le (le_of_lt h)}

/-- We define m % k and m / k in the same way as for nat
  except that when m = n * k we take m % k = k and
  m / k = n - 1.  This ensures that m % k is always positive
  and m = (m % k) + k * (m / k) in all cases.  Later we
  define a function div_exact which gives the usual m / k
  in the case where k divides m.
-/

def mod_div_aux : ℕ+ → ℕ → ℕ → ℕ+ × ℕ
| k 0 q := ⟨k,q.pred⟩
| k (r + 1) q := ⟨⟨r + 1,nat.succ_pos r⟩,q⟩

lemma mod_div_aux_spec : ∀ (k : ℕ+) (r q : ℕ) (h : ¬ (r = 0 ∧ q = 0)),
 (((mod_div_aux k r q).1 : ℕ) + k * (mod_div_aux k r q).2 = (r + k * q))
| k 0 0 h := (h ⟨rfl,rfl⟩).elim
| k 0 (q + 1) h := by {
  change k.val + k.val * (q + 1).pred = 0 + k.val * (q + 1),
  rw[nat.pred_succ,nat.mul_succ,zero_add,add_comm]}
| k (r + 1) q h := rfl

def mod_div (m k : ℕ+) : ℕ+ × ℕ := mod_div_aux k (m.val % k.val) (m.val / k.val)

def mod (m k : ℕ+) : ℕ+ := (mod_div m k).1
def div (m k : ℕ+) : ℕ  := (mod_div m k).2

theorem mod_add_div (m k : ℕ+) : (m : ℕ) = (mod m k) + k * (div m k) :=
begin
  let h₀ := nat.mod_add_div m.val k.val,
  have : ¬ (m.val % k.val = 0 ∧ m.val / k.val = 0),
  by {rintro ⟨hr,hq⟩,rw[hr,hq,mul_zero,zero_add] at h₀,exact (m.ne_zero h₀.symm).elim},
  have := mod_div_aux_spec k (m.val % k.val) (m.val / k.val) this,
  exact (this.trans h₀).symm,
end

theorem mod_coe (m k : ℕ+) :
 ((mod m k) : ℕ) = ite (m.val % k.val = 0) k.val (m.val % k.val) :=
begin
  dsimp[mod,mod_div],cases m.val % k.val,
  {rw[if_pos rfl],refl},
  {rw[if_neg n.succ_ne_zero],refl}
end

theorem div_coe (m k : ℕ+) :
 ((div m k) : ℕ) = ite (m.val % k.val = 0) (m.val / k.val).pred (m.val / k.val) :=
begin
  dsimp[div,mod_div],cases m.val % k.val,
  {rw[if_pos rfl],refl},
  {rw[if_neg n.succ_ne_zero],refl}
end

theorem mod_le (m k : ℕ+) : mod m k ≤ m ∧ mod m k ≤ k :=
begin
  change ((mod m k) : ℕ) ≤ m.val ∧ ((mod m k) : ℕ) ≤ k.val,
  rw[mod_coe],split_ifs,
  { have hm : m.val > 0 := m.property,
    rw[← nat.mod_add_div m.val k.val,h,zero_add] at hm ⊢,
    by_cases h' : (m.val / k.val) = 0,
    { rw[h',mul_zero] at hm,exact (lt_irrefl _ hm).elim},
    { let h' := nat.mul_le_mul_left k.val
             (nat.succ_le_of_lt (nat.pos_of_ne_zero h')),
      rw[mul_one] at h',exact ⟨h',le_refl k.val⟩}},
  {exact ⟨nat.mod_le m.val k.val,le_of_lt (nat.mod_lt m.val k.property)⟩}
end

instance : has_dvd ℕ+ := ⟨λ k m, (k : ℕ) ∣ (m : ℕ)⟩

theorem dvd_iff {k m : ℕ+} : k ∣ m ↔ (k : ℕ) ∣ (m : ℕ) := by {refl}

theorem dvd_iff' {k m : ℕ+} : k ∣ m ↔ mod m k = k :=
begin
  change k.val ∣ m.val ↔ mod m k = k,
  rw[nat.dvd_iff_mod_eq_zero],split,
  {intro h,apply eq,rw[mod_coe,if_pos h],refl},
  { intro h,by_cases h' : m.val % k.val = 0,
    { exact h'},
    { replace h : ((mod m k) : ℕ) = (k : ℕ) := congr_arg _ h,
      rw[mod_coe,if_neg h'] at h,
      exact (ne_of_lt (nat.mod_lt m.val k.property) h).elim}}
end

def div_exact {m k : ℕ+} (h : k ∣ m) : ℕ+ :=
 ⟨(div m k).succ,nat.succ_pos _⟩

theorem mul_div_exact {m k : ℕ+} (h : k ∣ m) : k * (div_exact h) = m :=
begin
 apply eq,rw[mul_coe],
 change (k : ℕ) * (div m k).succ = m,
 rw[mod_add_div m k,dvd_iff'.mp h,nat.mul_succ,add_comm],
end

theorem dvd_iff'' {k n : ℕ+} : k ∣ n ↔ ∃ m, k * m = n :=
⟨λ h, ⟨div_exact h,mul_div_exact h⟩,
 λ ⟨m,h⟩, dvd.intro (m : ℕ)
          ((mul_coe k m).symm.trans (congr_arg subtype.val h))⟩

theorem dvd_intro {k n : ℕ+} (m : ℕ+) (h : k * m = n) : k ∣ n :=
 dvd_iff''.mpr ⟨m,h⟩

theorem dvd_refl (m : ℕ+) : m ∣ m := dvd_intro 1 (mul_one m)

theorem dvd_antisymm {m n : ℕ+} : m ∣ n → n ∣ m → m = n :=
λ hmn hnm, subtype.eq (nat.dvd_antisymm hmn hnm)

theorem dvd_trans {k m n : ℕ+} : k ∣ m → m ∣ n → k ∣ n :=
@_root_.dvd_trans ℕ _ k.val m.val n.val

theorem one_dvd (n : ℕ+) : 1 ∣ n := dvd_intro n (one_mul n)

theorem dvd_one_iff (n : ℕ+) : n ∣ 1 ↔ n = 1 :=
 ⟨λ h,dvd_antisymm h (one_dvd n),λ h, h.symm ▸ (dvd_refl 1)⟩

def gcd (n m : ℕ+) : ℕ+ :=
 ⟨nat.gcd n.val m.val,nat.gcd_pos_of_pos_left m.val n.pos⟩

def lcm (n m : ℕ+) : ℕ+ :=
 ⟨nat.lcm n.val m.val,
  by {let h := mul_pos n.property m.property,
      rw[← gcd_mul_lcm n.val m.val,mul_comm] at h,
      exact pos_of_dvd_of_pos (dvd.intro (nat.gcd n.val m.val) rfl) h}⟩

@[simp] theorem gcd_val (n m : ℕ+) : (gcd n m).val = nat.gcd n.val m.val := rfl

@[simp] theorem lcm_val (n m : ℕ+) : (lcm n m).val = nat.lcm n.val m.val := rfl

theorem gcd_dvd_left (n m : ℕ+) : (gcd n m) ∣ n := nat.gcd_dvd_left n.val m.val

theorem gcd_dvd_right (n m : ℕ+) : (gcd n m) ∣ m := nat.gcd_dvd_right n.val m.val

theorem dvd_gcd {m n k : ℕ+} (hm : k ∣ m) (hn : k ∣ n) : k ∣ gcd m n :=
 @nat.dvd_gcd m.val n.val k.val hm hn

theorem dvd_lcm_left  (n m : ℕ+) : n ∣ lcm n m := nat.dvd_lcm_left  n.val m.val

theorem dvd_lcm_right (n m : ℕ+) : m ∣ lcm n m := nat.dvd_lcm_right n.val m.val

theorem lcm_dvd {m n k : ℕ+} (hm : m ∣ k) (hn : n ∣ k) : lcm m n ∣ k :=
 @nat.lcm_dvd m.val n.val k.val hm hn

theorem gcd_mul_lcm (n m : ℕ+) : (gcd n m) * (lcm n m) = n * m :=
 subtype.eq (nat.gcd_mul_lcm n.val m.val)

def prime (p : ℕ+) : Prop := p.val.prime

end pnat

/-- The type of prime numbers
-/
def nat.primes := {p : ℕ // p.prime}

namespace nat.primes

instance : has_repr nat.primes := ⟨λ p,repr p.val⟩

instance coe_nat  : has_coe nat.primes ℕ  := ⟨subtype.val⟩
instance coe_pnat : has_coe nat.primes ℕ+ := ⟨λ p, ⟨p.val,p.property.pos⟩⟩

theorem coe_pnat_nat (p : nat.primes) : ((p : ℕ+) : ℕ) = (p : ℕ) := rfl

theorem coe_nat_inj (p q : nat.primes) : (p : ℕ) = (q : ℕ) → p = q :=
λ h, subtype.eq h

theorem coe_pnat_inj (p q : nat.primes) : (p : ℕ+) = (q : ℕ+) → p = q := λ h,
begin
  replace h : ((p : ℕ+) : ℕ) = ((q : ℕ+) : ℕ) := congr_arg subtype.val h,
  rw[coe_pnat_nat,coe_pnat_nat] at h,
  exact subtype.eq h,
end

end nat.primes

/-- The type of multisets of prime numbers.  Unique factorization
 gives an equivalence between this set and ℕ+, as we will formalize
 below. -/

def prime_multiset := multiset nat.primes

namespace prime_multiset

instance : has_repr prime_multiset :=
by {dsimp[prime_multiset],apply_instance}

instance : canonically_ordered_monoid prime_multiset :=
by {dsimp[prime_multiset],apply_instance}

instance : lattice.distrib_lattice prime_multiset :=
by {dsimp[prime_multiset],apply_instance}

instance : lattice.semilattice_sup_bot prime_multiset :=
by {dsimp[prime_multiset],apply_instance}

instance : has_sub prime_multiset :=
by {dsimp[prime_multiset],apply_instance}

theorem add_sub_of_le {u v : prime_multiset} : u ≤ v → u + (v - u) = v :=
multiset.add_sub_of_le

/-- The multiset consisting of a single prime
-/
def of_prime (p : nat.primes) : prime_multiset := (p :: 0)

theorem card_of_prime (p : nat.primes) : multiset.card (of_prime p) = 1 := rfl

/-- We can forget the primality property and regard a multiset
 of primes as just a multiset of positive integers, or a multiset
 of natural numbers.  In the opposite direction, if we have a
 multiset of positive integers or natural numbers, together with
 a proof that all the elements are prime, then we can regard it
 as a multiset of primes.  The next block of results records
 obvious properties of these coercions.
-/

def to_nat_multiset : prime_multiset → multiset ℕ :=
λ v, v.map (λ p, (p : ℕ))

instance coe_nat : has_coe prime_multiset (multiset ℕ) := ⟨to_nat_multiset⟩

instance coe_nat_hom : is_add_monoid_hom (coe : prime_multiset → multiset ℕ) :=
by {unfold_coes,dsimp[to_nat_multiset],apply_instance}

theorem coe_nat_inj : function.injective (coe : prime_multiset → multiset ℕ) :=
multiset.injective_map nat.primes.coe_nat_inj

theorem coe_nat_of_prime (p : nat.primes) :
((of_prime p) : multiset ℕ) = (p : ℕ) :: 0 := rfl

theorem coe_nat_prime (v : prime_multiset)
(p : ℕ) (h : p ∈ (v : multiset ℕ)) : p.prime :=
by {rcases multiset.mem_map.mp h with ⟨⟨p',hp'⟩,⟨h_mem,h_eq⟩⟩,exact h_eq ▸ hp'}

def to_pnat_multiset : prime_multiset → multiset ℕ+ :=
λ v, v.map (λ p, (p : ℕ+))

instance coe_pnat : has_coe prime_multiset (multiset ℕ+) := ⟨to_pnat_multiset⟩

instance coe_pnat_hom : is_add_monoid_hom (coe : prime_multiset → multiset ℕ+) :=
by {unfold_coes,dsimp[to_pnat_multiset],apply_instance}

theorem coe_pnat_inj : function.injective (coe : prime_multiset → multiset ℕ+) :=
multiset.injective_map nat.primes.coe_pnat_inj

theorem coe_pnat_of_prime (p : nat.primes) :
((of_prime p) : multiset ℕ+) = (p : ℕ+) :: 0 := rfl

theorem coe_pnat_prime (v : prime_multiset)
 (p : ℕ+) (h : p ∈ (v : multiset ℕ+)) : p.prime :=
by {rcases multiset.mem_map.mp h with ⟨⟨p',hp'⟩,⟨h_mem,h_eq⟩⟩, exact h_eq ▸ hp'}

instance coe_multiset_pnat_nat : has_coe (multiset ℕ+) (multiset ℕ) :=
⟨λ v, v.map (λ n,(n : ℕ))⟩

theorem coe_pnat_nat (v : prime_multiset) :
 ((v : (multiset ℕ+)) : (multiset ℕ)) = (v : multiset ℕ) :=
by {change (v.map (coe : nat.primes → ℕ+)).map subtype.val = v.map subtype.val,
  rw[multiset.map_map],congr,}

def prod (v : prime_multiset) : ℕ+ := (v : multiset pnat).prod

theorem coe_prod (v : prime_multiset) : (v.prod : ℕ) = (v : multiset ℕ).prod :=
begin
  let h : (v.prod : ℕ) = ((v.map coe).map coe).prod :=
  (multiset.prod_hom coe v.to_pnat_multiset).symm,
  rw[multiset.map_map] at h,
  have : (coe : ℕ+ → ℕ) ∘ (coe : nat.primes → ℕ+) = coe := funext (λ p, rfl),
  rw[this] at h, exact h,
end

theorem prod_of_prime (p : nat.primes) : (of_prime p).prod = (p : ℕ+) :=
 by { change multiset.prod ((p : ℕ+) :: 0) = (p : ℕ+),
  rw[multiset.prod_cons,multiset.prod_zero,mul_one]}

def of_nat_multiset
 (v : multiset ℕ) (h : ∀ (p : ℕ), p ∈ v → p.prime) : prime_multiset :=
 @multiset.pmap ℕ nat.primes nat.prime (λ p hp,⟨p,hp⟩) v h

theorem to_of_nat_multiset (v : multiset ℕ) (h) :
 ((of_nat_multiset v h) : multiset ℕ) = v :=
begin
  unfold_coes,dsimp[of_nat_multiset,to_nat_multiset],
  have : (λ (p : ℕ) (h : p.prime), ((⟨p,h⟩ : nat.primes) : ℕ)) = (λ p h, id p) :=
    by {funext p h,refl},
  rw[multiset.map_pmap,this,multiset.pmap_eq_map,multiset.map_id],
end

theorem prod_of_nat_multiset (v : multiset ℕ) (h) :
 ((of_nat_multiset v h).prod : ℕ) = (v.prod : ℕ) :=
by {rw[coe_prod,to_of_nat_multiset]}

def of_pnat_multiset
 (v : multiset ℕ+) (h : ∀ (p : ℕ+), p ∈ v → p.prime) : prime_multiset :=
@multiset.pmap ℕ+ nat.primes pnat.prime (λ p hp,⟨(p : ℕ),hp⟩) v h

theorem to_of_pnat_multiset (v : multiset ℕ+) (h) :
 ((of_pnat_multiset v h) : multiset ℕ+) = v :=
begin
  unfold_coes,dsimp[of_pnat_multiset,to_pnat_multiset],
  have : (λ (p : ℕ+) (h : p.prime), ((coe : nat.primes → ℕ+) ⟨p,h⟩)) = (λ p h, id p) :=
    by {funext p h,apply subtype.eq,refl},
  rw[multiset.map_pmap,this,multiset.pmap_eq_map,multiset.map_id],
end

theorem prod_of_pnat_multiset (v : multiset ℕ+) (h) :
 ((of_pnat_multiset v h).prod : ℕ+) = v.prod :=
by {dsimp[prod],rw[to_of_pnat_multiset]}

/-- Lists can be coerced to multisets; here we have some results
 about how this interacts with our constructions on multisets.
-/
def of_nat_list (l : list ℕ) (h : ∀ (p : ℕ), p ∈ l → p.prime) : prime_multiset :=
of_nat_multiset (l : multiset ℕ) h

theorem prod_of_nat_list (l : list ℕ) (h) : ((of_nat_list l h).prod : ℕ) = l.prod :=
by {have := prod_of_nat_multiset (l : multiset ℕ) h,
    rw[multiset.coe_prod] at this, exact this}

def of_pnat_list (l : list ℕ+) (h : ∀ (p : ℕ+), p ∈ l → p.prime) : prime_multiset :=
of_pnat_multiset (l : multiset ℕ+) h

theorem prod_of_pnat_list (l : list ℕ+) (h) : (of_pnat_list l h).prod = l.prod :=
by {have := prod_of_pnat_multiset (l : multiset ℕ+) h,
    rw[multiset.coe_prod] at this, exact this}

/-- The product map gives a homomorphism from the additive monoid
 of multisets to the multiplicative monoid ℕ+.
-/

theorem prod_zero : (0 : prime_multiset).prod = 1 :=
by {dsimp[prod],exact multiset.prod_zero}

theorem prod_add (u v : prime_multiset) : (u + v).prod = u.prod * v.prod :=
by { dsimp[prod],
     rw[is_add_monoid_hom.map_add (coe : prime_multiset → multiset ℕ+)],
     rw[multiset.prod_add]}

theorem prod_smul (d : ℕ) (u : prime_multiset) :
 (add_monoid.smul d u).prod = u.prod ^ d :=
by { induction d with d ih,refl,
     rw[succ_smul,prod_add,ih,nat.succ_eq_add_one,pnat.pow_succ,mul_comm],}

end prime_multiset

namespace pnat

/-- The prime factors of n, regarded as a multiset -/
def factor_multiset (n : ℕ+) : prime_multiset :=
prime_multiset.of_nat_list (nat.factors n) (@nat.mem_factors n)

/-- The product of the factors is the original number -/
theorem prod_factor_multiset (n : ℕ+) : (factor_multiset n).prod = n :=
eq $ by {dsimp[factor_multiset],rw[prime_multiset.prod_of_nat_list],
          exact nat.prod_factors n.pos,}

theorem coe_nat_factor_multiset (n : ℕ+) :
 ((factor_multiset n) : (multiset ℕ)) = ((nat.factors n) : multiset ℕ) :=
prime_multiset.to_of_nat_multiset (nat.factors n) (@nat.mem_factors n)

end pnat

namespace prime_multiset

/-- If we start with a multiset of primes, take the product and
 then factor it, we get back the original multiset. -/
theorem factor_multiset_prod (v : prime_multiset) :
 v.prod.factor_multiset = v :=
begin
  apply prime_multiset.coe_nat_inj,
  rw[v.prod.coe_nat_factor_multiset,prime_multiset.coe_prod],
  rcases v with l,unfold_coes,dsimp[prime_multiset.to_nat_multiset],
  rw[multiset.coe_prod],
  let l' := l.map (coe : nat.primes → ℕ),
  have : ∀ (p : ℕ), p ∈ l' → p.prime :=
    λ p hp, by {rcases list.mem_map.mp hp with ⟨⟨p',hp'⟩,⟨h_mem,h_eq⟩⟩,
                exact h_eq ▸ hp'},
  exact multiset.coe_eq_coe.mpr (@nat.factors_unique _ l' rfl this).symm,
end

end prime_multiset

namespace pnat

/-- Positive integers biject with multisets of primes. -/
def factor_multiset_equiv : ℕ+ ≃ prime_multiset := {
  to_fun    := factor_multiset,
  inv_fun   := prime_multiset.prod,
  left_inv  := prod_factor_multiset,
  right_inv := prime_multiset.factor_multiset_prod
}

/-- Factoring gives a homomorphism from the multiplicative
 monoid ℕ+ to the additive monoid of multisets. -/
theorem factor_multiset_one : factor_multiset 1 = 0 := rfl

theorem factor_multiset_mul (n m : ℕ+) :
  factor_multiset (n * m) = (factor_multiset n) + (factor_multiset m) :=
begin
  let u := factor_multiset n,
  let v := factor_multiset m,
  have : n = u.prod := (prod_factor_multiset n).symm, rw[this],
  have : m = v.prod := (prod_factor_multiset m).symm, rw[this],
  rw[← prime_multiset.prod_add],
  repeat {rw[prime_multiset.factor_multiset_prod]},
end

theorem factor_multiset_pow (n : ℕ+) (m : ℕ) :
 factor_multiset (n ^ m) = add_monoid.smul m (factor_multiset n) :=
begin
  let u := factor_multiset n,
  have : n = u.prod := (prod_factor_multiset n).symm,
  rw[this,← prime_multiset.prod_smul],
  repeat {rw[prime_multiset.factor_multiset_prod]},
end

/-- Factoring a prime gives the corresponding one-element multiset. -/
theorem factor_multiset_of_prime (p : nat.primes) :
 (p : ℕ+).factor_multiset = prime_multiset.of_prime p :=
begin
  apply factor_multiset_equiv.symm.injective,
  change (p : ℕ+).factor_multiset.prod = (prime_multiset.of_prime p).prod,
  rw[(p : ℕ+).prod_factor_multiset,prime_multiset.prod_of_prime],
end

/-- We now have four different results that all encode the
 idea that inequality of multisets corresponds to divisibility
 of positive integers. -/
theorem factor_multiset_le_iff {m n : ℕ+} :
  factor_multiset m ≤ factor_multiset n ↔ m ∣ n :=
begin
  split,
  { intro h,rw[← prod_factor_multiset m,← prod_factor_multiset m],
    apply dvd_intro (n.factor_multiset - m.factor_multiset).prod,
    rw[← prime_multiset.prod_add,prime_multiset.factor_multiset_prod,
       prime_multiset.add_sub_of_le h,prod_factor_multiset]},
  { intro  h,rw[← mul_div_exact h,factor_multiset_mul],
    exact le_add_right (le_refl _)}
end

theorem factor_multiset_le_iff' {m : ℕ+} {v : prime_multiset}:
 factor_multiset m ≤ v ↔ m ∣ v.prod :=
by { let h := @factor_multiset_le_iff m v.prod,
     rw[v.factor_multiset_prod] at h,exact h,}

end pnat

namespace prime_multiset

theorem prod_dvd_iff {u v : prime_multiset} : u.prod ∣ v.prod ↔ u ≤ v :=
by { let h := @pnat.factor_multiset_le_iff' u.prod v,
     rw[u.factor_multiset_prod] at h, exact h.symm}

theorem prod_dvd_iff' {u : prime_multiset} {n : ℕ+} : u.prod ∣ n ↔ u ≤ n.factor_multiset :=
 by {let h := @prod_dvd_iff u n.factor_multiset,
     rw[n.prod_factor_multiset] at h, exact h}

end prime_multiset

namespace pnat

/-- The gcd and lcm operations on positive integers correspond
 to the inf and sup operations on multisets.
-/
theorem factor_multiset_gcd (m n : ℕ+) :
 factor_multiset (gcd m n) = (factor_multiset m) ⊓ (factor_multiset n) :=
begin
  apply le_antisymm,
  { apply lattice.le_inf_iff.mpr; split; apply factor_multiset_le_iff.mpr,
    exact gcd_dvd_left m n, exact gcd_dvd_right m n},
  { rw[← prime_multiset.prod_dvd_iff,prod_factor_multiset],
    apply dvd_gcd; rw[prime_multiset.prod_dvd_iff'],
    exact lattice.inf_le_left, exact lattice.inf_le_right,}
end

theorem factor_multiset_lcm (m n : ℕ+) :
 factor_multiset (lcm m n) = (factor_multiset m) ⊔ (factor_multiset n) :=
begin
  apply le_antisymm,
  { rw[← prime_multiset.prod_dvd_iff,prod_factor_multiset],
    apply lcm_dvd; rw[← factor_multiset_le_iff'],
    exact lattice.le_sup_left, exact lattice.le_sup_right,},
  { apply lattice.sup_le_iff.mpr; split; apply factor_multiset_le_iff.mpr,
    exact dvd_lcm_left m n, exact dvd_lcm_right m n},
end

/-- The number of occurrences of p in the factor multiset of m
 is the same as the p-adic valuation of m. -/
theorem count_factor_multiset (m : ℕ+) (p : nat.primes) (k : ℕ) :
 (p : ℕ+) ^ k ∣ m ↔ k ≤ m.factor_multiset.count p :=
begin
  intros,rw[multiset.le_count_iff_repeat_le],
  rw[← factor_multiset_le_iff,factor_multiset_pow,factor_multiset_of_prime],
  congr' 2,
  apply multiset.eq_repeat.mpr,split,
  {rw[multiset.card_smul,prime_multiset.card_of_prime,mul_one]},
  { have : ∀ (m : ℕ), add_monoid.smul m (p::0) = multiset.repeat p m :=
    λ m, by {induction m with m ih,refl,rw[succ_smul,multiset.repeat_succ,ih],
     rw[multiset.cons_add,zero_add]},
    intros q h, rw[prime_multiset.of_prime,this k] at h,
    exact multiset.eq_of_mem_repeat h,
  }
end

end pnat

namespace prime_multiset

theorem prod_inf (u v : prime_multiset) :
 (u ⊓ v).prod = pnat.gcd u.prod v.prod :=
begin
  let n := u.prod,
  let m := v.prod,
  change (u ⊓ v).prod = pnat.gcd n m,
  have : u = n.factor_multiset := u.factor_multiset_prod.symm, rw[this],
  have : v = m.factor_multiset := v.factor_multiset_prod.symm, rw[this],
  rw[← pnat.factor_multiset_gcd n m,pnat.prod_factor_multiset],
end

theorem prod_sup (u v : prime_multiset) :
 (u ⊔ v).prod = pnat.lcm u.prod v.prod :=
begin
  let n := u.prod,
  let m := v.prod,
  change (u ⊔ v).prod = pnat.lcm n m,
  have : u = n.factor_multiset := u.factor_multiset_prod.symm, rw[this],
  have : v = m.factor_multiset := v.factor_multiset_prod.symm, rw[this],
  rw[← pnat.factor_multiset_lcm n m,pnat.prod_factor_multiset],
end

end prime_multiset
