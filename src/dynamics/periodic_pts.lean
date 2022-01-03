/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import data.nat.prime
import dynamics.fixed_points.basic
import data.pnat.basic
import data.set.lattice

/-!
# Periodic points

A point `x : α` is a periodic point of `f : α → α` of period `n` if `f^[n] x = x`.

## Main definitions

* `is_periodic_pt f n x` : `x` is a periodic point of `f` of period `n`, i.e. `f^[n] x = x`.
  We do not require `n > 0` in the definition.
* `pts_of_period f n` : the set `{x | is_periodic_pt f n x}`. Note that `n` is not required to
  be the minimal period of `x`.
* `periodic_pts f` : the set of all periodic points of `f`.
* `minimal_period f x` : the minimal period of a point `x` under an endomorphism `f` or zero
  if `x` is not a periodic point of `f`.

## Main statements

We provide “dot syntax”-style operations on terms of the form `h : is_periodic_pt f n x` including
arithmetic operations on `n` and `h.map (hg : semiconj_by g f f')`. We also prove that `f`
is bijective on each set `pts_of_period f n` and on `periodic_pts f`. Finally, we prove that `x`
is a periodic point of `f` of period `n` if and only if `minimal_period f x | n`.

## References

* https://en.wikipedia.org/wiki/Periodic_point

-/

open set

namespace function

variables {α : Type*} {β : Type*} {f fa : α → α} {fb : β → β} {x y : α} {m n : ℕ}

/-- A point `x` is a periodic point of `f : α → α` of period `n` if `f^[n] x = x`.
Note that we do not require `0 < n` in this definition. Many theorems about periodic points
need this assumption. -/
def is_periodic_pt (f : α → α) (n : ℕ) (x : α) := is_fixed_pt (f^[n]) x

/-- A fixed point of `f` is a periodic point of `f` of any prescribed period. -/
lemma is_fixed_pt.is_periodic_pt (hf : is_fixed_pt f x) (n : ℕ) : is_periodic_pt f n x :=
hf.iterate n

/-- For the identity map, all points are periodic. -/
lemma is_periodic_id (n : ℕ) (x : α) : is_periodic_pt id n x := (is_fixed_pt_id x).is_periodic_pt n

/-- Any point is a periodic point of period `0`. -/
lemma is_periodic_pt_zero (f : α → α) (x : α) : is_periodic_pt f 0 x := is_fixed_pt_id x

namespace is_periodic_pt

instance [decidable_eq α] {f : α → α} {n : ℕ} {x : α} : decidable (is_periodic_pt f n x) :=
is_fixed_pt.decidable

protected lemma is_fixed_pt (hf : is_periodic_pt f n x) : is_fixed_pt (f^[n]) x := hf

protected lemma map (hx : is_periodic_pt fa n x) {g : α → β} (hg : semiconj g fa fb) :
  is_periodic_pt fb n (g x) :=
hx.map (hg.iterate_right n)

lemma apply_iterate (hx : is_periodic_pt f n x) (m : ℕ) : is_periodic_pt f n (f^[m] x) :=
hx.map $ commute.iterate_self f m

protected lemma apply (hx : is_periodic_pt f n x) : is_periodic_pt f n (f x) :=
hx.apply_iterate 1

protected lemma add (hn : is_periodic_pt f n x) (hm : is_periodic_pt f m x) :
  is_periodic_pt f (n + m) x :=
by { rw [is_periodic_pt, iterate_add], exact hn.comp hm }

lemma left_of_add (hn : is_periodic_pt f (n + m) x) (hm : is_periodic_pt f m x) :
  is_periodic_pt f n x :=
by { rw [is_periodic_pt, iterate_add] at hn, exact hn.left_of_comp hm }

lemma right_of_add (hn : is_periodic_pt f (n + m) x) (hm : is_periodic_pt f n x) :
  is_periodic_pt f m x :=
by { rw add_comm at hn, exact hn.left_of_add hm }

protected lemma sub (hm : is_periodic_pt f m x) (hn : is_periodic_pt f n x) :
  is_periodic_pt f (m - n) x :=
begin
  cases le_total n m with h h,
  { refine left_of_add _ hn,
    rwa [tsub_add_cancel_of_le h] },
  { rw [tsub_eq_zero_iff_le.mpr h],
    apply is_periodic_pt_zero }
end

protected lemma mul_const (hm : is_periodic_pt f m x) (n : ℕ) : is_periodic_pt f (m * n) x :=
by simp only [is_periodic_pt, iterate_mul, hm.is_fixed_pt.iterate n]

protected lemma const_mul (hm : is_periodic_pt f m x) (n : ℕ) : is_periodic_pt f (n * m) x :=
by simp only [mul_comm n, hm.mul_const n]

lemma trans_dvd (hm : is_periodic_pt f m x) {n : ℕ} (hn : m ∣ n) : is_periodic_pt f n x :=
let ⟨k, hk⟩ := hn in hk.symm ▸ hm.mul_const k

protected lemma iterate (hf : is_periodic_pt f n x) (m : ℕ) : is_periodic_pt (f^[m]) n x :=
begin
  rw [is_periodic_pt, ← iterate_mul, mul_comm, iterate_mul],
  exact hf.is_fixed_pt.iterate m
end

lemma comp {g : α → α} (hco : commute f g) (hf : is_periodic_pt f n x) (hg : is_periodic_pt g n x) :
  is_periodic_pt (f ∘ g) n x :=
by { rw [is_periodic_pt, hco.comp_iterate], exact hf.comp hg }

lemma comp_lcm {g : α → α} (hco : commute f g) (hf : is_periodic_pt f m x)
  (hg : is_periodic_pt g n x) :
  is_periodic_pt (f ∘ g) (nat.lcm m n) x :=
(hf.trans_dvd $ nat.dvd_lcm_left _ _).comp hco (hg.trans_dvd $ nat.dvd_lcm_right _ _)

lemma left_of_comp {g : α → α} (hco : commute f g) (hfg : is_periodic_pt (f ∘ g) n x)
  (hg : is_periodic_pt g n x) : is_periodic_pt f n x :=
begin
  rw [is_periodic_pt, hco.comp_iterate] at hfg,
  exact hfg.left_of_comp hg
end

lemma iterate_mod_apply (h : is_periodic_pt f n x) (m : ℕ) :
  f^[m % n] x = (f^[m] x) :=
by conv_rhs { rw [← nat.mod_add_div m n, iterate_add_apply, (h.mul_const _).eq] }

protected lemma mod (hm : is_periodic_pt f m x) (hn : is_periodic_pt f n x) :
  is_periodic_pt f (m % n) x :=
(hn.iterate_mod_apply m).trans hm

protected lemma gcd (hm : is_periodic_pt f m x) (hn : is_periodic_pt f n x) :
  is_periodic_pt f (m.gcd n) x :=
begin
  revert hm hn,
  refine nat.gcd.induction m n (λ n h0 hn, _) (λ m n hm ih hm hn, _),
  { rwa [nat.gcd_zero_left], },
  { rw [nat.gcd_rec],
    exact ih (hn.mod hm) hm }
end

/-- If `f` sends two periodic points `x` and `y` of the same positive period to the same point,
then `x = y`. For a similar statement about points of different periods see `eq_of_apply_eq`. -/
lemma eq_of_apply_eq_same (hx : is_periodic_pt f n x) (hy : is_periodic_pt f n y) (hn : 0 < n)
  (h : f x = f y) :
  x = y :=
by rw [← hx.eq, ← hy.eq, ← iterate_pred_comp_of_pos f hn, comp_app, h]

/-- If `f` sends two periodic points `x` and `y` of positive periods to the same point,
then `x = y`. -/
lemma eq_of_apply_eq (hx : is_periodic_pt f m x) (hy : is_periodic_pt f n y) (hm : 0 < m)
  (hn : 0 < n) (h : f x = f y) :
  x = y :=
(hx.mul_const n).eq_of_apply_eq_same (hy.const_mul m) (mul_pos hm hn) h

end is_periodic_pt

/-- The set of periodic points of a given (possibly non-minimal) period. -/
def pts_of_period (f : α → α) (n : ℕ) : set α := {x : α | is_periodic_pt f n x}

@[simp] lemma mem_pts_of_period : x ∈ pts_of_period f n ↔ is_periodic_pt f n x :=
iff.rfl

lemma semiconj.maps_to_pts_of_period {g : α → β} (h : semiconj g fa fb) (n : ℕ) :
  maps_to g (pts_of_period fa n) (pts_of_period fb n) :=
(h.iterate_right n).maps_to_fixed_pts

lemma bij_on_pts_of_period (f : α → α) {n : ℕ} (hn : 0 < n) :
  bij_on f (pts_of_period f n) (pts_of_period f n) :=
⟨(commute.refl f).maps_to_pts_of_period n,
  λ x hx y hy hxy, hx.eq_of_apply_eq_same hy hn hxy,
  λ x hx, ⟨f^[n.pred] x, hx.apply_iterate _,
    by rw [← comp_app f, comp_iterate_pred_of_pos f hn, hx.eq]⟩⟩

lemma directed_pts_of_period_pnat (f : α → α) : directed (⊆) (λ n : ℕ+, pts_of_period f n) :=
λ m n, ⟨m * n, λ x hx, hx.mul_const n, λ x hx, hx.const_mul m⟩

/-- The set of periodic points of a map `f : α → α`. -/
def periodic_pts (f : α → α) : set α := {x : α | ∃ n > 0, is_periodic_pt f n x}

lemma mk_mem_periodic_pts (hn : 0 < n) (hx : is_periodic_pt f n x) :
  x ∈ periodic_pts f :=
⟨n, hn, hx⟩

lemma mem_periodic_pts : x ∈ periodic_pts f ↔ ∃ n > 0, is_periodic_pt f n x := iff.rfl

variable (f)

lemma bUnion_pts_of_period : (⋃ n > 0, pts_of_period f n) = periodic_pts f :=
set.ext $ λ x, by simp [mem_periodic_pts]

lemma Union_pnat_pts_of_period : (⋃ n : ℕ+, pts_of_period f n) = periodic_pts f :=
supr_subtype.trans $ bUnion_pts_of_period f

lemma bij_on_periodic_pts : bij_on f (periodic_pts f) (periodic_pts f) :=
Union_pnat_pts_of_period f ▸
  bij_on_Union_of_directed (directed_pts_of_period_pnat f) (λ i, bij_on_pts_of_period f i.pos)

variable {f}

lemma semiconj.maps_to_periodic_pts {g : α → β} (h : semiconj g fa fb) :
  maps_to g (periodic_pts fa) (periodic_pts fb) :=
λ x ⟨n, hn, hx⟩, ⟨n, hn, hx.map h⟩

open_locale classical

noncomputable theory

/-- Minimal period of a point `x` under an endomorphism `f`. If `x` is not a periodic point of `f`,
then `minimal_period f x = 0`. -/
def minimal_period (f : α → α) (x : α) :=
if h : x ∈ periodic_pts f then nat.find h else 0

lemma is_periodic_pt_minimal_period (f : α → α) (x : α) :
  is_periodic_pt f (minimal_period f x) x :=
begin
  delta minimal_period,
  split_ifs with hx,
  { exact (nat.find_spec hx).snd },
  { exact is_periodic_pt_zero f x }
end

lemma iterate_eq_mod_minimal_period : f^[n] x = (f^[n % minimal_period f x] x) :=
((is_periodic_pt_minimal_period f x).iterate_mod_apply n).symm

lemma minimal_period_pos_of_mem_periodic_pts (hx : x ∈ periodic_pts f) :
  0 < minimal_period f x :=
by simp only [minimal_period, dif_pos hx, (nat.find_spec hx).fst.lt]

lemma is_periodic_pt.minimal_period_pos (hn : 0 < n) (hx : is_periodic_pt f n x) :
  0 < minimal_period f x :=
minimal_period_pos_of_mem_periodic_pts $ mk_mem_periodic_pts hn hx

lemma minimal_period_pos_iff_mem_periodic_pts :
  0 < minimal_period f x ↔ x ∈ periodic_pts f :=
⟨not_imp_not.1 $ λ h,
  by simp only [minimal_period, dif_neg h, lt_irrefl 0, not_false_iff],
  minimal_period_pos_of_mem_periodic_pts⟩

lemma is_periodic_pt.minimal_period_le (hn : 0 < n) (hx : is_periodic_pt f n x) :
  minimal_period f x ≤ n :=
begin
  rw [minimal_period, dif_pos (mk_mem_periodic_pts hn hx)],
  exact nat.find_min' (mk_mem_periodic_pts hn hx) ⟨hn, hx⟩
end

lemma minimal_period_id : minimal_period id x = 1 :=
((is_periodic_id _ _ ).minimal_period_le nat.one_pos).antisymm
  (nat.succ_le_of_lt ((is_periodic_id _ _ ).minimal_period_pos nat.one_pos))

lemma is_fixed_point_iff_minimal_period_eq_one : minimal_period f x = 1 ↔ is_fixed_pt f x :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw ← iterate_one f,
    refine function.is_periodic_pt.is_fixed_pt _,
    rw ← h,
    exact is_periodic_pt_minimal_period f x },
  { exact ((h.is_periodic_pt 1).minimal_period_le nat.one_pos).antisymm
      (nat.succ_le_of_lt ((h.is_periodic_pt 1).minimal_period_pos nat.one_pos)) }
end

lemma is_periodic_pt.eq_zero_of_lt_minimal_period (hx : is_periodic_pt f n x)
  (hn : n < minimal_period f x) :
  n = 0 :=
eq.symm $ (eq_or_lt_of_le $ n.zero_le).resolve_right $ λ hn0,
not_lt.2 (hx.minimal_period_le hn0) hn

lemma not_is_periodic_pt_of_pos_of_lt_minimal_period :
  ∀ {n: ℕ} (n0 : n ≠ 0) (hn : n < minimal_period f x), ¬ is_periodic_pt f n x
| 0 n0 _ := (n0 rfl).elim
| (n + 1) _ hn := λ hp, nat.succ_ne_zero _ (hp.eq_zero_of_lt_minimal_period hn)

lemma is_periodic_pt.minimal_period_dvd (hx : is_periodic_pt f n x) :
  minimal_period f x ∣ n :=
(eq_or_lt_of_le $ n.zero_le).elim (λ hn0, hn0 ▸ dvd_zero _) $ λ hn0,
(nat.dvd_iff_mod_eq_zero _ _).2 $
(hx.mod $ is_periodic_pt_minimal_period f x).eq_zero_of_lt_minimal_period $
nat.mod_lt _ $ hx.minimal_period_pos hn0

lemma is_periodic_pt_iff_minimal_period_dvd :
  is_periodic_pt f n x ↔ minimal_period f x ∣ n :=
⟨is_periodic_pt.minimal_period_dvd, λ h, (is_periodic_pt_minimal_period f x).trans_dvd h⟩

open nat

lemma minimal_period_eq_minimal_period_iff {g : β → β} {y : β} :
  minimal_period f x = minimal_period g y ↔ ∀ n, is_periodic_pt f n x ↔ is_periodic_pt g n y :=
by simp_rw [is_periodic_pt_iff_minimal_period_dvd, dvd_right_iff_eq]

lemma minimal_period_eq_prime {p : ℕ} [hp : fact p.prime] (hper : is_periodic_pt f p x)
  (hfix : ¬ is_fixed_pt f x) : minimal_period f x = p :=
(hp.out.eq_one_or_self_of_dvd _ (hper.minimal_period_dvd)).resolve_left
  (mt is_fixed_point_iff_minimal_period_eq_one.1 hfix)

lemma minimal_period_eq_prime_pow {p k : ℕ} [hp : fact p.prime] (hk : ¬ is_periodic_pt f (p ^ k) x)
(hk1 : is_periodic_pt f (p ^ (k + 1)) x) : minimal_period f x = p ^ (k + 1) :=
begin
  apply nat.eq_prime_pow_of_dvd_least_prime_pow hp.out;
  rwa ← is_periodic_pt_iff_minimal_period_dvd
end

lemma commute.minimal_period_of_comp_dvd_lcm {g : α → α} (h : function.commute f g) :
  minimal_period (f ∘ g) x ∣ nat.lcm (minimal_period f x) (minimal_period g x) :=
begin
  rw [← is_periodic_pt_iff_minimal_period_dvd],
  exact (is_periodic_pt_minimal_period f x).comp_lcm h (is_periodic_pt_minimal_period g x)
end

lemma commute.minimal_period_of_comp_dvd_mul {g : α → α} (h : function.commute f g) :
  minimal_period (f ∘ g) x ∣ (minimal_period f x) * (minimal_period g x) :=
dvd_trans h.minimal_period_of_comp_dvd_lcm (lcm_dvd_mul _ _)

lemma commute.minimal_period_of_comp_eq_mul_of_coprime {g : α → α} (h : function.commute f g)
  (hco : coprime (minimal_period f x) (minimal_period g x)) :
  minimal_period (f ∘ g) x = (minimal_period f x) * (minimal_period g x) :=
begin
  apply dvd_antisymm (h.minimal_period_of_comp_dvd_mul),
  suffices : ∀ {f g : α → α}, commute f g → coprime (minimal_period f x) (minimal_period g x) →
    minimal_period f x ∣ minimal_period (f ∘ g) x,
    from hco.mul_dvd_of_dvd_of_dvd (this h hco) (h.comp_eq.symm ▸ this h.symm hco.symm),
  clear hco h f g,
  intros f g h hco,
  refine hco.dvd_of_dvd_mul_left (is_periodic_pt.left_of_comp h _ _).minimal_period_dvd,
  { exact (is_periodic_pt_minimal_period _ _).const_mul _ },
  { exact (is_periodic_pt_minimal_period _ _).mul_const _ }
end

private lemma minimal_period_iterate_eq_div_gcd_aux (h : 0 < gcd (minimal_period f x) n) :
  minimal_period (f ^[n]) x = minimal_period f x / nat.gcd (minimal_period f x) n :=
begin
  apply nat.dvd_antisymm,
  { apply is_periodic_pt.minimal_period_dvd,
    rw [is_periodic_pt, is_fixed_pt, ← iterate_mul, ← nat.mul_div_assoc _ (gcd_dvd_left _ _),
        mul_comm, nat.mul_div_assoc _ (gcd_dvd_right _ _), mul_comm, iterate_mul],
    exact (is_periodic_pt_minimal_period f x).iterate _ },
  { apply coprime.dvd_of_dvd_mul_right (coprime_div_gcd_div_gcd h),
    apply dvd_of_mul_dvd_mul_right h,
    rw [nat.div_mul_cancel (gcd_dvd_left _ _), mul_assoc, nat.div_mul_cancel (gcd_dvd_right _ _),
        mul_comm],
    apply is_periodic_pt.minimal_period_dvd,
    rw [is_periodic_pt, is_fixed_pt, iterate_mul],
    exact is_periodic_pt_minimal_period _ _ }
end

lemma minimal_period_iterate_eq_div_gcd (h : n ≠ 0) :
  minimal_period (f ^[n]) x = minimal_period f x / nat.gcd (minimal_period f x) n :=
minimal_period_iterate_eq_div_gcd_aux $ gcd_pos_of_pos_right _ (nat.pos_of_ne_zero h)

lemma minimal_period_iterate_eq_div_gcd' (h : x ∈ periodic_pts f) :
  minimal_period (f ^[n]) x = minimal_period f x / nat.gcd (minimal_period f x) n :=
minimal_period_iterate_eq_div_gcd_aux $
  gcd_pos_of_pos_left n (minimal_period_pos_iff_mem_periodic_pts.mpr h)

end function
