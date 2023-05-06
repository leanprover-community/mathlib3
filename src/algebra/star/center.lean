import algebra.star.basic
import group_theory.subsemigroup.center
import group_theory.subsemigroup.centralizer
import algebra.star.pointwise

variables {R : Type*} [semigroup R] [star_semigroup R] {a : R} {s : set R}

lemma set.star_mem_center (ha : a ∈ set.center R) : star a ∈ set.center R :=
by simpa only [star_mul, star_star] using
  λ g, congr_arg star ((set.mem_center_iff R).mp ha $ star g).symm

lemma set.star_mem_centralizer' (h : ∀ (a : R), a ∈ s → star a ∈ s)
  (ha : a ∈ set.centralizer s) : star a ∈ set.centralizer s :=
λ y hy, by simpa using congr_arg star (ha _ (h _ hy)).symm

open_locale pointwise

lemma set.star_mem_centralizer (ha : a ∈ set.centralizer (s ∪ star s)) :
  star a ∈ set.centralizer (s ∪ star s) :=
set.star_mem_centralizer' (λ x hx, hx.elim (λ hx, or.inr $ set.star_mem_star.mpr hx) or.inl) ha
