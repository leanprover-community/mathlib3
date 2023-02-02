import taoziegler.page1
import measure_theory.measure.measure_space
import analysis.asymptotics.asymptotics
import data.complex.exponential
import taoziegler.tomathlib.multiset

open_locale topology ennreal measure_theory
open filter asymptotics
open_locale topology

open measure_theory

-- variables (μ ν : measure ℕ)

/-- There exists a natural number `H` such that there are infinitely many pairs of distinct
`p, q ∈ s` such that `|p - q| ≤ H` .-/
def bounded_gaps (s : set ℕ) : Prop := ∃ (H : ℕ), set.infinite
  {pq : ℕ × ℕ | pq.1 ≠ pq.2 ∧ pq.1 ∈ s ∧ pq.2 ∈ s ∧ max (pq.1 - pq.2) (pq.2 - pq.1) ≤ H}

lemma bounded_gaps_iff {s : set ℕ} : bounded_gaps s ↔ ∃ (H : ℕ), set.infinite
  {pq : ℕ × ℕ | pq.1 ≠ pq.2 ∧ pq.1 ∈ s ∧ pq.2 ∈ s ∧ max (pq.1 - pq.2) (pq.2 - pq.1) ≤ H} := iff.rfl

-- Remark 1.4
lemma bounded_gaps_of_infinite_subset_mem_add_mem_succ
  (A : set ℕ) (B : set ℕ) (hB : B.infinite) (hBA : B ⊆ A)
  (H : ∀ (b ∈ B) (b' ∈ B) (hne : b ≠ b'), b + b' + 1 ∈ A) : bounded_gaps A :=
begin
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b ∈ B := hB.nonempty,
  obtain ⟨b', hb', hlt⟩ : ∃ b' : ℕ, b' ∈ B ∧ b < b',
  { simpa using hB.exists_nat_lt b },
  refine ⟨b' + b' - b, _⟩,
  set Bk : set (ℕ × ℕ) := (λ k : ℕ, (b + k + 1, b' + k + 1)) '' (B \ {b, b'}),
  have infBk : set.infinite Bk,
  { rw set.infinite_image_iff,
    { refine hB.diff _,
      simp },
    { exact λ _, by simp } },
  refine set.infinite.mono _ infBk,
  rintro ⟨p, q⟩ ⟨x, hx, hpx⟩,
  simp only [prod.mk.inj_iff] at hpx,
  rcases hpx with ⟨rfl, rfl⟩,
  simp only [set.mem_diff, set.mem_insert_iff, set.mem_singleton_iff, not_or_distrib, ←ne.def]
    at hx,
  simp only [hlt.ne, H b hb x hx.left hx.right.left.symm, H b' hb' x hx.left hx.right.right.symm,
             ne.def, max_le_iff, tsub_le_iff_right, set.mem_set_of_eq, add_left_inj, not_false_iff,
             true_and, nat.add_sub_assoc hlt.le],
  split,
  { linarith },
  { rw [add_assoc],
    linarith },
end

-- Gallagher Theorem 1

/-- $P_k(h, N)$, the number of integers `n ≤ N` for which the interval $(n, n + h)$ contains
exactly `k` primes. -/
def card_intervals_of_card_eq (h N : ℕ) : ℕ := finset.card
  (((finset.range (N + 1)).image (λ n, finset.Ioc n (n + h))).filter (λ s, ∀ x ∈ s, nat.prime x))


-- Proof of (3)

variables (p : ℕ) (d : finset ℕ)

def prod_differences : ℕ :=
  finset.prod ((finset.image (λ pq : ℕ × ℕ, pq.2 - pq.1) (finset.product d d)).filter (≠ 0)) id

lemma distinct_residue_classes_pos (hd : d.nonempty) : 0 < ν p d :=
by rwa [distinct_residue_classes, finset.card_pos, finset.nonempty.image_iff]

lemma distinct_residue_classes_le : ν p d ≤ d.card := finset.card_image_le

lemma distinct_residue_classes_eq_card (h : ¬ p ∣ prod_differences d) :
  ν p d = d.card :=
begin
  rw [distinct_residue_classes],
  rcases (nat.zero_le p).eq_or_lt with rfl|hp,
  { refine finset.card_image_of_inj_on _,
    refine function.injective.inj_on _ _,
    exact nat.cast_injective },
  contrapose! h,
  replace h := lt_of_le_of_ne finset.card_image_le h,
  obtain ⟨x, hx, y, hy, hne, hxy⟩ : ∃ (x ∈ d) (y ∈ d), x ≠ y ∧ (x : zmod p) = y,
  { exact finset.exists_ne_map_eq_of_card_lt_of_maps_to h (λ _, finset.mem_image_of_mem _) },
  rw prod_differences,
  wlog hlt : x < y := hne.lt_or_lt using [x y, y x],
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, y = x + n * p,
  { refine ⟨(y - x) / p, _⟩,
    rw zmod.nat_coe_eq_nat_coe_iff' at hxy,
    rw [nat.div_mul_cancel, nat.add_sub_of_le hlt.le],
    refine nat.dvd_of_mod_eq_zero _,
    exact nat.sub_mod_eq_zero_of_mod_eq hxy.symm },
  have npos : 0 < n,
  { contrapose! hlt,
    rw [le_zero_iff] at hlt,
    simp [hlt] },
  refine (dvd_mul_left p n).trans (finset.dvd_prod_of_mem _ _),
  simp only [ne.def, finset.mem_filter, finset.mem_image, finset.mem_product, exists_prop,
             prod.exists, nat.mul_eq_zero, not_or_distrib],
  exact ⟨⟨x, _, ⟨hx, hy⟩, nat.add_sub_cancel_left _ _⟩, npos.ne', hp.ne'⟩
end
