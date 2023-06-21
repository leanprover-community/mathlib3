/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.asymptotics.asymptotics
import combinatorics.additive.behrend
import combinatorics.simple_graph.degree_sum
import combinatorics.simple_graph.triangle.tripartite
import data.zmod.basic
import tactic.linear_combination

/-!
# The Ruzsa-Szemerédi problem

This file proves the lower bound of the Ruzsa-Szemerédi problem. The problem is to find the maximum
number of edges that a graph on `n` vertices can have if all edges belong to a most one triangle.
The lower bound comes from turning the big Salem-Spencer set from Behrend's lower bound on Roth
numbers into a graph that has the property that every triangle gives a (possibly trivial)
arithmetic progression on the original set.

## Main declarations

* `simple_graph.ruzsa_szemeredi_number`
* `ruzsa_szemeredi_number_nat_lower_bound`: Explicit lower bound on tThe Ruzsa-Szemerédi graph
   associated to a set `s`.
* `add_salem_spencer.edge_disjoint_triangles`: If `s` is Salem-Spencer, then `add_graph s` has
  edge-disjoint triangles.
-/

namespace asymptotics
variables {α E : Type*} {l : filter α} {f g g' : α → E} [seminormed_add_comm_group E] {c : ℝ}

lemma is_O_with.def (h : is_O_with c l f g) : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by rwa ←is_O_with

lemma is_O.of_add_is_o_right (hf : f =O[l] (g + g')) (hg : g' =o[l] g) : f =O[l] g :=
begin
  obtain ⟨c, hc, h⟩ := hf.exists_pos,
  refine is_O.of_bound (c * (1 + 1/2))
    ((h.def.and $ hg.def one_half_pos).mono $ λ x hx, hx.1.trans _),
  rw [mul_assoc, mul_le_mul_left hc, one_add_mul],
  exact (norm_add_le _ _).trans (add_le_add_left hx.2 _),
end

end asymptotics

namespace asymptotics
variables {α E : Type*} {l : filter α} {f g g' : α → E} [normed_add_comm_group E] {c : ℝ}

protected lemma is_equivalent.is_Theta (h : is_equivalent l f g) : f =Θ[l] g := ⟨h.is_O, h.is_O_symm⟩

lemma is_o.is_Theta_add_left (h : g =o[l] f) : (f + g) =Θ[l] f :=
(is_equivalent.refl.add_is_o h).is_Theta

lemma is_o.is_Theta_sub_left (h : g =o[l] f) : (f - g) =Θ[l] f :=
(is_equivalent.refl.sub_is_o h).is_Theta

lemma is_o.is_O_add_right (hg : g' =o[l] g) : f =O[l] (g + g') ↔ f =O[l] g :=
is_Theta.is_O_congr_right hg.is_Theta_add_left

lemma is_o.is_O_sub_right (hg : g' =o[l] g) : f =O[l] (g - g') ↔ f =O[l] g :=
is_Theta.is_O_congr_right hg.is_Theta_sub_left

end asymptotics

namespace asymptotics
variables {α E : Type*} {l : filter α} {f g g' : α → E} [normed_field E] {c' : ℝ} {c : E}

/-! ### Multiplication by a constant -/

lemma is_O_with_const_div_self (c : E) (f : α → E) (l : filter α) :
  is_O_with ‖c‖⁻¹ l (λ x, f x / c) f :=
is_O_with_of_le' _ $ λ x, by rw [norm_div, div_eq_inv_mul]

lemma is_O_const_div_self (c : E) (f : α → E) (l : filter α) : (λ x, f x / c) =O[l] f :=
(is_O_with_const_div_self c f l).is_O

lemma is_O_with.const_div_left (h : is_O_with c' l f g) (c : E) :
  is_O_with (c' / ‖c‖) l (λ x, f x / c) g :=
by simpa only [div_eq_inv_mul]
  using (is_O_with_const_div_self c f l).trans h (inv_nonneg.2 $ norm_nonneg c)

lemma is_O.const_div_left (h : f =O[l] g) (c : E) : (λ x, f x / c) =O[l] g :=
let ⟨c', hc⟩ := h.is_O_with in (hc.const_div_left _).is_O

lemma is_O_with_self_const_div' (u : Eˣ) (f : α → E) (l : filter α) :
  is_O_with ‖(u : E)‖ l f (λ x, f x / u) :=
begin
  convert (is_O_with_const_div_self ↑u⁻¹ _ l).congr_left (λ x, _),
  { rw [←norm_inv, ←units.coe_inv, inv_inv] },
  { simp }
end

lemma is_O_with_self_const_div (hc : c ≠ 0) (f : α → E) (l : filter α) :
  is_O_with ‖c‖ l f (λ x, f x / c) :=
is_O_with_self_const_div' (units.mk0 c hc) f l

lemma is_O_self_const_div (hc : c ≠ 0) (f : α → E) (l : filter α) : f =O[l] (λ x, f x / c) :=
(is_O_with_self_const_div' (units.mk0 _ hc) f l).is_O

lemma is_O_const_div_left_iff (hc : c ≠ 0) : (λ x, f x / c) =O[l] g ↔ f =O[l] g :=
⟨(is_O_self_const_div hc f l).trans, λ h, h.const_div_left _⟩

lemma is_o.const_div_left (h : f =o[l] g) (c : E) : (λ x, f x / c) =o[l] g :=
(is_O_const_div_self c f l).trans_is_o h

lemma is_o_const_div_left_iff (hc : c ≠ 0) : (λ x, f x / c) =o[l] g ↔ f =o[l] g :=
⟨(is_O_self_const_div hc f l).trans_is_o, λ h, h.const_div_left c⟩

lemma is_O_with.of_const_div_right (hc' : 0 ≤ c') (h : is_O_with c' l f (λ x, g x / c)) :
  is_O_with (c' / ‖c‖) l f g :=
by simpa using h.trans (is_O_with_const_div_self c g l) hc'

lemma is_O.of_const_div_right (h : f =O[l] (λ x, g x / c)) : f =O[l] g :=
let ⟨c, cnonneg, hc⟩ := h.exists_nonneg in (hc.of_const_div_right cnonneg).is_O

lemma is_O_with.const_div_right' {u : Eˣ} (hc' : 0 ≤ c') (h : is_O_with c' l f g) :
  is_O_with (c' * ‖(↑u : E)‖) l f (λ x, g x / ↑u) :=
h.trans (is_O_with_self_const_div' _ _ _) hc'

lemma is_O_with.const_div_right (hc : c ≠ 0) (hc' : 0 ≤ c') (h : is_O_with c' l f g) :
  is_O_with (c' * ‖c‖) l f (λ x, g x / c) :=
h.trans (is_O_with_self_const_div hc g l) hc'

lemma is_O.const_div_right (hc : c ≠ 0) (h : f =O[l] g) : f =O[l] (λ x, g x / c) :=
h.trans (is_O_self_const_div hc g l)

lemma is_O_const_div_right_iff (hc : c ≠ 0) : f =O[l] (λ x, g x / c) ↔ f =O[l] g :=
⟨λ h, h.of_const_div_right, λ h, h.const_div_right hc⟩

lemma is_o.of_const_div_right (h : f =o[l] (λ x, g x / c)) : f =o[l] g :=
h.trans_is_O (is_O_const_div_self c g l)

lemma is_o.const_div_right (hc : c ≠ 0) (h : f =o[l] g) : f =o[l] (λ x, g x / c) :=
h.trans_is_O (is_O_self_const_div hc g l)

lemma is_o_const_div_right_iff (hc : c ≠ 0) : f =o[l] (λ x, g x / c) ↔ f =o[l] g :=
⟨λ h, h.of_const_div_right, λ h, h.const_div_right hc⟩

end asymptotics

namespace nat
variables {a b : ℕ}

lemma le_mul_div_add (hb : b ≠ 0) : a ≤ b * (a / b) + b - 1 :=
le_tsub_of_add_le_right $ by rw [succ_le_iff, ←mul_add_one, mul_comm,
  ←div_lt_iff_lt_mul (pos_iff_ne_zero.2 hb), lt_add_one_iff]

end nat

open finset fintype (card) nat real simple_graph sum3 simple_graph.tripartite_from_triangles
open_locale pointwise

variables {α β : Type*}

/-! ### The Ruzsa-Szemerédi number -/

namespace simple_graph
variables (α) [decidable_eq α] [decidable_eq β] [fintype α] [fintype β] {G H : simple_graph α}
include α

/-- The Ruzsa-Szemerédi number of a fintype is the cardinality of its greatest locally linear simple
graph. -/
noncomputable def ruzsa_szemeredi_number : ℕ :=
by classical; exact nat.find_greatest
  (λ m, ∃ G : simple_graph α, (G.clique_finset 3).card = m ∧ G.locally_linear) ((card α).choose 3)

omit α

lemma ruzsa_szemeredi_number_le : ruzsa_szemeredi_number α ≤ (card α).choose 3 :=
nat.find_greatest_le _

lemma ruzsa_szemeredi_number_spec :
  ∃ G : simple_graph α, (G.clique_finset 3).card = ruzsa_szemeredi_number α ∧ G.locally_linear :=
@nat.find_greatest_spec _ _
  (λ m, ∃ G : simple_graph α, (G.clique_finset 3).card = m ∧ G.locally_linear) _ (nat.zero_le _)
  ⟨⊥, by simp, locally_linear_bot⟩

variables {α} {n : ℕ}

lemma locally_linear.le_ruzsa_szemeredi_number [decidable_rel G.adj] (hG : G.locally_linear) :
  (G.clique_finset 3).card ≤ ruzsa_szemeredi_number α :=
le_find_greatest card_clique_finset_le ⟨G, by congr', hG⟩

lemma ruzsa_szemeredi_number_mono (f : α ↪ β) :
  ruzsa_szemeredi_number α ≤ ruzsa_szemeredi_number β :=
begin
  refine find_greatest_mono _ (choose_mono _ $ fintype.card_le_of_embedding f),
  rintro n ⟨G, rfl, hG⟩,
  refine ⟨G.map f, _, hG.map _⟩,
  rw [←card_map ⟨map f, finset.map_injective _⟩, ←clique_finset_map G f],
  congr',
  dec_trivial,
end

lemma ruzsa_szemeredi_number_congr (e : α ≃ β) :
  ruzsa_szemeredi_number α = ruzsa_szemeredi_number β :=
(ruzsa_szemeredi_number_mono (e : α ↪ β)).antisymm $ ruzsa_szemeredi_number_mono e.symm

noncomputable def ruzsa_szemeredi_number_nat (n : ℕ) : ℕ := ruzsa_szemeredi_number (fin n)

@[simp] lemma ruzsa_szemeredi_number_nat_card :
  ruzsa_szemeredi_number_nat (card α) = ruzsa_szemeredi_number α :=
ruzsa_szemeredi_number_congr (fintype.equiv_fin _).symm

lemma ruzsa_szemeredi_number_nat_mono : monotone ruzsa_szemeredi_number_nat :=
λ m n h, ruzsa_szemeredi_number_mono (fin.cast_le h).to_embedding

lemma ruzsa_szemeredi_number_nat_le : ruzsa_szemeredi_number_nat n ≤ n.choose 3 :=
(ruzsa_szemeredi_number_le _).trans_eq $ by rw fintype.card_fin

@[simp] lemma ruzsa_szmeredi_number_nat_zero : ruzsa_szemeredi_number_nat 0 = 0 :=
le_zero_iff.1 ruzsa_szemeredi_number_nat_le
@[simp] lemma ruzsa_szmeredi_number_nat_one : ruzsa_szemeredi_number_nat 1 = 0 :=
le_zero_iff.1 ruzsa_szemeredi_number_nat_le
@[simp] lemma ruzsa_szmeredi_number_nat_two : ruzsa_szemeredi_number_nat 2 = 0 :=
le_zero_iff.1 ruzsa_szemeredi_number_nat_le

end simple_graph

open simple_graph

/-! ### The Ruzsa-Szemerédi construction -/

namespace ruzsa_szemeredi
variables [fintype α] [comm_ring α] {s : finset α} {x : α × α × α}

/-- The triangle indices for the Ruzsa-Szemerédi construction. -/
private def triangle_indices (s : finset α) : finset (α × α × α) :=
(univ ×ˢ s).map ⟨λ xa, (xa.1, xa.1 + xa.2, xa.1 + 2 * xa.2), begin
  rintro ⟨x, a⟩ ⟨y, b⟩ h,
  simp only [prod.ext_iff] at h,
  obtain rfl := h.1,
  obtain rfl := add_right_injective _ h.2.1,
  refl,
end⟩

@[simp] lemma mem_triangle_indices :
  x ∈ triangle_indices s ↔ ∃ y (a ∈ s), (y, y + a, y + 2 * a) = x :=
by simp [triangle_indices]

@[simp] lemma card_triangle_indices : (triangle_indices s).card = card α * s.card :=
by simp [triangle_indices, card_univ]

lemma no_accidental (hs : add_salem_spencer (s : set α)) :
  no_accidental (triangle_indices s : finset (α × α × α)) :=
⟨begin
  simp only [mem_triangle_indices, prod.mk.inj_iff, exists_prop, forall_exists_index, and_imp],
  rintro _ _ _ _ _ _ d a ha rfl rfl rfl b' b hb rfl rfl h₁ d' c hc rfl h₂ rfl,
  have : a + c = b + b := by linear_combination h₁.symm - h₂.symm,
  obtain rfl := hs ha hc hb this,
  simp [*] at *,
end⟩

variables [fact $ is_unit (2 : α)]

instance : explicit_disjoint (triangle_indices s : finset (α × α × α)) :=
{ inj₀ := begin
    simp only [mem_triangle_indices, prod.mk.inj_iff, exists_prop, forall_exists_index, and_imp],
    rintro _ _ _ _ x a ha rfl rfl rfl y b hb rfl h₁ h₂,
    linear_combination 2*h₁.symm - h₂.symm,
  end,
  inj₁ := begin
    simp only [mem_triangle_indices, prod.mk.inj_iff, exists_prop, forall_exists_index, and_imp],
    rintro _ _ _ _ x a ha rfl rfl rfl y b hb rfl rfl h,
    simpa [(fact.out $ is_unit (2 : α)).mul_right_inj, eq_comm] using h,
  end,
  inj₂ := begin
    simp only [mem_triangle_indices, prod.mk.inj_iff, exists_prop, forall_exists_index, and_imp],
    rintro _ _ _ _ x a ha rfl rfl rfl y b hb rfl h rfl,
    simpa [(fact.out $ is_unit (2 : α)).mul_right_inj, eq_comm] using h,
  end }

lemma locally_linear (hs : add_salem_spencer (s : set α)) :
  (graph $ (triangle_indices s : finset (α × α × α))).locally_linear :=
by { haveI := no_accidental hs, exact tripartite_from_triangles.locally_linear _ }

lemma card_edge_finset (hs : add_salem_spencer (s : set α)) [decidable_eq α] :
  (graph $ (triangle_indices s : finset (α × α × α))).edge_finset.card = 3 * card α * s.card :=
begin
  haveI := no_accidental hs,
  rw [(locally_linear hs).card_edge_finset, card_triangles, card_triangle_indices, mul_assoc],
end

end ruzsa_szemeredi

open ruzsa_szemeredi

variables (α) [fintype α] [decidable_eq α] [comm_ring α] [fact $ is_unit (2 : α)]

lemma add_roth_number_le_ruzsa_szemeredi_number :
  card α * add_roth_number (univ : finset α) ≤ ruzsa_szemeredi_number (α ⊕ α ⊕ α) :=
begin
  obtain ⟨s, -, hscard, hs⟩ := add_roth_number_spec (univ : finset α),
  haveI := no_accidental hs,
  rw [←hscard, ←card_triangle_indices, ←card_triangles],
  exact (locally_linear hs).le_ruzsa_szemeredi_number,
end

lemma roth_number_nat_le_ruzsa_szemeredi_number_nat (n : ℕ) :
  (2 * n + 1) * roth_number_nat n ≤ ruzsa_szemeredi_number_nat (6 * n + 3) :=
begin
  refine (mul_le_mul_left' ((fin.roth_number_nat_le_add_roth_number le_rfl).trans $
    add_roth_number.mono $ subset_univ _) _).trans _,
  rw ←fintype.card_fin (2 * n + 1),
  have : nat.coprime 2 (2 * n + 1) := by simp,
  haveI : fact (is_unit (2 : fin (2 * n + 1))) :=
    ⟨by simpa using (zmod.unit_of_coprime 2 this).is_unit⟩,
  refine (add_roth_number_le_ruzsa_szemeredi_number _).trans_eq _,
  simp_rw [←ruzsa_szemeredi_number_nat_card, fintype.card_sum, fintype.card_fin],
  ring_nf,
end

lemma roth_number_nat_le_ruzsa_szemeredi_number_nat' :
   ∀ n : ℕ, (n / 3 - 2 : ℝ) * roth_number_nat ((n - 3) / 6) ≤ ruzsa_szemeredi_number_nat n
| 0 := by simp
| 1 := by simp
| 2 := by simp
| (n + 3) := begin
    calc
        _ ≤ (↑(2 * (n / 6) + 1) : ℝ) * roth_number_nat (n / 6)
          : mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _)
      ... ≤ (ruzsa_szemeredi_number_nat (6 * (n / 6) + 3) : ℝ) : _
      ... ≤ _ : nat.cast_le.2
                  (ruzsa_szemeredi_number_nat_mono $ add_le_add_right (nat.mul_div_le _ _) _),
    { norm_num,
      rw [←div_add_one (three_ne_zero' ℝ), ←le_sub_iff_add_le, div_le_iff (zero_lt_three' ℝ),
        add_assoc, add_sub_assoc, add_mul, mul_right_comm],
      norm_num,
      norm_cast,
      exact (nat.le_mul_div_add $ show 6 ≠ 0, by norm_num).trans (by norm_num) },
    { norm_cast,
      exact roth_number_nat_le_ruzsa_szemeredi_number_nat _ }
  end

lemma ruzsa_szemeredi_number_nat_lower_bound (n : ℕ) :
  (n / 3 - 2 : ℝ) * ↑((n - 3) / 6) * exp (-4 * sqrt (log ↑((n - 3) / 6))) ≤
    ruzsa_szemeredi_number_nat n :=
begin
  rw mul_assoc,
  obtain hn | hn := le_total (n / 3 - 2 : ℝ) 0,
  { exact (mul_nonpos_of_nonpos_of_nonneg hn $ by positivity).trans (nat.cast_nonneg _) },
  { exact (mul_le_mul_of_nonneg_left behrend.roth_lower_bound hn).trans
      (roth_number_nat_le_ruzsa_szemeredi_number_nat' _) }
end

open asymptotics filter

lemma ruzsa_szemeredi_number_nat_asymptotic :
  is_O at_top (λ n, n ^ 2 * exp (-4 * sqrt (log n)) : ℕ → ℝ)
    (λ n, (ruzsa_szemeredi_number_nat n : ℝ)) :=
begin
  have : is_O at_top
    (λ n, (n / 3 - 2) * ↑((n - 3) / 6) * exp (-4 * sqrt (log ↑((n - 3) / 6))) : ℕ → ℝ)
    (λ n, (ruzsa_szemeredi_number_nat n : ℝ)),
  { refine is_O.of_bound 1 _,
    simp only [neg_mul, norm_eq_abs, norm_coe_nat, one_mul, eventually_at_top, ge_iff_le],
    refine ⟨6, λ n hn, _⟩,
    simpa using abs_le_abs_of_nonneg _ (ruzsa_szemeredi_number_nat_lower_bound n),
    have : (0 : ℝ) ≤ n / 3 - 2 := sorry,
    positivity },
  simp_rw sq,
  refine is_O.trans _ this,
  refine (is_O.mul _ _).mul (is_O.of_bound' $ eventually_at_top.2 ⟨9, λ n hn, _⟩),
  refine (is_o_const_left.2 $ or.inr _).is_O_sub_right.2 _,
  sorry,
  refine is_O_self_const_div three_ne_zero _ _,
  sorry,
  have : (0 : ℝ) < ↑((n - 3) / 6) := sorry,
  have : (0 : ℝ) < n := sorry,
  have : 0 ≤ real.log n := sorry,
  simp only [neg_mul, norm_eq_abs, abs_exp, exp_le_exp, neg_le_neg_iff, mul_le_mul_left,
    zero_lt_bit0, zero_lt_one, log_le_log, real.sqrt_le_sqrt_iff, real.log_le_log, cast_le, *],
  exact (nat.div_le_self _ _).trans tsub_le_self,
end
