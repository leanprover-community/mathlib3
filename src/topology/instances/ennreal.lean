/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import topology.instances.nnreal
import order.liminf_limsup
import topology.metric_space.lipschitz
/-!
# Extended non-negative reals
-/

noncomputable theory

open classical set filter metric
open_locale classical topological_space ennreal nnreal big_operators filter

variables {α : Type*} {β : Type*} {γ : Type*}

namespace ennreal
variables {a b c d : ℝ≥0∞} {r p q : ℝ≥0}
variables {x y z : ℝ≥0∞} {ε ε₁ ε₂ : ℝ≥0∞} {s : set ℝ≥0∞}

section topological_space
open topological_space

/-- Topology on `ℝ≥0∞`.

Note: this is different from the `emetric_space` topology. The `emetric_space` topology has
`is_open {⊤}`, while this topology doesn't have singleton elements. -/
instance : topological_space ℝ≥0∞ := preorder.topology ℝ≥0∞

instance : order_topology ℝ≥0∞ := ⟨rfl⟩

instance : t2_space ℝ≥0∞ := by apply_instance -- short-circuit type class inference

instance : second_countable_topology ℝ≥0∞ :=
⟨⟨⋃q ≥ (0:ℚ), {{a : ℝ≥0∞ | a < real.to_nnreal q}, {a : ℝ≥0∞ | ↑(real.to_nnreal q) < a}},
  (countable_encodable _).bUnion $ assume a ha, (countable_singleton _).insert _,
  le_antisymm
    (le_generate_from $ by simp [or_imp_distrib, is_open_lt', is_open_gt'] {contextual := tt})
    (le_generate_from $ λ s h, begin
      rcases h with ⟨a, hs | hs⟩;
      [ rw show s = ⋃q∈{q:ℚ | 0 ≤ q ∧ a < real.to_nnreal q}, {b | ↑(real.to_nnreal q) < b},
           from set.ext (assume b, by simp [hs, @ennreal.lt_iff_exists_rat_btwn a b, and_assoc]),
        rw show s = ⋃q∈{q:ℚ | 0 ≤ q ∧ ↑(real.to_nnreal q) < a}, {b | b < ↑(real.to_nnreal q)},
           from set.ext (assume b,
             by simp [hs, @ennreal.lt_iff_exists_rat_btwn b a, and_comm, and_assoc])];
      { apply is_open_Union, intro q,
        apply is_open_Union, intro hq,
        exact generate_open.basic _ (mem_bUnion hq.1 $ by simp) }
    end)⟩⟩

lemma embedding_coe : embedding (coe : ℝ≥0 → ℝ≥0∞) :=
⟨⟨begin
  refine le_antisymm _ _,
  { rw [@order_topology.topology_eq_generate_intervals ℝ≥0∞ _,
      ← coinduced_le_iff_le_induced],
    refine le_generate_from (assume s ha, _),
    rcases ha with ⟨a, rfl | rfl⟩,
    show is_open {b : ℝ≥0 | a < ↑b},
    { cases a; simp [none_eq_top, some_eq_coe, is_open_lt'] },
    show is_open {b : ℝ≥0 | ↑b < a},
    { cases a; simp [none_eq_top, some_eq_coe, is_open_gt', is_open_const] } },
  { rw [@order_topology.topology_eq_generate_intervals ℝ≥0 _],
    refine le_generate_from (assume s ha, _),
    rcases ha with ⟨a, rfl | rfl⟩,
    exact ⟨Ioi a, is_open_Ioi, by simp [Ioi]⟩,
    exact ⟨Iio a, is_open_Iio, by simp [Iio]⟩ }
  end⟩,
  assume a b, coe_eq_coe.1⟩

lemma is_open_ne_top : is_open {a : ℝ≥0∞ | a ≠ ⊤} := is_open_ne

lemma is_open_Ico_zero : is_open (Ico 0 b) := by { rw ennreal.Ico_eq_Iio, exact is_open_Iio}

lemma open_embedding_coe : open_embedding (coe : ℝ≥0 → ℝ≥0∞) :=
⟨embedding_coe, by { convert is_open_ne_top, ext (x|_); simp [none_eq_top, some_eq_coe] }⟩

lemma coe_range_mem_nhds : range (coe : ℝ≥0 → ℝ≥0∞) ∈ 𝓝 (r : ℝ≥0∞) :=
is_open.mem_nhds open_embedding_coe.open_range $ mem_range_self _

@[norm_cast] lemma tendsto_coe {f : filter α} {m : α → ℝ≥0} {a : ℝ≥0} :
  tendsto (λa, (m a : ℝ≥0∞)) f (𝓝 ↑a) ↔ tendsto m f (𝓝 a) :=
embedding_coe.tendsto_nhds_iff.symm

lemma continuous_coe : continuous (coe : ℝ≥0 → ℝ≥0∞) :=
embedding_coe.continuous

lemma continuous_coe_iff  {α} [topological_space α] {f : α → ℝ≥0} :
  continuous (λa, (f a : ℝ≥0∞)) ↔ continuous f :=
embedding_coe.continuous_iff.symm

lemma nhds_coe {r : ℝ≥0} : 𝓝 (r : ℝ≥0∞) = (𝓝 r).map coe :=
(open_embedding_coe.map_nhds_eq r).symm

lemma tendsto_nhds_coe_iff {α : Type*} {l : filter α} {x : ℝ≥0} {f : ℝ≥0∞ → α} :
  tendsto f (𝓝 ↑x) l ↔ tendsto (f ∘ coe : ℝ≥0 → α) (𝓝 x) l :=
show _ ≤ _ ↔ _ ≤ _, by rw [nhds_coe, filter.map_map]

lemma continuous_at_coe_iff {α : Type*} [topological_space α] {x : ℝ≥0} {f : ℝ≥0∞ → α} :
  continuous_at f (↑x) ↔ continuous_at (f ∘ coe : ℝ≥0 → α) x :=
tendsto_nhds_coe_iff

lemma nhds_coe_coe {r p : ℝ≥0} :
  𝓝 ((r : ℝ≥0∞), (p : ℝ≥0∞)) = (𝓝 (r, p)).map (λp:ℝ≥0×ℝ≥0, (p.1, p.2)) :=
((open_embedding_coe.prod open_embedding_coe).map_nhds_eq (r, p)).symm

lemma continuous_of_real : continuous ennreal.of_real :=
(continuous_coe_iff.2 continuous_id).comp nnreal.continuous_of_real

lemma tendsto_of_real {f : filter α} {m : α → ℝ} {a : ℝ} (h : tendsto m f (𝓝 a)) :
  tendsto (λa, ennreal.of_real (m a)) f (𝓝 (ennreal.of_real a)) :=
tendsto.comp (continuous.tendsto continuous_of_real _) h

lemma tendsto_to_nnreal {a : ℝ≥0∞} (ha : a ≠ ⊤) :
  tendsto ennreal.to_nnreal (𝓝 a) (𝓝 a.to_nnreal) :=
begin
  lift a to ℝ≥0 using ha,
  rw [nhds_coe, tendsto_map'_iff],
  exact tendsto_id
end

lemma eventually_eq_of_to_real_eventually_eq {l : filter α} {f g : α → ℝ≥0∞}
  (hfi : ∀ᶠ x in l, f x ≠ ∞) (hgi : ∀ᶠ x in l, g x ≠ ∞)
  (hfg : (λ x, (f x).to_real) =ᶠ[l] (λ x, (g x).to_real)) :
  f =ᶠ[l] g :=
begin
  filter_upwards [hfi, hgi, hfg],
  intros x hfx hgx hfgx,
  rwa ← ennreal.to_real_eq_to_real hfx hgx,
end

lemma continuous_on_to_nnreal : continuous_on ennreal.to_nnreal {a | a ≠ ∞}  :=
λ a ha, continuous_at.continuous_within_at (tendsto_to_nnreal ha)

lemma tendsto_to_real {a : ℝ≥0∞} (ha : a ≠ ⊤) : tendsto ennreal.to_real (𝓝 a) (𝓝 a.to_real) :=
nnreal.tendsto_coe.2 $ tendsto_to_nnreal ha

/-- The set of finite `ℝ≥0∞` numbers is homeomorphic to `ℝ≥0`. -/
def ne_top_homeomorph_nnreal : {a | a ≠ ∞} ≃ₜ ℝ≥0 :=
{ continuous_to_fun := continuous_on_iff_continuous_restrict.1 continuous_on_to_nnreal,
  continuous_inv_fun := continuous_subtype_mk _ continuous_coe,
  .. ne_top_equiv_nnreal }

/-- The set of finite `ℝ≥0∞` numbers is homeomorphic to `ℝ≥0`. -/
def lt_top_homeomorph_nnreal : {a | a < ∞} ≃ₜ ℝ≥0 :=
by refine (homeomorph.set_congr $ set.ext $ λ x, _).trans ne_top_homeomorph_nnreal;
  simp only [mem_set_of_eq, lt_top_iff_ne_top]

lemma nhds_top : 𝓝 ∞ = ⨅ a ≠ ∞, 𝓟 (Ioi a) :=
nhds_top_order.trans $ by simp [lt_top_iff_ne_top, Ioi]

lemma nhds_top' : 𝓝 ∞ = ⨅ r : ℝ≥0, 𝓟 (Ioi r) :=
nhds_top.trans $ infi_ne_top _

lemma nhds_top_basis : (𝓝 ∞).has_basis (λ a, a < ∞) (λ a, Ioi a) := nhds_top_basis

lemma tendsto_nhds_top_iff_nnreal {m : α → ℝ≥0∞} {f : filter α} :
  tendsto m f (𝓝 ⊤) ↔ ∀ x : ℝ≥0, ∀ᶠ a in f, ↑x < m a :=
by simp only [nhds_top', tendsto_infi, tendsto_principal, mem_Ioi]

lemma tendsto_nhds_top_iff_nat {m : α → ℝ≥0∞} {f : filter α} :
  tendsto m f (𝓝 ⊤) ↔ ∀ n : ℕ, ∀ᶠ a in f, ↑n < m a :=
tendsto_nhds_top_iff_nnreal.trans ⟨λ h n, by simpa only [ennreal.coe_nat] using h n,
  λ h x, let ⟨n, hn⟩ := exists_nat_gt x in
    (h n).mono (λ y, lt_trans $ by rwa [← ennreal.coe_nat, coe_lt_coe])⟩

lemma tendsto_nhds_top {m : α → ℝ≥0∞} {f : filter α}
  (h : ∀ n : ℕ, ∀ᶠ a in f, ↑n < m a) : tendsto m f (𝓝 ⊤) :=
tendsto_nhds_top_iff_nat.2 h

lemma tendsto_nat_nhds_top : tendsto (λ n : ℕ, ↑n) at_top (𝓝 ∞) :=
tendsto_nhds_top $ λ n, mem_at_top_sets.2
  ⟨n+1, λ m hm, ennreal.coe_nat_lt_coe_nat.2 $ nat.lt_of_succ_le hm⟩

@[simp, norm_cast] lemma tendsto_coe_nhds_top {f : α → ℝ≥0} {l : filter α} :
  tendsto (λ x, (f x : ℝ≥0∞)) l (𝓝 ∞) ↔ tendsto f l at_top :=
by rw [tendsto_nhds_top_iff_nnreal, at_top_basis_Ioi.tendsto_right_iff];
  [simp, apply_instance, apply_instance]

lemma nhds_zero : 𝓝 (0 : ℝ≥0∞) = ⨅a ≠ 0, 𝓟 (Iio a) :=
nhds_bot_order.trans $ by simp [bot_lt_iff_ne_bot, Iio]

lemma nhds_zero_basis : (𝓝 (0 : ℝ≥0∞)).has_basis (λ a : ℝ≥0∞, 0 < a) (λ a, Iio a) := nhds_bot_basis

lemma nhds_zero_basis_Iic : (𝓝 (0 : ℝ≥0∞)).has_basis (λ a : ℝ≥0∞, 0 < a) Iic := nhds_bot_basis_Iic

@[instance] lemma nhds_within_Ioi_coe_ne_bot {r : ℝ≥0} : (𝓝[>] (r : ℝ≥0∞)).ne_bot :=
nhds_within_Ioi_self_ne_bot' ⟨⊤, ennreal.coe_lt_top⟩

@[instance] lemma nhds_within_Ioi_zero_ne_bot : (𝓝[>] (0 : ℝ≥0∞)).ne_bot :=
nhds_within_Ioi_coe_ne_bot

-- using Icc because
-- • don't have 'Ioo (x - ε) (x + ε) ∈ 𝓝 x' unless x > 0
-- • (x - y ≤ ε ↔ x ≤ ε + y) is true, while (x - y < ε ↔ x < ε + y) is not
lemma Icc_mem_nhds (xt : x ≠ ⊤) (ε0 : ε ≠ 0) : Icc (x - ε) (x + ε) ∈ 𝓝 x :=
begin
  rw _root_.mem_nhds_iff,
  by_cases x0 : x = 0,
  { use Iio (x + ε),
    have : Iio (x + ε) ⊆ Icc (x - ε) (x + ε), assume a, rw x0, simpa using le_of_lt,
    use this, exact ⟨is_open_Iio, mem_Iio_self_add xt ε0⟩ },
  { use Ioo (x - ε) (x + ε), use Ioo_subset_Icc_self,
    exact ⟨is_open_Ioo, mem_Ioo_self_sub_add xt x0 ε0 ε0 ⟩ }
end

lemma nhds_of_ne_top (xt : x ≠ ⊤) : 𝓝 x = ⨅ ε > 0, 𝓟 (Icc (x - ε) (x + ε)) :=
begin
  refine le_antisymm _ _,
  -- first direction
  simp only [le_infi_iff, le_principal_iff], assume ε ε0, exact Icc_mem_nhds xt ε0.lt.ne',
  -- second direction
  rw nhds_generate_from, refine le_infi (assume s, le_infi $ assume hs, _),
  rcases hs with ⟨xs, ⟨a, (rfl : s = Ioi a)|(rfl : s = Iio a)⟩⟩,
  { rcases exists_between xs with ⟨b, ab, bx⟩,
    have xb_pos : 0 < x - b := tsub_pos_iff_lt.2 bx,
    have xxb : x - (x - b) = b := sub_sub_cancel xt bx.le,
    refine infi_le_of_le (x - b) (infi_le_of_le xb_pos _),
    simp only [mem_principal, le_principal_iff],
    assume y, rintros ⟨h₁, h₂⟩, rw xxb at h₁, calc a < b : ab ... ≤ y : h₁ },
  { rcases exists_between xs with ⟨b, xb, ba⟩,
    have bx_pos : 0 < b - x := tsub_pos_iff_lt.2 xb,
    have xbx : x + (b - x) = b := add_tsub_cancel_of_le xb.le,
    refine infi_le_of_le (b - x) (infi_le_of_le bx_pos _),
    simp only [mem_principal, le_principal_iff],
    assume y, rintros ⟨h₁, h₂⟩, rw xbx at h₂, calc y ≤ b : h₂ ... < a : ba },
end

/-- Characterization of neighborhoods for `ℝ≥0∞` numbers. See also `tendsto_order`
for a version with strict inequalities. -/
protected theorem tendsto_nhds {f : filter α} {u : α → ℝ≥0∞} {a : ℝ≥0∞} (ha : a ≠ ⊤) :
  tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in f, (u x) ∈ Icc (a - ε) (a + ε) :=
by simp only [nhds_of_ne_top ha, tendsto_infi, tendsto_principal, mem_Icc]

protected lemma tendsto_at_top [nonempty β] [semilattice_sup β] {f : β → ℝ≥0∞} {a : ℝ≥0∞}
  (ha : a ≠ ⊤) : tendsto f at_top (𝓝 a) ↔ ∀ε>0, ∃N, ∀n≥N, (f n) ∈ Icc (a - ε) (a + ε) :=
by simp only [ennreal.tendsto_nhds ha, mem_at_top_sets, mem_set_of_eq, filter.eventually]

instance : has_continuous_add ℝ≥0∞ :=
begin
  refine ⟨continuous_iff_continuous_at.2 _⟩,
  rintro ⟨(_|a), b⟩,
  { exact tendsto_nhds_top_mono' continuous_at_fst (λ p, le_add_right le_rfl) },
  rcases b with (_|b),
  { exact tendsto_nhds_top_mono' continuous_at_snd (λ p, le_add_left le_rfl) },
  simp only [continuous_at, some_eq_coe, nhds_coe_coe, ← coe_add, tendsto_map'_iff, (∘),
    tendsto_coe, tendsto_add]
end

protected lemma tendsto_at_top_zero [hβ : nonempty β] [semilattice_sup β] {f : β → ℝ≥0∞} :
  filter.at_top.tendsto f (𝓝 0) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, f n ≤ ε :=
begin
  rw ennreal.tendsto_at_top zero_ne_top,
  { simp_rw [set.mem_Icc, zero_add, zero_tsub, zero_le _, true_and], },
  { exact hβ, },
end

protected lemma tendsto_mul (ha : a ≠ 0 ∨ b ≠ ⊤) (hb : b ≠ 0 ∨ a ≠ ⊤) :
  tendsto (λp:ℝ≥0∞×ℝ≥0∞, p.1 * p.2) (𝓝 (a, b)) (𝓝 (a * b)) :=
have ht : ∀b:ℝ≥0∞, b ≠ 0 → tendsto (λp:ℝ≥0∞×ℝ≥0∞, p.1 * p.2) (𝓝 ((⊤:ℝ≥0∞), b)) (𝓝 ⊤),
begin
  refine assume b hb, tendsto_nhds_top_iff_nnreal.2 $ assume n, _,
  rcases lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hb) with ⟨ε, hε, hεb⟩,
  replace hε : 0 < ε, from coe_pos.1 hε,
  filter_upwards [prod_is_open.mem_nhds (lt_mem_nhds $ @coe_lt_top (n / ε)) (lt_mem_nhds hεb)],
  rintros ⟨a₁, a₂⟩ ⟨h₁, h₂⟩,
  dsimp at h₁ h₂ ⊢,
  rw [← div_mul_cancel n hε.ne', coe_mul],
  exact mul_lt_mul h₁ h₂
end,
begin
  cases a, {simp [none_eq_top] at hb, simp [none_eq_top, ht b hb, top_mul, hb] },
  cases b,
  { simp [none_eq_top] at ha,
    simp [*, nhds_swap (a : ℝ≥0∞) ⊤, none_eq_top, some_eq_coe, top_mul, tendsto_map'_iff, (∘),
      mul_comm] },
  simp [some_eq_coe, nhds_coe_coe, tendsto_map'_iff, (∘)],
  simp only [coe_mul.symm, tendsto_coe, tendsto_mul]
end

protected lemma tendsto.mul {f : filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
  (hma : tendsto ma f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ ⊤) (hmb : tendsto mb f (𝓝 b)) (hb : b ≠ 0 ∨ a ≠ ⊤) :
  tendsto (λa, ma a * mb a) f (𝓝 (a * b)) :=
show tendsto ((λp:ℝ≥0∞×ℝ≥0∞, p.1 * p.2) ∘ (λa, (ma a, mb a))) f (𝓝 (a * b)), from
tendsto.comp (ennreal.tendsto_mul ha hb) (hma.prod_mk_nhds hmb)

protected lemma tendsto.const_mul {f : filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
  (hm : tendsto m f (𝓝 b)) (hb : b ≠ 0 ∨ a ≠ ⊤) : tendsto (λb, a * m b) f (𝓝 (a * b)) :=
by_cases
  (assume : a = 0, by simp [this, tendsto_const_nhds])
  (assume ha : a ≠ 0, ennreal.tendsto.mul tendsto_const_nhds (or.inl ha) hm hb)

protected lemma tendsto.mul_const {f : filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
  (hm : tendsto m f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ ⊤) : tendsto (λx, m x * b) f (𝓝 (a * b)) :=
by simpa only [mul_comm] using ennreal.tendsto.const_mul hm ha

lemma tendsto_finset_prod_of_ne_top {ι : Type*} {f : ι → α → ℝ≥0∞} {x : filter α} {a : ι → ℝ≥0∞}
  (s : finset ι) (h : ∀ i ∈ s, tendsto (f i) x (𝓝 (a i))) (h' : ∀ i ∈ s, a i ≠ ∞):
  tendsto (λ b, ∏ c in s, f c b) x (𝓝 (∏ c in s, a c)) :=
begin
  induction s using finset.induction with a s has IH, { simp [tendsto_const_nhds] },
  simp only [finset.prod_insert has],
  apply tendsto.mul (h _ (finset.mem_insert_self _ _)),
  { right,
    exact (prod_lt_top (λ i hi, h' _ (finset.mem_insert_of_mem hi))).ne },
  { exact IH (λ i hi, h _ (finset.mem_insert_of_mem hi))
      (λ i hi, h' _ (finset.mem_insert_of_mem hi)) },
  { exact or.inr (h' _ (finset.mem_insert_self _ _)) }
end

protected lemma continuous_at_const_mul {a b : ℝ≥0∞} (h : a ≠ ⊤ ∨ b ≠ 0) :
  continuous_at ((*) a) b :=
tendsto.const_mul tendsto_id h.symm

protected lemma continuous_at_mul_const {a b : ℝ≥0∞} (h : a ≠ ⊤ ∨ b ≠ 0) :
  continuous_at (λ x, x * a) b :=
tendsto.mul_const tendsto_id h.symm

protected lemma continuous_const_mul {a : ℝ≥0∞} (ha : a ≠ ⊤) : continuous ((*) a) :=
continuous_iff_continuous_at.2 $ λ x, ennreal.continuous_at_const_mul (or.inl ha)

protected lemma continuous_mul_const {a : ℝ≥0∞} (ha : a ≠ ⊤) : continuous (λ x, x * a) :=
continuous_iff_continuous_at.2 $ λ x, ennreal.continuous_at_mul_const (or.inl ha)

@[continuity]
lemma continuous_pow (n : ℕ) : continuous (λ a : ℝ≥0∞, a ^ n) :=
begin
  induction n with n IH,
  { simp [continuous_const] },
  simp_rw [nat.succ_eq_add_one, pow_add, pow_one, continuous_iff_continuous_at],
  assume x,
  refine ennreal.tendsto.mul (IH.tendsto _) _ tendsto_id _;
  by_cases H : x = 0,
  { simp only [H, zero_ne_top, ne.def, or_true, not_false_iff]},
  { exact or.inl (λ h, H (pow_eq_zero h)) },
  { simp only [H, pow_eq_top_iff, zero_ne_top, false_or, eq_self_iff_true,
               not_true, ne.def, not_false_iff, false_and], },
  { simp only [H, true_or, ne.def, not_false_iff] }
end

protected lemma tendsto.pow {f : filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} {n : ℕ}
  (hm : tendsto m f (𝓝 a)) :
  tendsto (λ x, (m x) ^ n) f (𝓝 (a ^ n)) :=
((continuous_pow n).tendsto a).comp hm

lemma le_of_forall_lt_one_mul_le {x y : ℝ≥0∞} (h : ∀ a < 1, a * x ≤ y) : x ≤ y :=
begin
  have : tendsto (* x) (𝓝[<] 1) (𝓝 (1 * x)) :=
    (ennreal.continuous_at_mul_const (or.inr one_ne_zero)).mono_left inf_le_left,
  rw one_mul at this,
  haveI : (𝓝[<] (1 : ℝ≥0∞)).ne_bot := nhds_within_Iio_self_ne_bot' ⟨0, ennreal.zero_lt_one⟩,
  exact le_of_tendsto this (eventually_nhds_within_iff.2 $ eventually_of_forall h)
end

lemma infi_mul_left' {ι} {f : ι → ℝ≥0∞} {a : ℝ≥0∞}
  (h : a = ⊤ → (⨅ i, f i) = 0 → ∃ i, f i = 0) (h0 : a = 0 → nonempty ι) :
  (⨅ i, a * f i) = a * ⨅ i, f i :=
begin
  by_cases H : a = ⊤ ∧ (⨅ i, f i) = 0,
  { rcases h H.1 H.2 with ⟨i, hi⟩,
    rw [H.2, mul_zero, ← bot_eq_zero, infi_eq_bot],
    exact λ b hb, ⟨i, by rwa [hi, mul_zero, ← bot_eq_zero]⟩ },
  { rw not_and_distrib at H,
    casesI is_empty_or_nonempty ι,
    { rw [infi_of_empty, infi_of_empty, mul_top, if_neg],
      exact mt h0 (not_nonempty_iff.2 ‹_›) },
    { exact (map_infi_of_continuous_at_of_monotone' (ennreal.continuous_at_const_mul H)
        ennreal.mul_left_mono).symm } }
end

lemma infi_mul_left {ι} [nonempty ι] {f : ι → ℝ≥0∞} {a : ℝ≥0∞}
  (h : a = ⊤ → (⨅ i, f i) = 0 → ∃ i, f i = 0) :
  (⨅ i, a * f i) = a * ⨅ i, f i :=
infi_mul_left' h (λ _, ‹nonempty ι›)

lemma infi_mul_right' {ι} {f : ι → ℝ≥0∞} {a : ℝ≥0∞}
  (h : a = ⊤ → (⨅ i, f i) = 0 → ∃ i, f i = 0) (h0 : a = 0 → nonempty ι) :
  (⨅ i, f i * a) = (⨅ i, f i) * a :=
by simpa only [mul_comm a] using infi_mul_left' h h0

lemma infi_mul_right {ι} [nonempty ι] {f : ι → ℝ≥0∞} {a : ℝ≥0∞}
  (h : a = ⊤ → (⨅ i, f i) = 0 → ∃ i, f i = 0) :
  (⨅ i, f i * a) = (⨅ i, f i) * a :=
infi_mul_right' h (λ _, ‹nonempty ι›)

protected lemma continuous_inv : continuous (has_inv.inv : ℝ≥0∞ → ℝ≥0∞) :=
continuous_iff_continuous_at.2 $ λ a, tendsto_order.2
⟨begin
  assume b hb,
  simp only [@ennreal.lt_inv_iff_lt_inv b],
  exact gt_mem_nhds (ennreal.lt_inv_iff_lt_inv.1 hb),
end,
begin
  assume b hb,
  simp only [gt_iff_lt, @ennreal.inv_lt_iff_inv_lt _ b],
  exact lt_mem_nhds (ennreal.inv_lt_iff_inv_lt.1 hb)
end⟩

@[simp] protected lemma tendsto_inv_iff {f : filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} :
  tendsto (λ x, (m x)⁻¹) f (𝓝 a⁻¹) ↔ tendsto m f (𝓝 a) :=
⟨λ h, by simpa only [function.comp, ennreal.inv_inv]
  using (ennreal.continuous_inv.tendsto a⁻¹).comp h,
  (ennreal.continuous_inv.tendsto a).comp⟩

protected lemma tendsto.div {f : filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
  (hma : tendsto ma f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ 0) (hmb : tendsto mb f (𝓝 b)) (hb : b ≠ ⊤ ∨ a ≠ ⊤) :
  tendsto (λa, ma a / mb a) f (𝓝 (a / b)) :=
by { apply tendsto.mul hma _ (ennreal.tendsto_inv_iff.2 hmb) _; simp [ha, hb] }

protected lemma tendsto.const_div {f : filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
  (hm : tendsto m f (𝓝 b)) (hb : b ≠ ⊤ ∨ a ≠ ⊤) : tendsto (λb, a / m b) f (𝓝 (a / b)) :=
by { apply tendsto.const_mul (ennreal.tendsto_inv_iff.2 hm), simp [hb] }

protected lemma tendsto.div_const {f : filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
  (hm : tendsto m f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ 0) : tendsto (λx, m x / b) f (𝓝 (a / b)) :=
by { apply tendsto.mul_const hm, simp [ha] }

protected lemma tendsto_inv_nat_nhds_zero : tendsto (λ n : ℕ, (n : ℝ≥0∞)⁻¹) at_top (𝓝 0) :=
ennreal.inv_top ▸ ennreal.tendsto_inv_iff.2 tendsto_nat_nhds_top

lemma bsupr_add {ι} {s : set ι} (hs : s.nonempty) {f : ι → ℝ≥0∞} :
  (⨆ i ∈ s, f i) + a = ⨆ i ∈ s, f i + a :=
begin
  simp only [← Sup_image], symmetry,
  rw [image_comp (+ a)],
  refine is_lub.Sup_eq ((is_lub_Sup $ f '' s).is_lub_of_tendsto _ (hs.image _) _),
  exacts [λ x _ y _ hxy, add_le_add hxy le_rfl,
    tendsto.add (tendsto_id' inf_le_left) tendsto_const_nhds]
end

lemma Sup_add {s : set ℝ≥0∞} (hs : s.nonempty) : Sup s + a = ⨆b∈s, b + a :=
by rw [Sup_eq_supr, bsupr_add hs]

lemma supr_add {ι : Sort*} {s : ι → ℝ≥0∞} [h : nonempty ι] : supr s + a = ⨆b, s b + a :=
let ⟨x⟩ := h in
calc supr s + a = Sup (range s) + a : by rw Sup_range
  ... = (⨆b∈range s, b + a) : Sup_add ⟨s x, x, rfl⟩
  ... = _ : supr_range

lemma add_supr {ι : Sort*} {s : ι → ℝ≥0∞} [h : nonempty ι] : a + supr s = ⨆b, a + s b :=
by rw [add_comm, supr_add]; simp [add_comm]

lemma supr_add_supr {ι : Sort*} {f g : ι → ℝ≥0∞} (h : ∀i j, ∃k, f i + g j ≤ f k + g k) :
  supr f + supr g = (⨆ a, f a + g a) :=
begin
  by_cases hι : nonempty ι,
  { letI := hι,
    refine le_antisymm _ (supr_le $ λ a, add_le_add (le_supr _ _) (le_supr _ _)),
    simpa [add_supr, supr_add] using
      λ i j:ι, show f i + g j ≤ ⨆ a, f a + g a, from
      let ⟨k, hk⟩ := h i j in le_supr_of_le k hk },
  { have : ∀f:ι → ℝ≥0∞, (⨆i, f i) = 0 := λ f, supr_eq_zero.mpr (λ i, (hι ⟨i⟩).elim),
    rw [this, this, this, zero_add] }
end

lemma supr_add_supr_of_monotone {ι : Sort*} [semilattice_sup ι]
  {f g : ι → ℝ≥0∞} (hf : monotone f) (hg : monotone g) :
  supr f + supr g = (⨆ a, f a + g a) :=
supr_add_supr $ assume i j, ⟨i ⊔ j, add_le_add (hf $ le_sup_left) (hg $ le_sup_right)⟩

lemma finset_sum_supr_nat {α} {ι} [semilattice_sup ι] {s : finset α} {f : α → ι → ℝ≥0∞}
  (hf : ∀a, monotone (f a)) :
  ∑ a in s, supr (f a) = (⨆ n, ∑ a in s, f a n) :=
begin
  refine finset.induction_on s _ _,
  { simp, },
  { assume a s has ih,
    simp only [finset.sum_insert has],
    rw [ih, supr_add_supr_of_monotone (hf a)],
    assume i j h,
    exact (finset.sum_le_sum $ assume a ha, hf a h) }
end

lemma mul_Sup {s : set ℝ≥0∞} {a : ℝ≥0∞} : a * Sup s = ⨆i∈s, a * i :=
begin
  by_cases hs : ∀x∈s, x = (0:ℝ≥0∞),
  { have h₁ : Sup s = 0 := (bot_unique $ Sup_le $ assume a ha, (hs a ha).symm ▸ le_refl 0),
    have h₂ : (⨆i ∈ s, a * i) = 0 :=
      (bot_unique $ supr_le $ assume a, supr_le $ assume ha, by simp [hs a ha]),
    rw [h₁, h₂, mul_zero] },
  { simp only [not_forall] at hs,
    rcases hs with ⟨x, hx, hx0⟩,
    have s₁ : Sup s ≠ 0 :=
      pos_iff_ne_zero.1 (lt_of_lt_of_le (pos_iff_ne_zero.2 hx0) (le_Sup hx)),
    have : Sup ((λb, a * b) '' s) = a * Sup s :=
      is_lub.Sup_eq ((is_lub_Sup s).is_lub_of_tendsto
        (assume x _ y _ h, mul_le_mul_left' h _)
        ⟨x, hx⟩
        (ennreal.tendsto.const_mul (tendsto_id' inf_le_left) (or.inl s₁))),
    rw [this.symm, Sup_image] }
end

lemma mul_supr {ι : Sort*} {f : ι → ℝ≥0∞} {a : ℝ≥0∞} : a * supr f = ⨆i, a * f i :=
by rw [← Sup_range, mul_Sup, supr_range]

lemma supr_mul {ι : Sort*} {f : ι → ℝ≥0∞} {a : ℝ≥0∞} : supr f * a = ⨆i, f i * a :=
by rw [mul_comm, mul_supr]; congr; funext; rw [mul_comm]

lemma supr_div {ι : Sort*} {f : ι → ℝ≥0∞} {a : ℝ≥0∞} : supr f / a = ⨆i, f i / a :=
supr_mul

protected lemma tendsto_coe_sub : ∀{b:ℝ≥0∞}, tendsto (λb:ℝ≥0∞, ↑r - b) (𝓝 b) (𝓝 (↑r - b)) :=
begin
  refine forall_ennreal.2 ⟨λ a, _, _⟩,
  { simp [@nhds_coe a, tendsto_map'_iff, (∘), tendsto_coe, ← with_top.coe_sub],
    exact tendsto_const_nhds.sub tendsto_id },
  simp,
  exact (tendsto.congr' (mem_of_superset (lt_mem_nhds $ @coe_lt_top r) $
    by simp [le_of_lt] {contextual := tt})) tendsto_const_nhds
end

lemma sub_supr {ι : Sort*} [nonempty ι] {b : ι → ℝ≥0∞} (hr : a < ⊤) :
  a - (⨆i, b i) = (⨅i, a - b i) :=
let ⟨r, eq, _⟩ := lt_iff_exists_coe.mp hr in
have Inf ((λb, ↑r - b) '' range b) = ↑r - (⨆i, b i),
  from is_glb.Inf_eq $ is_lub_supr.is_glb_of_tendsto
    (assume x _ y _, tsub_le_tsub (le_refl (r : ℝ≥0∞)))
    (range_nonempty _)
    (ennreal.tendsto_coe_sub.comp (tendsto_id' inf_le_left)),
by rw [eq, ←this]; simp [Inf_image, infi_range, -mem_range]; exact le_rfl

lemma exists_countable_dense_no_zero_top :
  ∃ (s : set ℝ≥0∞), countable s ∧ dense s ∧ 0 ∉ s ∧ ∞ ∉ s :=
begin
  obtain ⟨s, s_count, s_dense, hs⟩ : ∃ s : set ℝ≥0∞, countable s ∧ dense s ∧
    (∀ x, is_bot x → x ∉ s) ∧ (∀ x, is_top x → x ∉ s) := exists_countable_dense_no_bot_top ℝ≥0∞,
  exact ⟨s, s_count, s_dense, λ h, hs.1 0 (by simp) h, λ h, hs.2 ∞ (by simp) h⟩,
end

end topological_space

section tsum

variables {f g : α → ℝ≥0∞}

@[norm_cast] protected lemma has_sum_coe {f : α → ℝ≥0} {r : ℝ≥0} :
  has_sum (λa, (f a : ℝ≥0∞)) ↑r ↔ has_sum f r :=
have (λs:finset α, ∑ a in s, ↑(f a)) = (coe : ℝ≥0 → ℝ≥0∞) ∘ (λs:finset α, ∑ a in s, f a),
  from funext $ assume s, ennreal.coe_finset_sum.symm,
by unfold has_sum; rw [this, tendsto_coe]

protected lemma tsum_coe_eq {f : α → ℝ≥0} (h : has_sum f r) : ∑'a, (f a : ℝ≥0∞) = r :=
(ennreal.has_sum_coe.2 h).tsum_eq

protected lemma coe_tsum {f : α → ℝ≥0} : summable f → ↑(tsum f) = ∑'a, (f a : ℝ≥0∞)
| ⟨r, hr⟩ := by rw [hr.tsum_eq, ennreal.tsum_coe_eq hr]

protected lemma has_sum : has_sum f (⨆s:finset α, ∑ a in s, f a) :=
tendsto_at_top_supr $ λ s t, finset.sum_le_sum_of_subset

@[simp] protected lemma summable : summable f := ⟨_, ennreal.has_sum⟩

lemma tsum_coe_ne_top_iff_summable {f : β → ℝ≥0} :
  ∑' b, (f b:ℝ≥0∞) ≠ ∞ ↔ summable f :=
begin
  refine ⟨λ h, _, λ h, ennreal.coe_tsum h ▸ ennreal.coe_ne_top⟩,
  lift (∑' b, (f b:ℝ≥0∞)) to ℝ≥0 using h with a ha,
  refine ⟨a, ennreal.has_sum_coe.1 _⟩,
  rw ha,
  exact ennreal.summable.has_sum
end

protected lemma tsum_eq_supr_sum : ∑'a, f a = (⨆s:finset α, ∑ a in s, f a) :=
ennreal.has_sum.tsum_eq

protected lemma tsum_eq_supr_sum' {ι : Type*} (s : ι → finset α) (hs : ∀ t, ∃ i, t ⊆ s i) :
  ∑' a, f a = ⨆ i, ∑ a in s i, f a :=
begin
  rw [ennreal.tsum_eq_supr_sum],
  symmetry,
  change (⨆i:ι, (λ t : finset α, ∑ a in t, f a) (s i)) = ⨆s:finset α, ∑ a in s, f a,
  exact (finset.sum_mono_set f).supr_comp_eq hs
end

protected lemma tsum_sigma {β : α → Type*} (f : Πa, β a → ℝ≥0∞) :
  ∑'p:Σa, β a, f p.1 p.2 = ∑'a b, f a b :=
tsum_sigma' (assume b, ennreal.summable) ennreal.summable

protected lemma tsum_sigma' {β : α → Type*} (f : (Σ a, β a) → ℝ≥0∞) :
  ∑'p:(Σa, β a), f p = ∑'a b, f ⟨a, b⟩ :=
tsum_sigma' (assume b, ennreal.summable) ennreal.summable

protected lemma tsum_prod {f : α → β → ℝ≥0∞} : ∑'p:α×β, f p.1 p.2 = ∑'a, ∑'b, f a b :=
tsum_prod' ennreal.summable $ λ _, ennreal.summable

protected lemma tsum_comm {f : α → β → ℝ≥0∞} : ∑'a, ∑'b, f a b = ∑'b, ∑'a, f a b :=
tsum_comm' ennreal.summable (λ _, ennreal.summable) (λ _, ennreal.summable)

protected lemma tsum_add : ∑'a, (f a + g a) = (∑'a, f a) + (∑'a, g a) :=
tsum_add ennreal.summable ennreal.summable

protected lemma tsum_le_tsum (h : ∀a, f a ≤ g a) : ∑'a, f a ≤ ∑'a, g a :=
tsum_le_tsum h ennreal.summable ennreal.summable

protected lemma sum_le_tsum {f : α → ℝ≥0∞} (s : finset α) : ∑ x in s, f x ≤ ∑' x, f x :=
sum_le_tsum s (λ x hx, zero_le _) ennreal.summable

protected lemma tsum_eq_supr_nat' {f : ℕ → ℝ≥0∞} {N : ℕ → ℕ} (hN : tendsto N at_top at_top) :
  ∑'i:ℕ, f i = (⨆i:ℕ, ∑ a in finset.range (N i), f a) :=
ennreal.tsum_eq_supr_sum' _ $ λ t,
  let ⟨n, hn⟩    := t.exists_nat_subset_range,
      ⟨k, _, hk⟩ := exists_le_of_tendsto_at_top hN 0 n in
  ⟨k, finset.subset.trans hn (finset.range_mono hk)⟩

protected lemma tsum_eq_supr_nat {f : ℕ → ℝ≥0∞} :
  ∑'i:ℕ, f i = (⨆i:ℕ, ∑ a in finset.range i, f a) :=
ennreal.tsum_eq_supr_sum' _ finset.exists_nat_subset_range

protected lemma tsum_eq_liminf_sum_nat {f : ℕ → ℝ≥0∞} :
  ∑' i, f i = filter.at_top.liminf (λ n, ∑ i in finset.range n, f i) :=
begin
  rw [ennreal.tsum_eq_supr_nat, filter.liminf_eq_supr_infi_of_nat],
  congr,
  refine funext (λ n, le_antisymm _ _),
  { refine le_binfi (λ i hi, finset.sum_le_sum_of_subset_of_nonneg _ (λ _ _ _, zero_le _)),
    simpa only [finset.range_subset, add_le_add_iff_right] using hi, },
  { refine le_trans (infi_le _ n) _,
    simp [le_refl n, le_refl ((finset.range n).sum f)], },
end

protected lemma le_tsum (a : α) : f a ≤ ∑'a, f a :=
le_tsum' ennreal.summable a

@[simp] protected lemma tsum_eq_zero : ∑' i, f i = 0 ↔ ∀ i, f i = 0 :=
⟨λ h i, nonpos_iff_eq_zero.1 $ h ▸ ennreal.le_tsum i, λ h, by simp [h]⟩

protected lemma tsum_eq_top_of_eq_top : (∃ a, f a = ∞) → ∑' a, f a = ∞
| ⟨a, ha⟩ := top_unique $ ha ▸ ennreal.le_tsum a

@[simp] protected lemma tsum_top [nonempty α] : ∑' a : α, ∞ = ∞ :=
let ⟨a⟩ := ‹nonempty α› in ennreal.tsum_eq_top_of_eq_top ⟨a, rfl⟩

lemma tsum_const_eq_top_of_ne_zero {α : Type*} [infinite α] {c : ℝ≥0∞} (hc : c ≠ 0) :
  (∑' (a : α), c) = ∞ :=
begin
  have A : tendsto (λ (n : ℕ), (n : ℝ≥0∞) * c) at_top (𝓝 (∞ * c)),
  { apply ennreal.tendsto.mul_const tendsto_nat_nhds_top,
    simp only [true_or, top_ne_zero, ne.def, not_false_iff] },
  have B : ∀ (n : ℕ), (n : ℝ≥0∞) * c ≤ (∑' (a : α), c),
  { assume n,
    rcases infinite.exists_subset_card_eq α n with ⟨s, hs⟩,
    simpa [hs] using @ennreal.sum_le_tsum α (λ i, c) s },
  simpa [hc] using le_of_tendsto' A B,
end

protected lemma ne_top_of_tsum_ne_top (h : ∑' a, f a ≠ ∞) (a : α) : f a ≠ ∞ :=
λ ha, h $ ennreal.tsum_eq_top_of_eq_top ⟨a, ha⟩

protected lemma tsum_mul_left : ∑'i, a * f i = a * ∑'i, f i :=
if h : ∀i, f i = 0 then by simp [h] else
let ⟨i, (hi : f i ≠ 0)⟩ := not_forall.mp h in
have sum_ne_0 : ∑'i, f i ≠ 0, from ne_of_gt $
  calc 0 < f i : lt_of_le_of_ne (zero_le _) hi.symm
    ... ≤ ∑'i, f i : ennreal.le_tsum _,
have tendsto (λs:finset α, ∑ j in s, a * f j) at_top (𝓝 (a * ∑'i, f i)),
  by rw [← show (*) a ∘ (λs:finset α, ∑ j in s, f j) = λs, ∑ j in s, a * f j,
         from funext $ λ s, finset.mul_sum];
  exact ennreal.tendsto.const_mul ennreal.summable.has_sum (or.inl sum_ne_0),
has_sum.tsum_eq this

protected lemma tsum_mul_right : (∑'i, f i * a) = (∑'i, f i) * a :=
by simp [mul_comm, ennreal.tsum_mul_left]

@[simp] lemma tsum_supr_eq {α : Type*} (a : α) {f : α → ℝ≥0∞} :
  ∑'b:α, (⨆ (h : a = b), f b) = f a :=
le_antisymm
  (by rw [ennreal.tsum_eq_supr_sum]; exact supr_le (assume s,
    calc (∑ b in s, ⨆ (h : a = b), f b) ≤ ∑ b in {a}, ⨆ (h : a = b), f b :
        finset.sum_le_sum_of_ne_zero $ assume b _ hb,
          suffices a = b, by simpa using this.symm,
          classical.by_contradiction $ assume h,
            by simpa [h] using hb
      ... = f a : by simp))
  (calc f a ≤ (⨆ (h : a = a), f a) : le_supr (λh:a=a, f a) rfl
    ... ≤ (∑'b:α, ⨆ (h : a = b), f b) : ennreal.le_tsum _)

lemma has_sum_iff_tendsto_nat {f : ℕ → ℝ≥0∞} (r : ℝ≥0∞) :
  has_sum f r ↔ tendsto (λn:ℕ, ∑ i in finset.range n, f i) at_top (𝓝 r) :=
begin
  refine ⟨has_sum.tendsto_sum_nat, assume h, _⟩,
  rw [← supr_eq_of_tendsto _ h, ← ennreal.tsum_eq_supr_nat],
  { exact ennreal.summable.has_sum },
  { exact assume s t hst, finset.sum_le_sum_of_subset (finset.range_subset.2 hst) }
end

lemma tendsto_nat_tsum (f : ℕ → ℝ≥0∞) :
  tendsto (λn:ℕ, ∑ i in finset.range n, f i) at_top (𝓝 (∑' n, f n)) :=
by { rw ← has_sum_iff_tendsto_nat, exact ennreal.summable.has_sum }

lemma to_nnreal_apply_of_tsum_ne_top {α : Type*} {f : α → ℝ≥0∞} (hf : ∑' i, f i ≠ ∞) (x : α) :
  (((ennreal.to_nnreal ∘ f) x : ℝ≥0) : ℝ≥0∞) = f x :=
coe_to_nnreal $ ennreal.ne_top_of_tsum_ne_top hf _

lemma summable_to_nnreal_of_tsum_ne_top {α : Type*} {f : α → ℝ≥0∞} (hf : ∑' i, f i ≠ ∞) :
  summable (ennreal.to_nnreal ∘ f) :=
by simpa only [←tsum_coe_ne_top_iff_summable, to_nnreal_apply_of_tsum_ne_top hf] using hf

lemma tendsto_cofinite_zero_of_tsum_ne_top {α} {f : α → ℝ≥0∞} (hf : ∑' x, f x ≠ ∞) :
  tendsto f cofinite (𝓝 0) :=
begin
  have f_ne_top : ∀ n, f n ≠ ∞, from ennreal.ne_top_of_tsum_ne_top hf,
  have h_f_coe : f = λ n, ((f n).to_nnreal : ennreal),
    from funext (λ n, (coe_to_nnreal (f_ne_top n)).symm),
  rw [h_f_coe, ←@coe_zero, tendsto_coe],
  exact nnreal.tendsto_cofinite_zero_of_summable (summable_to_nnreal_of_tsum_ne_top hf),
end

lemma tendsto_at_top_zero_of_tsum_ne_top {f : ℕ → ℝ≥0∞} (hf : ∑' x, f x ≠ ∞) :
  tendsto f at_top (𝓝 0) :=
by { rw ←nat.cofinite_eq_at_top, exact tendsto_cofinite_zero_of_tsum_ne_top hf }

/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
lemma tendsto_tsum_compl_at_top_zero {α : Type*} {f : α → ℝ≥0∞} (hf : ∑' x, f x ≠ ∞) :
  tendsto (λ (s : finset α), ∑' b : {x // x ∉ s}, f b) at_top (𝓝 0) :=
begin
  lift f to α → ℝ≥0 using ennreal.ne_top_of_tsum_ne_top hf,
  convert ennreal.tendsto_coe.2 (nnreal.tendsto_tsum_compl_at_top_zero f),
  ext1 s,
  rw ennreal.coe_tsum,
  exact nnreal.summable_comp_injective (tsum_coe_ne_top_iff_summable.1 hf) subtype.coe_injective
end

protected lemma tsum_apply {ι α : Type*} {f : ι → α → ℝ≥0∞} {x : α} :
  (∑' i, f i) x = ∑' i, f i x :=
tsum_apply $ pi.summable.mpr $ λ _, ennreal.summable

lemma tsum_sub {f : ℕ → ℝ≥0∞} {g : ℕ → ℝ≥0∞} (h₁ : ∑' i, g i ≠ ∞) (h₂ : g ≤ f) :
  ∑' i, (f i - g i) = (∑' i, f i) - (∑' i, g i) :=
begin
  have h₃: ∑' i, (f i - g i) = ∑' i, (f i - g i + g i) - ∑' i, g i,
  { rw [ennreal.tsum_add, add_sub_self h₁]},
  have h₄:(λ i, (f i - g i) + (g i)) = f,
  { ext n, rw tsub_add_cancel_of_le (h₂ n)},
  rw h₄ at h₃, apply h₃,
end

lemma tsum_mono_subtype (f : α → ℝ≥0∞) {s t : set α} (h : s ⊆ t) :
  ∑' (x : s), f x ≤ ∑' (x : t), f x :=
begin
  simp only [tsum_subtype],
  apply ennreal.tsum_le_tsum,
  assume x,
  split_ifs,
  { exact le_rfl },
  { exact (h_2 (h h_1)).elim },
  { exact zero_le _ },
  { exact le_rfl }
end

lemma tsum_union_le (f : α → ℝ≥0∞) (s t : set α) :
  ∑' (x : s ∪ t), f x ≤ ∑' (x : s), f x + ∑' (x : t), f x :=
calc ∑' (x : s ∪ t), f x = ∑' (x : s ∪ (t \ s)), f x :
  by { apply tsum_congr_subtype, rw union_diff_self }
... = ∑' (x : s), f x + ∑' (x : t \ s), f x :
  tsum_union_disjoint disjoint_diff ennreal.summable ennreal.summable
... ≤ ∑' (x : s), f x + ∑' (x : t), f x :
  add_le_add le_rfl (tsum_mono_subtype _ (diff_subset _ _))

lemma tsum_bUnion_le {ι : Type*} (f : α → ℝ≥0∞) (s : finset ι) (t : ι → set α) :
  ∑' (x : ⋃ (i ∈ s), t i), f x ≤ ∑ i in s, ∑' (x : t i), f x :=
begin
  classical,
  induction s using finset.induction_on with i s hi ihs h, { simp },
  have : (⋃ (j ∈ insert i s), t j) = t i ∪ (⋃ (j ∈ s), t j), by simp,
  rw tsum_congr_subtype f this,
  calc ∑' (x : (t i ∪ (⋃ (j ∈ s), t j))), f x ≤
  ∑' (x : t i), f x + ∑' (x : ⋃ (j ∈ s), t j), f x : tsum_union_le _ _ _
  ... ≤ ∑' (x : t i), f x + ∑ i in s, ∑' (x : t i), f x : add_le_add le_rfl ihs
  ... = ∑ j in insert i s, ∑' (x : t j), f x : (finset.sum_insert hi).symm
end

lemma tsum_Union_le {ι : Type*} [fintype ι] (f : α → ℝ≥0∞) (t : ι → set α) :
  ∑' (x : ⋃ i, t i), f x ≤ ∑ i, ∑' (x : t i), f x :=
begin
  classical,
  have : (⋃ i, t i) = (⋃ (i ∈ (finset.univ : finset ι)), t i), by simp,
  rw tsum_congr_subtype f this,
  exact tsum_bUnion_le _ _ _
end

end tsum

lemma tendsto_to_real_iff {ι} {fi : filter ι} {f : ι → ℝ≥0∞} (hf : ∀ i, f i ≠ ∞) {x : ℝ≥0∞}
  (hx : x ≠ ∞) :
  fi.tendsto (λ n, (f n).to_real) (𝓝 x.to_real) ↔ fi.tendsto f (𝓝 x) :=
begin
  refine ⟨λ h, _, λ h, tendsto.comp (ennreal.tendsto_to_real hx) h⟩,
  have h_eq : f = (λ n, ennreal.of_real (f n).to_real),
    by { ext1 n, rw ennreal.of_real_to_real (hf n), },
  rw [h_eq, ← ennreal.of_real_to_real hx],
  exact ennreal.tendsto_of_real h,
end

lemma tsum_coe_ne_top_iff_summable_coe {f : α → ℝ≥0} :
  ∑' a, (f a : ℝ≥0∞) ≠ ∞ ↔ summable (λ a, (f a : ℝ)) :=
begin
  rw nnreal.summable_coe,
  exact tsum_coe_ne_top_iff_summable,
end

lemma tsum_coe_eq_top_iff_not_summable_coe {f : α → ℝ≥0} :
  ∑' a, (f a : ℝ≥0∞) = ∞ ↔ ¬ summable (λ a, (f a : ℝ)) :=
begin
  rw [← @not_not (∑' a, ↑(f a) = ⊤)],
  exact not_congr tsum_coe_ne_top_iff_summable_coe
end

lemma summable_to_real {f : α → ℝ≥0∞} (hsum : ∑' x, f x ≠ ∞) :
  summable (λ x, (f x).to_real) :=
begin
  lift f to α → ℝ≥0 using ennreal.ne_top_of_tsum_ne_top hsum,
  rwa ennreal.tsum_coe_ne_top_iff_summable_coe at hsum,
end

end ennreal

namespace nnreal

open_locale nnreal

lemma tsum_eq_to_nnreal_tsum {f : β → ℝ≥0} :
  (∑' b, f b) = (∑' b, (f b : ℝ≥0∞)).to_nnreal :=
begin
  by_cases h : summable f,
  { rw [← ennreal.coe_tsum h, ennreal.to_nnreal_coe] },
  { have A := tsum_eq_zero_of_not_summable h,
    simp only [← ennreal.tsum_coe_ne_top_iff_summable, not_not] at h,
    simp only [h, ennreal.top_to_nnreal, A] }
end

/-- Comparison test of convergence of `ℝ≥0`-valued series. -/
lemma exists_le_has_sum_of_le {f g : β → ℝ≥0} {r : ℝ≥0}
  (hgf : ∀b, g b ≤ f b) (hfr : has_sum f r) : ∃p≤r, has_sum g p :=
have ∑'b, (g b : ℝ≥0∞) ≤ r,
begin
  refine has_sum_le (assume b, _) ennreal.summable.has_sum (ennreal.has_sum_coe.2 hfr),
  exact ennreal.coe_le_coe.2 (hgf _)
end,
let ⟨p, eq, hpr⟩ := ennreal.le_coe_iff.1 this in
⟨p, hpr, ennreal.has_sum_coe.1 $ eq ▸ ennreal.summable.has_sum⟩

/-- Comparison test of convergence of `ℝ≥0`-valued series. -/
lemma summable_of_le {f g : β → ℝ≥0} (hgf : ∀b, g b ≤ f b) : summable f → summable g
| ⟨r, hfr⟩ := let ⟨p, _, hp⟩ := exists_le_has_sum_of_le hgf hfr in hp.summable

/-- A series of non-negative real numbers converges to `r` in the sense of `has_sum` if and only if
the sequence of partial sum converges to `r`. -/
lemma has_sum_iff_tendsto_nat {f : ℕ → ℝ≥0} {r : ℝ≥0} :
  has_sum f r ↔ tendsto (λn:ℕ, ∑ i in finset.range n, f i) at_top (𝓝 r) :=
begin
  rw [← ennreal.has_sum_coe, ennreal.has_sum_iff_tendsto_nat],
  simp only [ennreal.coe_finset_sum.symm],
  exact ennreal.tendsto_coe
end

lemma not_summable_iff_tendsto_nat_at_top {f : ℕ → ℝ≥0} :
  ¬ summable f ↔ tendsto (λ n : ℕ, ∑ i in finset.range n, f i) at_top at_top :=
begin
  split,
  { intros h,
    refine ((tendsto_of_monotone _).resolve_right h).comp _,
    exacts [finset.sum_mono_set _, tendsto_finset_range] },
  { rintros hnat ⟨r, hr⟩,
    exact not_tendsto_nhds_of_tendsto_at_top hnat _ (has_sum_iff_tendsto_nat.1 hr) }
end

lemma summable_iff_not_tendsto_nat_at_top {f : ℕ → ℝ≥0} :
  summable f ↔ ¬ tendsto (λ n : ℕ, ∑ i in finset.range n, f i) at_top at_top :=
by rw [← not_iff_not, not_not, not_summable_iff_tendsto_nat_at_top]

lemma summable_of_sum_range_le {f : ℕ → ℝ≥0} {c : ℝ≥0}
  (h : ∀ n, ∑ i in finset.range n, f i ≤ c) : summable f :=
begin
  apply summable_iff_not_tendsto_nat_at_top.2 (λ H, _),
  rcases exists_lt_of_tendsto_at_top H 0 c with ⟨n, -, hn⟩,
  exact lt_irrefl _ (hn.trans_le (h n)),
end

lemma tsum_le_of_sum_range_le {f : ℕ → ℝ≥0} {c : ℝ≥0}
  (h : ∀ n, ∑ i in finset.range n, f i ≤ c) : ∑' n, f n ≤ c :=
le_of_tendsto' (has_sum_iff_tendsto_nat.1 (summable_of_sum_range_le h).has_sum) h

lemma tsum_comp_le_tsum_of_inj {β : Type*} {f : α → ℝ≥0} (hf : summable f)
  {i : β → α} (hi : function.injective i) : ∑' x, f (i x) ≤ ∑' x, f x :=
tsum_le_tsum_of_inj i hi (λ c hc, zero_le _) (λ b, le_refl _) (summable_comp_injective hf hi) hf

lemma summable_sigma {β : Π x : α, Type*} {f : (Σ x, β x) → ℝ≥0} :
  summable f ↔ (∀ x, summable (λ y, f ⟨x, y⟩)) ∧ summable (λ x, ∑' y, f ⟨x, y⟩) :=
begin
  split,
  { simp only [← nnreal.summable_coe, nnreal.coe_tsum],
    exact λ h, ⟨h.sigma_factor, h.sigma⟩ },
  { rintro ⟨h₁, h₂⟩,
    simpa only [← ennreal.tsum_coe_ne_top_iff_summable, ennreal.tsum_sigma', ennreal.coe_tsum, h₁]
      using h₂ }
end

lemma indicator_summable {f : α → ℝ≥0} (hf : summable f) (s : set α) :
  summable (s.indicator f) :=
begin
  refine nnreal.summable_of_le (λ a, le_trans (le_of_eq (s.indicator_apply f a)) _) hf,
  split_ifs,
  exact le_refl (f a),
  exact zero_le_coe,
end

lemma tsum_indicator_ne_zero {f : α → ℝ≥0} (hf : summable f) {s : set α} (h : ∃ a ∈ s, f a ≠ 0) :
  ∑' x, (s.indicator f) x ≠ 0 :=
λ h', let ⟨a, ha, hap⟩ := h in
  hap (trans (set.indicator_apply_eq_self.mpr (absurd ha)).symm
    (((tsum_eq_zero_iff (indicator_summable hf s)).1 h') a))

open finset

/-- For `f : ℕ → ℝ≥0`, then `∑' k, f (k + i)` tends to zero. This does not require a summability
assumption on `f`, as otherwise all sums are zero. -/
lemma tendsto_sum_nat_add (f : ℕ → ℝ≥0) : tendsto (λ i, ∑' k, f (k + i)) at_top (𝓝 0) :=
begin
  rw ← tendsto_coe,
  convert tendsto_sum_nat_add (λ i, (f i : ℝ)),
  norm_cast,
end

lemma has_sum_lt {f g : α → ℝ≥0} {sf sg : ℝ≥0} {i : α} (h : ∀ (a : α), f a ≤ g a) (hi : f i < g i)
  (hf : has_sum f sf) (hg : has_sum g sg) : sf < sg :=
begin
  have A : ∀ (a : α), (f a : ℝ) ≤ g a := λ a, nnreal.coe_le_coe.2 (h a),
  have : (sf : ℝ) < sg :=
    has_sum_lt A (nnreal.coe_lt_coe.2 hi) (has_sum_coe.2 hf) (has_sum_coe.2 hg),
  exact nnreal.coe_lt_coe.1 this
end

@[mono] lemma has_sum_strict_mono
  {f g : α → ℝ≥0} {sf sg : ℝ≥0} (hf : has_sum f sf) (hg : has_sum g sg) (h : f < g) : sf < sg :=
let ⟨hle, i, hi⟩ := pi.lt_def.mp h in has_sum_lt hle hi hf hg

lemma tsum_lt_tsum {f g : α → ℝ≥0} {i : α} (h : ∀ (a : α), f a ≤ g a) (hi : f i < g i)
  (hg : summable g) : ∑' n, f n < ∑' n, g n :=
has_sum_lt h hi (summable_of_le h hg).has_sum hg.has_sum

@[mono] lemma tsum_strict_mono {f g : α → ℝ≥0} (hg : summable g) (h : f < g) :
  ∑' n, f n < ∑' n, g n :=
let ⟨hle, i, hi⟩ := pi.lt_def.mp h in tsum_lt_tsum hle hi hg

lemma tsum_pos {g : α → ℝ≥0} (hg : summable g) (i : α) (hi : 0 < g i) :
  0 < ∑' b, g b :=
by { rw ← tsum_zero, exact tsum_lt_tsum (λ a, zero_le _) hi hg }

end nnreal

namespace ennreal

lemma tsum_to_real_eq
  {f : α → ℝ≥0∞} (hf : ∀ a, f a ≠ ∞) :
  (∑' a, f a).to_real = ∑' a, (f a).to_real :=
begin
  lift f to α → ℝ≥0 using hf,
  have : (∑' (a : α), (f a : ℝ≥0∞)).to_real =
    ((∑' (a : α), (f a : ℝ≥0∞)).to_nnreal : ℝ≥0∞).to_real,
  { rw [ennreal.coe_to_real], refl },
  rw [this, ← nnreal.tsum_eq_to_nnreal_tsum, ennreal.coe_to_real],
  exact nnreal.coe_tsum
end

lemma tendsto_sum_nat_add (f : ℕ → ℝ≥0∞) (hf : ∑' i, f i ≠ ∞) :
  tendsto (λ i, ∑' k, f (k + i)) at_top (𝓝 0) :=
begin
  lift f to ℕ → ℝ≥0 using ennreal.ne_top_of_tsum_ne_top hf,
  replace hf : summable f := tsum_coe_ne_top_iff_summable.1 hf,
  simp only [← ennreal.coe_tsum, nnreal.summable_nat_add _ hf, ← ennreal.coe_zero],
  exact_mod_cast nnreal.tendsto_sum_nat_add f
end

end ennreal

lemma tsum_comp_le_tsum_of_inj {β : Type*} {f : α → ℝ} (hf : summable f) (hn : ∀ a, 0 ≤ f a)
  {i : β → α} (hi : function.injective i) : tsum (f ∘ i) ≤ tsum f :=
begin
  lift f to α → ℝ≥0 using hn,
  rw nnreal.summable_coe at hf,
  simpa only [(∘), ← nnreal.coe_tsum] using nnreal.tsum_comp_le_tsum_of_inj hf hi
end

/-- Comparison test of convergence of series of non-negative real numbers. -/
lemma summable_of_nonneg_of_le {f g : β → ℝ}
  (hg : ∀b, 0 ≤ g b) (hgf : ∀b, g b ≤ f b) (hf : summable f) : summable g :=
begin
  lift f to β → ℝ≥0 using λ b, (hg b).trans (hgf b),
  lift g to β → ℝ≥0 using hg,
  rw nnreal.summable_coe at hf ⊢,
  exact nnreal.summable_of_le (λ b, nnreal.coe_le_coe.1 (hgf b)) hf
end

/-- A series of non-negative real numbers converges to `r` in the sense of `has_sum` if and only if
the sequence of partial sum converges to `r`. -/
lemma has_sum_iff_tendsto_nat_of_nonneg {f : ℕ → ℝ} (hf : ∀i, 0 ≤ f i) (r : ℝ) :
  has_sum f r ↔ tendsto (λ n : ℕ, ∑ i in finset.range n, f i) at_top (𝓝 r) :=
begin
  lift f to ℕ → ℝ≥0 using hf,
  simp only [has_sum, ← nnreal.coe_sum, nnreal.tendsto_coe'],
  exact exists_congr (λ hr, nnreal.has_sum_iff_tendsto_nat)
end

lemma ennreal.of_real_tsum_of_nonneg {f : α → ℝ} (hf_nonneg : ∀ n, 0 ≤ f n) (hf : summable f) :
  ennreal.of_real (∑' n, f n) = ∑' n, ennreal.of_real (f n) :=
by simp_rw [ennreal.of_real, ennreal.tsum_coe_eq (nnreal.has_sum_of_real_of_nonneg hf_nonneg hf)]

lemma not_summable_iff_tendsto_nat_at_top_of_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
  ¬ summable f ↔ tendsto (λ n : ℕ, ∑ i in finset.range n, f i) at_top at_top :=
begin
  lift f to ℕ → ℝ≥0 using hf,
  exact_mod_cast nnreal.not_summable_iff_tendsto_nat_at_top
end

lemma summable_iff_not_tendsto_nat_at_top_of_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
  summable f ↔ ¬ tendsto (λ n : ℕ, ∑ i in finset.range n, f i) at_top at_top :=
by rw [← not_iff_not, not_not, not_summable_iff_tendsto_nat_at_top_of_nonneg hf]

lemma summable_sigma_of_nonneg {β : Π x : α, Type*} {f : (Σ x, β x) → ℝ} (hf : ∀ x, 0 ≤ f x) :
  summable f ↔ (∀ x, summable (λ y, f ⟨x, y⟩)) ∧ summable (λ x, ∑' y, f ⟨x, y⟩) :=
by { lift f to (Σ x, β x) → ℝ≥0 using hf, exact_mod_cast nnreal.summable_sigma }

lemma summable_of_sum_le {ι : Type*} {f : ι → ℝ} {c : ℝ} (hf : 0 ≤ f)
  (h : ∀ u : finset ι, ∑ x in u, f x ≤ c) :
  summable f :=
⟨ ⨆ u : finset ι, ∑ x in u, f x,
  tendsto_at_top_csupr (finset.sum_mono_set_of_nonneg hf) ⟨c, λ y ⟨u, hu⟩, hu ▸ h u⟩ ⟩

lemma summable_of_sum_range_le {f : ℕ → ℝ} {c : ℝ} (hf : ∀ n, 0 ≤ f n)
  (h : ∀ n, ∑ i in finset.range n, f i ≤ c) : summable f :=
begin
  apply (summable_iff_not_tendsto_nat_at_top_of_nonneg hf).2 (λ H, _),
  rcases exists_lt_of_tendsto_at_top H 0 c with ⟨n, -, hn⟩,
  exact lt_irrefl _ (hn.trans_le (h n)),
end

lemma tsum_le_of_sum_range_le {f : ℕ → ℝ} {c : ℝ} (hf : ∀ n, 0 ≤ f n)
  (h : ∀ n, ∑ i in finset.range n, f i ≤ c) : ∑' n, f n ≤ c :=
le_of_tendsto' ((has_sum_iff_tendsto_nat_of_nonneg hf _).1
  (summable_of_sum_range_le hf h).has_sum) h

/-- If a sequence `f` with non-negative terms is dominated by a sequence `g` with summable
series and at least one term of `f` is strictly smaller than the corresponding term in `g`,
then the series of `f` is strictly smaller than the series of `g`. -/
lemma tsum_lt_tsum_of_nonneg {i : ℕ} {f g : ℕ → ℝ}
  (h0 : ∀ (b : ℕ), 0 ≤ f b) (h : ∀ (b : ℕ), f b ≤ g b) (hi : f i < g i) (hg : summable g) :
  ∑' n, f n < ∑' n, g n :=
tsum_lt_tsum h hi (summable_of_nonneg_of_le h0 h hg) hg

section
variables [emetric_space β]
open ennreal filter emetric

/-- In an emetric ball, the distance between points is everywhere finite -/
lemma edist_ne_top_of_mem_ball {a : β} {r : ℝ≥0∞} (x y : ball a r) : edist x.1 y.1 ≠ ⊤ :=
lt_top_iff_ne_top.1 $
calc edist x y ≤ edist a x + edist a y : edist_triangle_left x.1 y.1 a
  ... < r + r : by rw [edist_comm a x, edist_comm a y]; exact add_lt_add x.2 y.2
  ... ≤ ⊤ : le_top

/-- Each ball in an extended metric space gives us a metric space, as the edist
is everywhere finite. -/
def metric_space_emetric_ball (a : β) (r : ℝ≥0∞) : metric_space (ball a r) :=
emetric_space.to_metric_space edist_ne_top_of_mem_ball

local attribute [instance] metric_space_emetric_ball

lemma nhds_eq_nhds_emetric_ball (a x : β) (r : ℝ≥0∞) (h : x ∈ ball a r) :
  𝓝 x = map (coe : ball a r → β) (𝓝 ⟨x, h⟩) :=
(map_nhds_subtype_coe_eq _ $ is_open.mem_nhds emetric.is_open_ball h).symm
end

section
variable [pseudo_emetric_space α]
open emetric

lemma tendsto_iff_edist_tendsto_0 {l : filter β} {f : β → α} {y : α} :
  tendsto f l (𝓝 y) ↔ tendsto (λ x, edist (f x) y) l (𝓝 0) :=
by simp only [emetric.nhds_basis_eball.tendsto_right_iff, emetric.mem_ball,
  @tendsto_order ℝ≥0∞ β _ _, forall_prop_of_false ennreal.not_lt_zero, forall_const, true_and]

/-- Yet another metric characterization of Cauchy sequences on integers. This one is often the
most efficient. -/
lemma emetric.cauchy_seq_iff_le_tendsto_0 [nonempty β] [semilattice_sup β] {s : β → α} :
  cauchy_seq s ↔ (∃ (b: β → ℝ≥0∞), (∀ n m N : β, N ≤ n → N ≤ m → edist (s n) (s m) ≤ b N)
                    ∧ (tendsto b at_top (𝓝 0))) :=
⟨begin
  assume hs,
  rw emetric.cauchy_seq_iff at hs,
  /- `s` is Cauchy sequence. The sequence `b` will be constructed by taking
  the supremum of the distances between `s n` and `s m` for `n m ≥ N`-/
  let b := λN, Sup ((λ(p : β × β), edist (s p.1) (s p.2))''{p | p.1 ≥ N ∧ p.2 ≥ N}),
  --Prove that it bounds the distances of points in the Cauchy sequence
  have C : ∀ n m N, N ≤ n → N ≤ m → edist (s n) (s m) ≤ b N,
  { refine λm n N hm hn, le_Sup _,
    use (prod.mk m n),
    simp only [and_true, eq_self_iff_true, set.mem_set_of_eq],
    exact ⟨hm, hn⟩ },
  --Prove that it tends to `0`, by using the Cauchy property of `s`
  have D : tendsto b at_top (𝓝 0),
  { refine tendsto_order.2 ⟨λa ha, absurd ha (ennreal.not_lt_zero), λε εpos, _⟩,
    rcases exists_between εpos with ⟨δ, δpos, δlt⟩,
    rcases hs δ δpos with ⟨N, hN⟩,
    refine filter.mem_at_top_sets.2 ⟨N, λn hn, _⟩,
    have : b n ≤ δ := Sup_le begin
      simp only [and_imp, set.mem_image, set.mem_set_of_eq, exists_imp_distrib, prod.exists],
      intros d p q hp hq hd,
      rw ← hd,
      exact le_of_lt (hN p q (le_trans hn hp) (le_trans hn hq))
    end,
    simpa using lt_of_le_of_lt this δlt },
  -- Conclude
  exact ⟨b, ⟨C, D⟩⟩
end,
begin
  rintros ⟨b, ⟨b_bound, b_lim⟩⟩,
  /-b : ℕ → ℝ, b_bound : ∀ (n m N : ℕ), N ≤ n → N ≤ m → edist (s n) (s m) ≤ b N,
    b_lim : tendsto b at_top (𝓝 0)-/
  refine emetric.cauchy_seq_iff.2 (λε εpos, _),
  have : ∀ᶠ n in at_top, b n < ε := (tendsto_order.1 b_lim ).2 _ εpos,
  rcases filter.mem_at_top_sets.1 this with ⟨N, hN⟩,
  exact ⟨N, λm n hm hn, calc
    edist (s m) (s n) ≤ b N : b_bound m n N hm hn
    ... < ε : (hN _ (le_refl N)) ⟩
end⟩

lemma continuous_of_le_add_edist {f : α → ℝ≥0∞} (C : ℝ≥0∞)
  (hC : C ≠ ⊤) (h : ∀x y, f x ≤ f y + C * edist x y) : continuous f :=
begin
  rcases eq_or_ne C 0 with (rfl|C0),
  { simp only [zero_mul, add_zero] at h,
    exact continuous_of_const (λ x y, le_antisymm (h _ _) (h _ _)) },
  { refine continuous_iff_continuous_at.2 (λ x, _),
    by_cases hx : f x = ∞,
    { have : f =ᶠ[𝓝 x] (λ _, ∞),
      { filter_upwards [emetric.ball_mem_nhds x ennreal.coe_lt_top],
        refine λ y (hy : edist y x < ⊤), _, rw edist_comm at hy,
        simpa [hx, hC, hy.ne] using h x y },
      exact this.continuous_at },
    { refine (ennreal.tendsto_nhds hx).2 (λ ε (ε0 : 0 < ε), _),
      filter_upwards [emetric.closed_ball_mem_nhds x (ennreal.div_pos_iff.2 ⟨ε0.ne', hC⟩)],
      have hεC : C * (ε / C) = ε := ennreal.mul_div_cancel' C0 hC,
      refine λ y (hy : edist y x ≤ ε / C), ⟨tsub_le_iff_right.2 _, _⟩,
      { rw edist_comm at hy,
        calc f x ≤ f y + C * edist x y : h x y
        ... ≤ f y + C * (ε / C) : add_le_add_left (mul_le_mul_left' hy C) (f y)
        ... = f y + ε : by rw hεC },
      { calc f y ≤ f x + C * edist y x : h y x
        ... ≤ f x + C * (ε / C) : add_le_add_left (mul_le_mul_left' hy C) (f x)
        ... = f x + ε : by rw hεC } } }
end

theorem continuous_edist : continuous (λp:α×α, edist p.1 p.2) :=
begin
  apply continuous_of_le_add_edist 2 (by norm_num),
  rintros ⟨x, y⟩ ⟨x', y'⟩,
  calc edist x y ≤ edist x x' + edist x' y' + edist y' y : edist_triangle4 _ _ _ _
    ... = edist x' y' + (edist x x' + edist y y') : by simp [edist_comm]; cc
    ... ≤ edist x' y' + (edist (x, y) (x', y') + edist (x, y) (x', y')) :
      add_le_add_left (add_le_add (le_max_left _ _) (le_max_right _ _)) _
    ... = edist x' y' + 2 * edist (x, y) (x', y') : by rw [← mul_two, mul_comm]
end

@[continuity] theorem continuous.edist [topological_space β] {f g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λb, edist (f b) (g b)) :=
continuous_edist.comp (hf.prod_mk hg : _)

theorem filter.tendsto.edist {f g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (𝓝 a)) (hg : tendsto g x (𝓝 b)) :
  tendsto (λx, edist (f x) (g x)) x (𝓝 (edist a b)) :=
(continuous_edist.tendsto (a, b)).comp (hf.prod_mk_nhds hg)

lemma cauchy_seq_of_edist_le_of_tsum_ne_top {f : ℕ → α} (d : ℕ → ℝ≥0∞)
  (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) (hd : tsum d ≠ ∞) :
  cauchy_seq f :=
begin
  lift d to (ℕ → nnreal) using (λ i, ennreal.ne_top_of_tsum_ne_top hd i),
  rw ennreal.tsum_coe_ne_top_iff_summable at hd,
  exact cauchy_seq_of_edist_le_of_summable d hf hd
end

lemma emetric.is_closed_ball {a : α} {r : ℝ≥0∞} : is_closed (closed_ball a r) :=
is_closed_le (continuous_id.edist continuous_const) continuous_const

@[simp] lemma emetric.diam_closure (s : set α) : diam (closure s) = diam s :=
begin
  refine le_antisymm (diam_le $ λ x hx y hy, _) (diam_mono subset_closure),
  have : edist x y ∈ closure (Iic (diam s)),
    from  map_mem_closure2 (@continuous_edist α _) hx hy (λ _ _, edist_le_diam_of_mem),
  rwa closure_Iic at this
end

@[simp] lemma metric.diam_closure {α : Type*} [pseudo_metric_space α] (s : set α) :
  metric.diam (closure s) = diam s :=
by simp only [metric.diam, emetric.diam_closure]

lemma is_closed_set_of_lipschitz_on_with {α β} [pseudo_emetric_space α] [pseudo_emetric_space β]
  (K : ℝ≥0) (s : set α) :
  is_closed {f : α → β | lipschitz_on_with K f s} :=
begin
  simp only [lipschitz_on_with, set_of_forall],
  refine is_closed_bInter (λ x hx, is_closed_bInter $ λ y hy, is_closed_le _ _),
  exacts [continuous.edist (continuous_apply x) (continuous_apply y), continuous_const]
end

lemma is_closed_set_of_lipschitz_with {α β} [pseudo_emetric_space α] [pseudo_emetric_space β]
  (K : ℝ≥0) :
  is_closed {f : α → β | lipschitz_with K f} :=
by simp only [← lipschitz_on_univ, is_closed_set_of_lipschitz_on_with]

namespace real

/-- For a bounded set `s : set ℝ`, its `emetric.diam` is equal to `Sup s - Inf s` reinterpreted as
`ℝ≥0∞`. -/
lemma ediam_eq {s : set ℝ} (h : bounded s) :
  emetric.diam s = ennreal.of_real (Sup s - Inf s) :=
begin
  rcases eq_empty_or_nonempty s with rfl|hne, { simp },
  refine le_antisymm (metric.ediam_le_of_forall_dist_le $ λ x hx y hy, _) _,
  { have := real.subset_Icc_Inf_Sup_of_bounded h,
    exact real.dist_le_of_mem_Icc (this hx) (this hy) },
  { apply ennreal.of_real_le_of_le_to_real,
    rw [← metric.diam, ← metric.diam_closure],
    have h' := real.bounded_iff_bdd_below_bdd_above.1 h,
    calc Sup s - Inf s ≤ dist (Sup s) (Inf s) : le_abs_self _
                   ... ≤ diam (closure s)     :
      dist_le_diam_of_mem h.closure (cSup_mem_closure hne h'.2) (cInf_mem_closure hne h'.1) }
end

/-- For a bounded set `s : set ℝ`, its `metric.diam` is equal to `Sup s - Inf s`. -/
lemma diam_eq {s : set ℝ} (h : bounded s) : metric.diam s = Sup s - Inf s :=
begin
  rw [metric.diam, real.ediam_eq h, ennreal.to_real_of_real],
  rw real.bounded_iff_bdd_below_bdd_above at h,
  exact sub_nonneg.2 (real.Inf_le_Sup s h.1 h.2)
end

@[simp] lemma ediam_Ioo (a b : ℝ) :
  emetric.diam (Ioo a b) = ennreal.of_real (b - a) :=
begin
  rcases le_or_lt b a with h|h,
  { simp [h] },
  { rw [real.ediam_eq (bounded_Ioo _ _), cSup_Ioo h, cInf_Ioo h] },
end

@[simp] lemma ediam_Icc (a b : ℝ) :
  emetric.diam (Icc a b) = ennreal.of_real (b - a) :=
begin
  rcases le_or_lt a b with h|h,
  { rw [real.ediam_eq (bounded_Icc _ _), cSup_Icc h, cInf_Icc h] },
  { simp [h, h.le] }
end

@[simp] lemma ediam_Ico (a b : ℝ) :
  emetric.diam (Ico a b) = ennreal.of_real (b - a) :=
le_antisymm (ediam_Icc a b ▸ diam_mono Ico_subset_Icc_self)
  (ediam_Ioo a b ▸ diam_mono Ioo_subset_Ico_self)

@[simp] lemma ediam_Ioc (a b : ℝ) :
  emetric.diam (Ioc a b) = ennreal.of_real (b - a) :=
le_antisymm (ediam_Icc a b ▸ diam_mono Ioc_subset_Icc_self)
  (ediam_Ioo a b ▸ diam_mono Ioo_subset_Ioc_self)

end real

/-- If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ℝ≥0∞`,
then the distance from `f n` to the limit is bounded by `∑'_{k=n}^∞ d k`. -/
lemma edist_le_tsum_of_edist_le_of_tendsto {f : ℕ → α} (d : ℕ → ℝ≥0∞)
  (hf : ∀ n, edist (f n) (f n.succ) ≤ d n)
  {a : α} (ha : tendsto f at_top (𝓝 a)) (n : ℕ) :
  edist (f n) a ≤ ∑' m, d (n + m) :=
begin
  refine le_of_tendsto (tendsto_const_nhds.edist ha)
    (mem_at_top_sets.2 ⟨n, λ m hnm, _⟩),
  refine le_trans (edist_le_Ico_sum_of_edist_le hnm (λ k _ _, hf k)) _,
  rw [finset.sum_Ico_eq_sum_range],
  exact sum_le_tsum _ (λ _ _, zero_le _) ennreal.summable
end

/-- If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ℝ≥0∞`,
then the distance from `f 0` to the limit is bounded by `∑'_{k=0}^∞ d k`. -/
lemma edist_le_tsum_of_edist_le_of_tendsto₀ {f : ℕ → α} (d : ℕ → ℝ≥0∞)
  (hf : ∀ n, edist (f n) (f n.succ) ≤ d n)
  {a : α} (ha : tendsto f at_top (𝓝 a)) :
  edist (f 0) a ≤ ∑' m, d m :=
by simpa using edist_le_tsum_of_edist_le_of_tendsto d hf ha 0

end --section
