/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/
import topology.instances.nnreal
/-!
# Extended non-negative reals
-/

noncomputable theory
open classical set filter metric
open_locale classical
open_locale topological_space
variables {α : Type*} {β : Type*} {γ : Type*}

open_locale ennreal big_operators filter

namespace ennreal
variables {a b c d : ennreal} {r p q : nnreal}
variables {x y z : ennreal} {ε ε₁ ε₂ : ennreal} {s : set ennreal}

section topological_space
open topological_space

/-- Topology on `ennreal`.

Note: this is different from the `emetric_space` topology. The `emetric_space` topology has
`is_open {⊤}`, while this topology doesn't have singleton elements. -/
instance : topological_space ennreal := preorder.topology ennreal

instance : order_topology ennreal := ⟨rfl⟩

instance : t2_space ennreal := by apply_instance -- short-circuit type class inference

instance : second_countable_topology ennreal :=
⟨⟨⋃q ≥ (0:ℚ), {{a : ennreal | a < nnreal.of_real q}, {a : ennreal | ↑(nnreal.of_real q) < a}},
  (countable_encodable _).bUnion $ assume a ha, (countable_singleton _).insert _,
  le_antisymm
    (le_generate_from $ by simp [or_imp_distrib, is_open_lt', is_open_gt'] {contextual := tt})
    (le_generate_from $ λ s h, begin
      rcases h with ⟨a, hs | hs⟩;
      [ rw show s = ⋃q∈{q:ℚ | 0 ≤ q ∧ a < nnreal.of_real q}, {b | ↑(nnreal.of_real q) < b},
           from set.ext (assume b, by simp [hs, @ennreal.lt_iff_exists_rat_btwn a b, and_assoc]),
        rw show s = ⋃q∈{q:ℚ | 0 ≤ q ∧ ↑(nnreal.of_real q) < a}, {b | b < ↑(nnreal.of_real q)},
           from set.ext (assume b, by simp [hs, @ennreal.lt_iff_exists_rat_btwn b a, and_comm, and_assoc])];
      { apply is_open_Union, intro q,
        apply is_open_Union, intro hq,
        exact generate_open.basic _ (mem_bUnion hq.1 $ by simp) }
    end)⟩⟩

lemma embedding_coe : embedding (coe : nnreal → ennreal) :=
⟨⟨begin
  refine le_antisymm _ _,
  { rw [@order_topology.topology_eq_generate_intervals ennreal _,
      ← coinduced_le_iff_le_induced],
    refine le_generate_from (assume s ha, _),
    rcases ha with ⟨a, rfl | rfl⟩,
    show is_open {b : nnreal | a < ↑b},
    { cases a; simp [none_eq_top, some_eq_coe, is_open_lt'] },
    show is_open {b : nnreal | ↑b < a},
    { cases a; simp [none_eq_top, some_eq_coe, is_open_gt', is_open_const] } },
  { rw [@order_topology.topology_eq_generate_intervals nnreal _],
    refine le_generate_from (assume s ha, _),
    rcases ha with ⟨a, rfl | rfl⟩,
    exact ⟨Ioi a, is_open_Ioi, by simp [Ioi]⟩,
    exact ⟨Iio a, is_open_Iio, by simp [Iio]⟩ }
  end⟩,
  assume a b, coe_eq_coe.1⟩

lemma is_open_ne_top : is_open {a : ennreal | a ≠ ⊤} := is_open_ne

lemma is_open_Ico_zero : is_open (Ico 0 b) := by { rw ennreal.Ico_eq_Iio, exact is_open_Iio}

lemma coe_range_mem_nhds : range (coe : nnreal → ennreal) ∈ 𝓝 (r : ennreal) :=
have {a : ennreal | a ≠ ⊤} = range (coe : nnreal → ennreal),
  from set.ext $ assume a, by cases a; simp [none_eq_top, some_eq_coe],
this ▸ mem_nhds_sets is_open_ne_top coe_ne_top

@[norm_cast] lemma tendsto_coe {f : filter α} {m : α → nnreal} {a : nnreal} :
  tendsto (λa, (m a : ennreal)) f (𝓝 ↑a) ↔ tendsto m f (𝓝 a) :=
embedding_coe.tendsto_nhds_iff.symm

lemma continuous_coe {α} [topological_space α] {f : α → nnreal} :
continuous (λa, (f a : ennreal)) ↔ continuous f :=
embedding_coe.continuous_iff.symm

lemma nhds_coe {r : nnreal} : 𝓝 (r : ennreal) = (𝓝 r).map coe :=
by rw [embedding_coe.induced, map_nhds_induced_eq coe_range_mem_nhds]

lemma nhds_coe_coe {r p : nnreal} : 𝓝 ((r : ennreal), (p : ennreal)) =
  (𝓝 (r, p)).map (λp:nnreal×nnreal, (p.1, p.2)) :=
begin
  rw [(embedding_coe.prod_mk embedding_coe).map_nhds_eq],
  rw [← prod_range_range_eq],
  exact prod_mem_nhds_sets coe_range_mem_nhds coe_range_mem_nhds
end

lemma continuous_of_real : continuous ennreal.of_real :=
(continuous_coe.2 continuous_id).comp nnreal.continuous_of_real

lemma tendsto_of_real {f : filter α} {m : α → ℝ} {a : ℝ} (h : tendsto m f (𝓝 a)) :
  tendsto (λa, ennreal.of_real (m a)) f (𝓝 (ennreal.of_real a)) :=
tendsto.comp (continuous.tendsto continuous_of_real _) h

lemma tendsto_to_nnreal {a : ennreal} : a ≠ ⊤ →
  tendsto (ennreal.to_nnreal) (𝓝 a) (𝓝 a.to_nnreal) :=
begin
  cases a; simp [some_eq_coe, none_eq_top, nhds_coe, tendsto_map'_iff, (∘)],
  exact tendsto_id
end

lemma continuous_on_to_nnreal : continuous_on ennreal.to_nnreal {a | a ≠ ∞}  :=
continuous_on_iff_continuous_restrict.2 $ continuous_iff_continuous_at.2 $ λ x,
  (tendsto_to_nnreal x.2).comp continuous_at_subtype_coe

lemma tendsto_to_real {a : ennreal} : a ≠ ⊤ → tendsto (ennreal.to_real) (𝓝 a) (𝓝 a.to_real) :=
λ ha, tendsto.comp ((@nnreal.tendsto_coe _ (𝓝 a.to_nnreal) id (a.to_nnreal)).2 tendsto_id)
  (tendsto_to_nnreal ha)

lemma tendsto_nhds_top {m : α → ennreal} {f : filter α}
  (h : ∀ n : ℕ, ∀ᶠ a in f, ↑n < m a) : tendsto m f (𝓝 ⊤) :=
tendsto_nhds_generate_from $ assume s hs,
match s, hs with
| _, ⟨none,   or.inl rfl⟩, hr := (lt_irrefl ⊤ hr).elim
| _, ⟨some r, or.inl rfl⟩, hr :=
  let ⟨n, hrn⟩ := exists_nat_gt r in
  mem_sets_of_superset (h n) $ assume a hnma, show ↑r < m a, from
    lt_trans (show (r : ennreal) < n, from (coe_nat n) ▸ coe_lt_coe.2 hrn) hnma
| _, ⟨a,      or.inr rfl⟩, hr := (not_top_lt $ show ⊤ < a, from hr).elim
end

lemma tendsto_nat_nhds_top : tendsto (λ n : ℕ, ↑n) at_top (𝓝 ∞) :=
tendsto_nhds_top $ λ n, mem_at_top_sets.2
  ⟨n+1, λ m hm, ennreal.coe_nat_lt_coe_nat.2 $ nat.lt_of_succ_le hm⟩

lemma nhds_top : 𝓝 ∞ = ⨅a ≠ ∞, 𝓟 (Ioi a) :=
nhds_top_order.trans $ by simp [lt_top_iff_ne_top, Ioi]

lemma nhds_zero : 𝓝 (0 : ennreal) = ⨅a ≠ 0, 𝓟 (Iio a) :=
nhds_bot_order.trans $ by simp [bot_lt_iff_ne_bot, Iio]

/-- The set of finite `ennreal` numbers is homeomorphic to `nnreal`. -/
def ne_top_homeomorph_nnreal : {a | a ≠ ∞} ≃ₜ nnreal :=
{ to_fun := λ x, ennreal.to_nnreal x,
  inv_fun := λ x, ⟨x, coe_ne_top⟩,
  left_inv := λ ⟨x, hx⟩, subtype.eq $ coe_to_nnreal hx,
  right_inv := λ x, to_nnreal_coe,
  continuous_to_fun := continuous_on_iff_continuous_restrict.1 continuous_on_to_nnreal,
  continuous_inv_fun := continuous_subtype_mk _ (continuous_coe.2 continuous_id) }

/-- The set of finite `ennreal` numbers is homeomorphic to `nnreal`. -/
def lt_top_homeomorph_nnreal : {a | a < ∞} ≃ₜ nnreal :=
by refine (homeomorph.set_congr $ set.ext $ λ x, _).trans ne_top_homeomorph_nnreal;
  simp only [mem_set_of_eq, lt_top_iff_ne_top]

-- using Icc because
-- • don't have 'Ioo (x - ε) (x + ε) ∈ 𝓝 x' unless x > 0
-- • (x - y ≤ ε ↔ x ≤ ε + y) is true, while (x - y < ε ↔ x < ε + y) is not
@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma Icc_mem_nhds : x ≠ ⊤ → ε > 0 → Icc (x - ε) (x + ε) ∈ 𝓝 x :=
begin
  assume xt ε0, rw mem_nhds_sets_iff,
  by_cases x0 : x = 0,
  { use Iio (x + ε),
    have : Iio (x + ε) ⊆ Icc (x - ε) (x + ε), assume a, rw x0, simpa using le_of_lt,
    use this, exact ⟨is_open_Iio, mem_Iio_self_add xt ε0⟩ },
  { use Ioo (x - ε) (x + ε), use Ioo_subset_Icc_self,
    exact ⟨is_open_Ioo, mem_Ioo_self_sub_add xt x0 ε0 ε0 ⟩ }
end

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma nhds_of_ne_top : x ≠ ⊤ → 𝓝 x = ⨅ε > 0, 𝓟 (Icc (x - ε) (x + ε)) :=
begin
  assume xt, refine le_antisymm _ _,
  -- first direction
  simp only [le_infi_iff, le_principal_iff], assume ε ε0, exact Icc_mem_nhds xt ε0,
  -- second direction
  rw nhds_generate_from, refine le_infi (assume s, le_infi $ assume hs, _),
  simp only [mem_set_of_eq] at hs, rcases hs with ⟨xs, ⟨a, ha⟩⟩,
  cases ha,
  { rw ha at *,
    rcases dense xs with ⟨b, ⟨ab, bx⟩⟩,
    have xb_pos : x - b > 0 := zero_lt_sub_iff_lt.2 bx,
    have xxb : x - (x - b) = b := sub_sub_cancel (by rwa lt_top_iff_ne_top) (le_of_lt bx),
    refine infi_le_of_le (x - b) (infi_le_of_le xb_pos _),
    simp only [mem_principal_sets, le_principal_iff],
    assume y, rintros ⟨h₁, h₂⟩, rw xxb at h₁, calc a < b : ab ... ≤ y : h₁ },
  { rw ha at *,
    rcases dense xs with ⟨b, ⟨xb, ba⟩⟩,
    have bx_pos : b - x > 0 := zero_lt_sub_iff_lt.2 xb,
    have xbx : x + (b - x) = b := add_sub_cancel_of_le (le_of_lt xb),
    refine infi_le_of_le (b - x) (infi_le_of_le bx_pos _),
    simp only [mem_principal_sets, le_principal_iff],
    assume y, rintros ⟨h₁, h₂⟩, rw xbx at h₂, calc y ≤ b : h₂ ... < a : ba },
end

/-- Characterization of neighborhoods for `ennreal` numbers. See also `tendsto_order`
for a version with strict inequalities. -/
@[nolint ge_or_gt] -- see Note [nolint_ge]
protected theorem tendsto_nhds {f : filter α} {u : α → ennreal} {a : ennreal} (ha : a ≠ ⊤) :
  tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in f, (u x) ∈ Icc (a - ε) (a + ε) :=
by simp only [nhds_of_ne_top ha, tendsto_infi, tendsto_principal, mem_Icc]

@[nolint ge_or_gt] -- see Note [nolint_ge]
protected lemma tendsto_at_top [nonempty β] [semilattice_sup β] {f : β → ennreal} {a : ennreal}
  (ha : a ≠ ⊤) : tendsto f at_top (𝓝 a) ↔ ∀ε>0, ∃N, ∀n≥N, (f n) ∈ Icc (a - ε) (a + ε) :=
by simp only [ennreal.tendsto_nhds ha, mem_at_top_sets, mem_set_of_eq, filter.eventually]

lemma tendsto_coe_nnreal_nhds_top {α} {l : filter α} {f : α → nnreal} (h : tendsto f l at_top) :
  tendsto (λa, (f a : ennreal)) l (𝓝 ∞) :=
tendsto_nhds_top $ assume n,
have ∀ᶠ a in l, ↑(n+1) ≤ f a := h $ mem_at_top _,
mem_sets_of_superset this $ assume a (ha : ↑(n+1) ≤ f a),
begin
  rw [← coe_nat],
  dsimp,
  exact coe_lt_coe.2 (lt_of_lt_of_le (nat.cast_lt.2 (nat.lt_succ_self _)) ha)
end

instance : has_continuous_add ennreal :=
⟨ continuous_iff_continuous_at.2 $
  have hl : ∀a:ennreal, tendsto (λ (p : ennreal × ennreal), p.fst + p.snd) (𝓝 (⊤, a)) (𝓝 ⊤), from
    assume a, tendsto_nhds_top $ assume n,
    have set.prod {a | ↑n < a } univ ∈ 𝓝 ((⊤:ennreal), a), from
      prod_mem_nhds_sets (lt_mem_nhds $ coe_nat n ▸ coe_lt_top) univ_mem_sets,
    show {a : ennreal × ennreal | ↑n < a.fst + a.snd} ∈ 𝓝 (⊤, a),
    begin filter_upwards [this] assume ⟨a₁, a₂⟩ ⟨h₁, h₂⟩, lt_of_lt_of_le h₁ (le_add_right $ le_refl _) end,
  begin
    rintro ⟨a₁, a₂⟩,
    cases a₁, { simp [continuous_at, none_eq_top, hl a₂], },
    cases a₂, { simp [continuous_at, none_eq_top, some_eq_coe, nhds_swap (a₁ : ennreal) ⊤,
                      tendsto_map'_iff, (∘)], convert hl a₁, simp [add_comm] },
    simp [continuous_at, some_eq_coe, nhds_coe_coe, tendsto_map'_iff, (∘)],
    simp only [coe_add.symm, tendsto_coe, tendsto_add]
  end ⟩

protected lemma tendsto_mul (ha : a ≠ 0 ∨ b ≠ ⊤) (hb : b ≠ 0 ∨ a ≠ ⊤) :
  tendsto (λp:ennreal×ennreal, p.1 * p.2) (𝓝 (a, b)) (𝓝 (a * b)) :=
have ht : ∀b:ennreal, b ≠ 0 → tendsto (λp:ennreal×ennreal, p.1 * p.2) (𝓝 ((⊤:ennreal), b)) (𝓝 ⊤),
begin
  refine assume b hb, tendsto_nhds_top $ assume n, _,
  rcases dense (zero_lt_iff_ne_zero.2 hb) with ⟨ε', hε', hεb'⟩,
  rcases ennreal.lt_iff_exists_coe.1 hεb' with ⟨ε, rfl, h⟩,
  rcases exists_nat_gt (↑n / ε) with ⟨m, hm⟩,
  have hε : ε > 0, from coe_lt_coe.1 hε',
  refine mem_sets_of_superset (prod_mem_nhds_sets (lt_mem_nhds $ @coe_lt_top m) (lt_mem_nhds $ h)) _,
  rintros ⟨a₁, a₂⟩ ⟨h₁, h₂⟩,
  dsimp at h₁ h₂ ⊢,
  calc (n:ennreal) = ↑(((n:nnreal) / ε) * ε) :
    begin
      simp [nnreal.div_def],
      rw [mul_assoc, ← coe_mul, nnreal.inv_mul_cancel, coe_one, ← coe_nat, mul_one],
      exact zero_lt_iff_ne_zero.1 hε
    end
    ... < (↑m * ε : nnreal) : coe_lt_coe.2 $ mul_lt_mul hm (le_refl _) hε (nat.cast_nonneg _)
    ... ≤ a₁ * a₂ : by rw [coe_mul]; exact canonically_ordered_semiring.mul_le_mul
      (le_of_lt h₁)
      (le_of_lt h₂)
end,
begin
  cases a, {simp [none_eq_top] at hb, simp [none_eq_top, ht b hb, top_mul, hb] },
  cases b, {
    simp [none_eq_top] at ha,
    simp [*, nhds_swap (a : ennreal) ⊤, none_eq_top, some_eq_coe, top_mul, tendsto_map'_iff, (∘), mul_comm] },
  simp [some_eq_coe, nhds_coe_coe, tendsto_map'_iff, (∘)],
  simp only [coe_mul.symm, tendsto_coe, tendsto_mul]
end

protected lemma tendsto.mul {f : filter α} {ma : α → ennreal} {mb : α → ennreal} {a b : ennreal}
  (hma : tendsto ma f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ ⊤) (hmb : tendsto mb f (𝓝 b)) (hb : b ≠ 0 ∨ a ≠ ⊤) :
  tendsto (λa, ma a * mb a) f (𝓝 (a * b)) :=
show tendsto ((λp:ennreal×ennreal, p.1 * p.2) ∘ (λa, (ma a, mb a))) f (𝓝 (a * b)), from
tendsto.comp (ennreal.tendsto_mul ha hb) (hma.prod_mk_nhds hmb)

protected lemma tendsto.const_mul {f : filter α} {m : α → ennreal} {a b : ennreal}
  (hm : tendsto m f (𝓝 b)) (hb : b ≠ 0 ∨ a ≠ ⊤) : tendsto (λb, a * m b) f (𝓝 (a * b)) :=
by_cases
  (assume : a = 0, by simp [this, tendsto_const_nhds])
  (assume ha : a ≠ 0, ennreal.tendsto.mul tendsto_const_nhds (or.inl ha) hm hb)

protected lemma tendsto.mul_const {f : filter α} {m : α → ennreal} {a b : ennreal}
  (hm : tendsto m f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ ⊤) : tendsto (λx, m x * b) f (𝓝 (a * b)) :=
by simpa only [mul_comm] using ennreal.tendsto.const_mul hm ha

protected lemma continuous_at_const_mul {a b : ennreal} (h : a ≠ ⊤ ∨ b ≠ 0) :
  continuous_at ((*) a) b :=
tendsto.const_mul tendsto_id h.symm

protected lemma continuous_at_mul_const {a b : ennreal} (h : a ≠ ⊤ ∨ b ≠ 0) :
  continuous_at (λ x, x * a) b :=
tendsto.mul_const tendsto_id h.symm

protected lemma continuous_const_mul {a : ennreal} (ha : a ≠ ⊤) : continuous ((*) a) :=
continuous_iff_continuous_at.2 $ λ x, ennreal.continuous_at_const_mul (or.inl ha)

protected lemma continuous_mul_const {a : ennreal} (ha : a ≠ ⊤) : continuous (λ x, x * a) :=
continuous_iff_continuous_at.2 $ λ x, ennreal.continuous_at_mul_const (or.inl ha)

lemma infi_mul_left {ι} [nonempty ι] {f : ι → ennreal} {a : ennreal}
  (h : a = ⊤ → (⨅ i, f i) = 0 → ∃ i, f i = 0) :
  (⨅ i, a * f i) = a * ⨅ i, f i :=
begin
  by_cases H : a = ⊤ ∧ (⨅ i, f i) = 0,
  { rcases h H.1 H.2 with ⟨i, hi⟩,
    rw [H.2, mul_zero, ← bot_eq_zero, infi_eq_bot],
    exact λ b hb, ⟨i, by rwa [hi, mul_zero, ← bot_eq_zero]⟩ },
  { rw not_and_distrib at H,
    exact (map_infi_of_continuous_at_of_monotone' (ennreal.continuous_at_const_mul H)
      ennreal.mul_left_mono).symm }
end

lemma infi_mul_right {ι} [nonempty ι] {f : ι → ennreal} {a : ennreal}
  (h : a = ⊤ → (⨅ i, f i) = 0 → ∃ i, f i = 0) :
  (⨅ i, f i * a) = (⨅ i, f i) * a :=
by simpa only [mul_comm a] using infi_mul_left h

protected lemma continuous_inv : continuous (has_inv.inv : ennreal → ennreal) :=
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

@[simp] protected lemma tendsto_inv_iff {f : filter α} {m : α → ennreal} {a : ennreal} :
  tendsto (λ x, (m x)⁻¹) f (𝓝 a⁻¹) ↔ tendsto m f (𝓝 a) :=
⟨λ h, by simpa only [function.comp, ennreal.inv_inv]
  using (ennreal.continuous_inv.tendsto a⁻¹).comp h,
  (ennreal.continuous_inv.tendsto a).comp⟩

protected lemma tendsto.div {f : filter α} {ma : α → ennreal} {mb : α → ennreal} {a b : ennreal}
  (hma : tendsto ma f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ 0) (hmb : tendsto mb f (𝓝 b)) (hb : b ≠ ⊤ ∨ a ≠ ⊤) :
  tendsto (λa, ma a / mb a) f (𝓝 (a / b)) :=
by { apply tendsto.mul hma _ (ennreal.tendsto_inv_iff.2 hmb) _; simp [ha, hb] }

protected lemma tendsto.const_div {f : filter α} {m : α → ennreal} {a b : ennreal}
  (hm : tendsto m f (𝓝 b)) (hb : b ≠ ⊤ ∨ a ≠ ⊤) : tendsto (λb, a / m b) f (𝓝 (a / b)) :=
by { apply tendsto.const_mul (ennreal.tendsto_inv_iff.2 hm), simp [hb] }

protected lemma tendsto.div_const {f : filter α} {m : α → ennreal} {a b : ennreal}
  (hm : tendsto m f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ 0) : tendsto (λx, m x / b) f (𝓝 (a / b)) :=
by { apply tendsto.mul_const hm, simp [ha] }

protected lemma tendsto_inv_nat_nhds_zero : tendsto (λ n : ℕ, (n : ennreal)⁻¹) at_top (𝓝 0) :=
ennreal.inv_top ▸ ennreal.tendsto_inv_iff.2 tendsto_nat_nhds_top

lemma Sup_add {s : set ennreal} (hs : s.nonempty) : Sup s + a = ⨆b∈s, b + a :=
have Sup ((λb, b + a) '' s) = Sup s + a,
  from is_lub.Sup_eq (is_lub_of_is_lub_of_tendsto
    (assume x _ y _ h, add_le_add h (le_refl _))
    (is_lub_Sup s)
    hs
    (tendsto.add (tendsto_id' inf_le_left) tendsto_const_nhds)),
by simp [Sup_image, -add_comm] at this; exact this.symm

lemma supr_add {ι : Sort*} {s : ι → ennreal} [h : nonempty ι] : supr s + a = ⨆b, s b + a :=
let ⟨x⟩ := h in
calc supr s + a = Sup (range s) + a : by simp [Sup_range]
  ... = (⨆b∈range s, b + a) : Sup_add ⟨s x, x, rfl⟩
  ... = _ : supr_range

lemma add_supr {ι : Sort*} {s : ι → ennreal} [h : nonempty ι] : a + supr s = ⨆b, a + s b :=
by rw [add_comm, supr_add]; simp [add_comm]

lemma supr_add_supr {ι : Sort*} {f g : ι → ennreal} (h : ∀i j, ∃k, f i + g j ≤ f k + g k) :
  supr f + supr g = (⨆ a, f a + g a) :=
begin
  by_cases hι : nonempty ι,
  { letI := hι,
    refine le_antisymm _ (supr_le $ λ a, add_le_add (le_supr _ _) (le_supr _ _)),
    simpa [add_supr, supr_add] using
      λ i j:ι, show f i + g j ≤ ⨆ a, f a + g a, from
      let ⟨k, hk⟩ := h i j in le_supr_of_le k hk },
  { have : ∀f:ι → ennreal, (⨆i, f i) = 0 := assume f, bot_unique (supr_le $ assume i, (hι ⟨i⟩).elim),
    rw [this, this, this, zero_add] }
end

lemma supr_add_supr_of_monotone {ι : Sort*} [semilattice_sup ι]
  {f g : ι → ennreal} (hf : monotone f) (hg : monotone g) :
  supr f + supr g = (⨆ a, f a + g a) :=
supr_add_supr $ assume i j, ⟨i ⊔ j, add_le_add (hf $ le_sup_left) (hg $ le_sup_right)⟩

lemma finset_sum_supr_nat {α} {ι} [semilattice_sup ι] {s : finset α} {f : α → ι → ennreal}
  (hf : ∀a, monotone (f a)) :
  ∑ a in s, supr (f a) = (⨆ n, ∑ a in s, f a n) :=
begin
  refine finset.induction_on s _ _,
  { simp,
    exact (bot_unique $ supr_le $ assume i, le_refl ⊥).symm },
  { assume a s has ih,
    simp only [finset.sum_insert has],
    rw [ih, supr_add_supr_of_monotone (hf a)],
    assume i j h,
    exact (finset.sum_le_sum $ assume a ha, hf a h) }
end

section priority
-- for some reason the next proof fails without changing the priority of this instance
local attribute [instance, priority 1000] classical.prop_decidable
lemma mul_Sup {s : set ennreal} {a : ennreal} : a * Sup s = ⨆i∈s, a * i :=
begin
  by_cases hs : ∀x∈s, x = (0:ennreal),
  { have h₁ : Sup s = 0 := (bot_unique $ Sup_le $ assume a ha, (hs a ha).symm ▸ le_refl 0),
    have h₂ : (⨆i ∈ s, a * i) = 0 :=
      (bot_unique $ supr_le $ assume a, supr_le $ assume ha, by simp [hs a ha]),
    rw [h₁, h₂, mul_zero] },
  { simp only [not_forall] at hs,
    rcases hs with ⟨x, hx, hx0⟩,
    have s₁ : Sup s ≠ 0 :=
      zero_lt_iff_ne_zero.1 (lt_of_lt_of_le (zero_lt_iff_ne_zero.2 hx0) (le_Sup hx)),
    have : Sup ((λb, a * b) '' s) = a * Sup s :=
      is_lub.Sup_eq (is_lub_of_is_lub_of_tendsto
        (assume x _ y _ h, canonically_ordered_semiring.mul_le_mul (le_refl _) h)
        (is_lub_Sup _)
        ⟨x, hx⟩
        (ennreal.tendsto.const_mul (tendsto_id' inf_le_left) (or.inl s₁))),
    rw [this.symm, Sup_image] }
end
end priority

lemma mul_supr {ι : Sort*} {f : ι → ennreal} {a : ennreal} : a * supr f = ⨆i, a * f i :=
by rw [← Sup_range, mul_Sup, supr_range]

lemma supr_mul {ι : Sort*} {f : ι → ennreal} {a : ennreal} : supr f * a = ⨆i, f i * a :=
by rw [mul_comm, mul_supr]; congr; funext; rw [mul_comm]

protected lemma tendsto_coe_sub : ∀{b:ennreal}, tendsto (λb:ennreal, ↑r - b) (𝓝 b) (𝓝 (↑r - b)) :=
begin
  refine (forall_ennreal.2 $ and.intro (assume a, _) _),
  { simp [@nhds_coe a, tendsto_map'_iff, (∘), tendsto_coe, coe_sub.symm],
    exact nnreal.tendsto.sub tendsto_const_nhds tendsto_id },
  simp,
  exact (tendsto.congr' (mem_sets_of_superset (lt_mem_nhds $ @coe_lt_top r) $
    by simp [le_of_lt] {contextual := tt})) tendsto_const_nhds
end

lemma sub_supr {ι : Sort*} [hι : nonempty ι] {b : ι → ennreal} (hr : a < ⊤) :
  a - (⨆i, b i) = (⨅i, a - b i) :=
let ⟨i⟩ := hι in
let ⟨r, eq, _⟩ := lt_iff_exists_coe.mp hr in
have Inf ((λb, ↑r - b) '' range b) = ↑r - (⨆i, b i),
  from is_glb.Inf_eq $ is_glb_of_is_lub_of_tendsto
    (assume x _ y _, sub_le_sub (le_refl _))
    is_lub_supr
    ⟨_, i, rfl⟩
    (tendsto.comp ennreal.tendsto_coe_sub (tendsto_id' inf_le_left)),
by rw [eq, ←this]; simp [Inf_image, infi_range, -mem_range]; exact le_refl _

end topological_space

section tsum

variables {f g : α → ennreal}

@[norm_cast] protected lemma has_sum_coe {f : α → nnreal} {r : nnreal} :
  has_sum (λa, (f a : ennreal)) ↑r ↔ has_sum f r :=
have (λs:finset α, ∑ a in s, ↑(f a)) = (coe : nnreal → ennreal) ∘ (λs:finset α, ∑ a in s, f a),
  from funext $ assume s, ennreal.coe_finset_sum.symm,
by unfold has_sum; rw [this, tendsto_coe]

protected lemma tsum_coe_eq {f : α → nnreal} (h : has_sum f r) : (∑'a, (f a : ennreal)) = r :=
(ennreal.has_sum_coe.2 h).tsum_eq

protected lemma coe_tsum {f : α → nnreal} : summable f → ↑(tsum f) = (∑'a, (f a : ennreal))
| ⟨r, hr⟩ := by rw [hr.tsum_eq, ennreal.tsum_coe_eq hr]

protected lemma has_sum : has_sum f (⨆s:finset α, ∑ a in s, f a) :=
tendsto_order.2
  ⟨assume a' ha',
    let ⟨s, hs⟩ := lt_supr_iff.mp ha' in
    mem_at_top_sets.mpr ⟨s, assume t ht, lt_of_lt_of_le hs $ finset.sum_le_sum_of_subset ht⟩,
  assume a' ha',
    univ_mem_sets' $ assume s,
    have ∑ a in s, f a ≤ ⨆(s : finset α), ∑ a in s, f a,
      from le_supr (λ(s : finset α), ∑ a in s, f a) s,
    lt_of_le_of_lt this ha'⟩

@[simp] protected lemma summable : summable f := ⟨_, ennreal.has_sum⟩

lemma tsum_coe_ne_top_iff_summable {f : β → nnreal} :
  (∑' b, (f b:ennreal)) ≠ ∞ ↔ summable f :=
begin
  refine ⟨λ h, _, λ h, ennreal.coe_tsum h ▸ ennreal.coe_ne_top⟩,
  lift (∑' b, (f b:ennreal)) to nnreal using h with a ha,
  refine ⟨a, ennreal.has_sum_coe.1 _⟩,
  rw ha,
  exact ennreal.summable.has_sum
end

protected lemma tsum_eq_supr_sum : (∑'a, f a) = (⨆s:finset α, ∑ a in s, f a) :=
ennreal.has_sum.tsum_eq

protected lemma tsum_eq_supr_sum' {ι : Type*} (s : ι → finset α) (hs : ∀ t, ∃ i, t ⊆ s i) :
  (∑' a, f a) = ⨆ i, ∑ a in s i, f a :=
begin
  rw [ennreal.tsum_eq_supr_sum],
  symmetry,
  change (⨆i:ι, (λ t : finset α, ∑ a in t, f a) (s i)) = ⨆s:finset α, ∑ a in s, f a,
  exact (finset.sum_mono_set f).supr_comp_eq hs
end

protected lemma tsum_sigma {β : α → Type*} (f : Πa, β a → ennreal) :
  (∑'p:Σa, β a, f p.1 p.2) = (∑'a b, f a b) :=
tsum_sigma' (assume b, ennreal.summable) ennreal.summable

protected lemma tsum_sigma' {β : α → Type*} (f : (Σ a, β a) → ennreal) :
  (∑'p:(Σa, β a), f p) = (∑'a b, f ⟨a, b⟩) :=
tsum_sigma' (assume b, ennreal.summable) ennreal.summable

protected lemma tsum_prod {f : α → β → ennreal} : (∑'p:α×β, f p.1 p.2) = (∑'a, ∑'b, f a b) :=
tsum_prod' ennreal.summable $ λ _, ennreal.summable

protected lemma tsum_comm {f : α → β → ennreal} : (∑'a, ∑'b, f a b) = (∑'b, ∑'a, f a b) :=
tsum_comm' ennreal.summable (λ _, ennreal.summable) (λ _, ennreal.summable)

protected lemma tsum_add : (∑'a, f a + g a) = (∑'a, f a) + (∑'a, g a) :=
tsum_add ennreal.summable ennreal.summable

protected lemma tsum_le_tsum (h : ∀a, f a ≤ g a) : (∑'a, f a) ≤ (∑'a, g a) :=
tsum_le_tsum h ennreal.summable ennreal.summable

protected lemma sum_le_tsum {f : α → ennreal} (s : finset α) : s.sum f ≤ tsum f :=
sum_le_tsum s (λ x hx, zero_le _) ennreal.summable

protected lemma tsum_eq_supr_nat {f : ℕ → ennreal} :
  (∑'i:ℕ, f i) = (⨆i:ℕ, ∑ a in finset.range i, f a) :=
ennreal.tsum_eq_supr_sum' _ finset.exists_nat_subset_range

protected lemma le_tsum (a : α) : f a ≤ (∑'a, f a) :=
calc f a = ∑ a' in {a}, f a' : by simp
  ... ≤ (⨆s:finset α, ∑ a' in s, f a') : le_supr (λs:finset α, ∑ a' in s, f a') _
  ... = (∑'a, f a) : by rw [ennreal.tsum_eq_supr_sum]

protected lemma tsum_eq_top_of_eq_top : (∃ a, f a = ∞) → (∑' a, f a) = ∞
| ⟨a, ha⟩ := top_unique $ ha ▸ ennreal.le_tsum a

protected lemma ne_top_of_tsum_ne_top (h : (∑' a, f a) ≠ ∞) (a : α) : f a ≠ ∞ :=
λ ha, h $ ennreal.tsum_eq_top_of_eq_top ⟨a, ha⟩

protected lemma tsum_mul_left : (∑'i, a * f i) = a * (∑'i, f i) :=
if h : ∀i, f i = 0 then by simp [h] else
let ⟨i, (hi : f i ≠ 0)⟩ := classical.not_forall.mp h in
have sum_ne_0 : (∑'i, f i) ≠ 0, from ne_of_gt $
  calc 0 < f i : lt_of_le_of_ne (zero_le _) hi.symm
    ... ≤ (∑'i, f i) : ennreal.le_tsum _,
have tendsto (λs:finset α, ∑ j in s, a * f j) at_top (𝓝 (a * (∑'i, f i))),
  by rw [← show (*) a ∘ (λs:finset α, ∑ j in s, f j) = λs, ∑ j in s, a * f j,
         from funext $ λ s, finset.mul_sum];
  exact ennreal.tendsto.const_mul ennreal.summable.has_sum (or.inl sum_ne_0),
has_sum.tsum_eq this

protected lemma tsum_mul_right : (∑'i, f i * a) = (∑'i, f i) * a :=
by simp [mul_comm, ennreal.tsum_mul_left]

@[simp] lemma tsum_supr_eq {α : Type*} (a : α) {f : α → ennreal} :
  (∑'b:α, ⨆ (h : a = b), f b) = f a :=
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

lemma has_sum_iff_tendsto_nat {f : ℕ → ennreal} (r : ennreal) :
  has_sum f r ↔ tendsto (λn:ℕ, ∑ i in finset.range n, f i) at_top (𝓝 r) :=
begin
  refine ⟨has_sum.tendsto_sum_nat, assume h, _⟩,
  rw [← supr_eq_of_tendsto _ h, ← ennreal.tsum_eq_supr_nat],
  { exact ennreal.summable.has_sum },
  { exact assume s t hst, finset.sum_le_sum_of_subset (finset.range_subset.2 hst) }
end

end tsum

end ennreal

namespace nnreal

lemma exists_le_has_sum_of_le {f g : β → nnreal} {r : nnreal}
  (hgf : ∀b, g b ≤ f b) (hfr : has_sum f r) : ∃p≤r, has_sum g p :=
have (∑'b, (g b : ennreal)) ≤ r,
begin
  refine has_sum_le (assume b, _) ennreal.summable.has_sum (ennreal.has_sum_coe.2 hfr),
  exact ennreal.coe_le_coe.2 (hgf _)
end,
let ⟨p, eq, hpr⟩ := ennreal.le_coe_iff.1 this in
⟨p, hpr, ennreal.has_sum_coe.1 $ eq ▸ ennreal.summable.has_sum⟩

lemma summable_of_le {f g : β → nnreal} (hgf : ∀b, g b ≤ f b) : summable f → summable g
| ⟨r, hfr⟩ := let ⟨p, _, hp⟩ := exists_le_has_sum_of_le hgf hfr in hp.summable

lemma has_sum_iff_tendsto_nat {f : ℕ → nnreal} (r : nnreal) :
  has_sum f r ↔ tendsto (λn:ℕ, ∑ i in finset.range n, f i) at_top (𝓝 r) :=
begin
  rw [← ennreal.has_sum_coe, ennreal.has_sum_iff_tendsto_nat],
  simp only [ennreal.coe_finset_sum.symm],
  exact ennreal.tendsto_coe
end

lemma tsum_comp_le_tsum_of_inj {β : Type*} {f : α → nnreal} (hf : summable f)
  {i : β → α} (hi : function.injective i) : tsum (f ∘ i) ≤ tsum f :=
tsum_le_tsum_of_inj i hi (λ c hc, zero_le _) (λ b, le_refl _) (summable_comp_injective hf hi) hf

end nnreal

lemma tsum_comp_le_tsum_of_inj {β : Type*} {f : α → ℝ} (hf : summable f) (hn : ∀ a, 0 ≤ f a)
  {i : β → α} (hi : function.injective i) : tsum (f ∘ i) ≤ tsum f :=
begin
  let g : α → nnreal := λ a, ⟨f a, hn a⟩,
  have hg : summable g, by rwa ← nnreal.summable_coe,
  convert nnreal.coe_le_coe.2 (nnreal.tsum_comp_le_tsum_of_inj hg hi);
  { rw nnreal.coe_tsum, congr }
end

lemma summable_of_nonneg_of_le {f g : β → ℝ}
  (hg : ∀b, 0 ≤ g b) (hgf : ∀b, g b ≤ f b) (hf : summable f) : summable g :=
let f' (b : β) : nnreal := ⟨f b, le_trans (hg b) (hgf b)⟩ in
let g' (b : β) : nnreal := ⟨g b, hg b⟩ in
have summable f', from nnreal.summable_coe.1 hf,
have summable g', from
  nnreal.summable_of_le (assume b, (@nnreal.coe_le_coe (g' b) (f' b)).2 $ hgf b) this,
show summable (λb, g' b : β → ℝ), from nnreal.summable_coe.2 this

lemma has_sum_iff_tendsto_nat_of_nonneg {f : ℕ → ℝ} (hf : ∀i, 0 ≤ f i) (r : ℝ) :
  has_sum f r ↔ tendsto (λn:ℕ, ∑ i in finset.range n, f i) at_top (𝓝 r) :=
⟨has_sum.tendsto_sum_nat,
  assume hfr,
  have 0 ≤ r := ge_of_tendsto hfr $ univ_mem_sets' $ assume i,
    show 0 ≤ ∑ j in finset.range i, f j, from finset.sum_nonneg $ assume i _, hf i,
  let f' (n : ℕ) : nnreal := ⟨f n, hf n⟩, r' : nnreal := ⟨r, this⟩ in
  have f_eq : f = (λi:ℕ, (f' i : ℝ)) := rfl,
  have r_eq : r = r' := rfl,
  begin
    rw [f_eq, r_eq, nnreal.has_sum_coe, nnreal.has_sum_iff_tendsto_nat, ← nnreal.tendsto_coe],
    simp only [nnreal.coe_sum],
    exact hfr
  end⟩

lemma infi_real_pos_eq_infi_nnreal_pos {α : Type*} [complete_lattice α] {f : ℝ → α} :
  (⨅(n:ℝ) (h : 0 < n), f n) = (⨅(n:nnreal) (h : 0 < n), f n) :=
le_antisymm
  (le_infi $ assume n, le_infi $ assume hn, infi_le_of_le n $ infi_le _ (nnreal.coe_pos.2 hn))
  (le_infi $ assume r, le_infi $ assume hr, infi_le_of_le ⟨r, le_of_lt hr⟩ $ infi_le _ hr)

section
variables [emetric_space β]
open ennreal filter emetric

/-- In an emetric ball, the distance between points is everywhere finite -/
lemma edist_ne_top_of_mem_ball {a : β} {r : ennreal} (x y : ball a r) : edist x.1 y.1 ≠ ⊤ :=
lt_top_iff_ne_top.1 $
calc edist x y ≤ edist a x + edist a y : edist_triangle_left x.1 y.1 a
  ... < r + r : by rw [edist_comm a x, edist_comm a y]; exact add_lt_add x.2 y.2
  ... ≤ ⊤ : le_top

/-- Each ball in an extended metric space gives us a metric space, as the edist
is everywhere finite. -/
def metric_space_emetric_ball (a : β) (r : ennreal) : metric_space (ball a r) :=
emetric_space.to_metric_space edist_ne_top_of_mem_ball

local attribute [instance] metric_space_emetric_ball

lemma nhds_eq_nhds_emetric_ball (a x : β) (r : ennreal) (h : x ∈ ball a r) :
  𝓝 x = map (coe : ball a r → β) (𝓝 ⟨x, h⟩) :=
(map_nhds_subtype_coe_eq _ $ mem_nhds_sets emetric.is_open_ball h).symm
end

section
variable [emetric_space α]
open emetric

lemma tendsto_iff_edist_tendsto_0 {l : filter β} {f : β → α} {y : α} :
  tendsto f l (𝓝 y) ↔ tendsto (λ x, edist (f x) y) l (𝓝 0) :=
by simp only [emetric.nhds_basis_eball.tendsto_right_iff, emetric.mem_ball,
  @tendsto_order ennreal β _ _, forall_prop_of_false ennreal.not_lt_zero, forall_const, true_and]

/-- Yet another metric characterization of Cauchy sequences on integers. This one is often the
most efficient. -/
lemma emetric.cauchy_seq_iff_le_tendsto_0 [nonempty β] [semilattice_sup β] {s : β → α} :
  cauchy_seq s ↔ (∃ (b: β → ennreal), (∀ n m N : β, N ≤ n → N ≤ m → edist (s n) (s m) ≤ b N)
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
    rcases dense εpos with ⟨δ, δpos, δlt⟩,
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

lemma continuous_of_le_add_edist {f : α → ennreal} (C : ennreal)
  (hC : C ≠ ⊤) (h : ∀x y, f x ≤ f y + C * edist x y) : continuous f :=
begin
  refine continuous_iff_continuous_at.2 (λx, tendsto_order.2 ⟨_, _⟩),
  show ∀e, e < f x → ∀ᶠ y in 𝓝 x, e < f y,
  { assume e he,
    let ε := min (f x - e) 1,
    have : ε < ⊤ := lt_of_le_of_lt (min_le_right _ _) (by simp [lt_top_iff_ne_top]),
    have : 0 < ε := by simp [ε, hC, he, ennreal.zero_lt_one],
    have : 0 < C⁻¹ * (ε/2) := bot_lt_iff_ne_bot.2 (by simp [hC, (ne_of_lt this).symm, mul_eq_zero]),
    have I : C * (C⁻¹ * (ε/2)) < ε,
    { by_cases C_zero : C = 0,
      { simp [C_zero, ‹0 < ε›] },
      { calc C * (C⁻¹ * (ε/2)) = (C * C⁻¹) * (ε/2) : by simp [mul_assoc]
        ... = ε/2 : by simp [ennreal.mul_inv_cancel C_zero hC]
        ... < ε : ennreal.half_lt_self (bot_lt_iff_ne_bot.1 ‹0 < ε›) (lt_top_iff_ne_top.1 ‹ε < ⊤›) }},
    have : ball x (C⁻¹ * (ε/2)) ⊆ {y : α | e < f y},
    { rintros y hy,
      by_cases htop : f y = ⊤,
      { simp [htop, lt_top_iff_ne_top, ne_top_of_lt he] },
      { simp at hy,
        have : e + ε < f y + ε := calc
          e + ε ≤ e + (f x - e) : add_le_add_left (min_le_left _ _) _
          ... = f x : by simp [le_of_lt he]
          ... ≤ f y + C * edist x y : h x y
          ... = f y + C * edist y x : by simp [edist_comm]
          ... ≤ f y + C * (C⁻¹ * (ε/2)) :
            add_le_add_left (canonically_ordered_semiring.mul_le_mul (le_refl _) (le_of_lt hy)) _
          ... < f y + ε : (ennreal.add_lt_add_iff_left (lt_top_iff_ne_top.2 htop)).2 I,
        show e < f y, from
          (ennreal.add_lt_add_iff_right ‹ε < ⊤›).1 this }},
    apply filter.mem_sets_of_superset (ball_mem_nhds _ (‹0 < C⁻¹ * (ε/2)›)) this },
  show ∀e, f x < e → ∀ᶠ y in 𝓝 x, f y < e,
  { assume e he,
    let ε := min (e - f x) 1,
    have : ε < ⊤ := lt_of_le_of_lt (min_le_right _ _) (by simp [lt_top_iff_ne_top]),
    have : 0 < ε := by simp [ε, he, ennreal.zero_lt_one],
    have : 0 < C⁻¹ * (ε/2) := bot_lt_iff_ne_bot.2 (by simp [hC, (ne_of_lt this).symm, mul_eq_zero]),
    have I : C * (C⁻¹ * (ε/2)) < ε,
    { by_cases C_zero : C = 0,
      simp [C_zero, ‹0 < ε›],
      calc C * (C⁻¹ * (ε/2)) = (C * C⁻¹) * (ε/2) : by simp [mul_assoc]
        ... = ε/2 : by simp [ennreal.mul_inv_cancel C_zero hC]
        ... < ε : ennreal.half_lt_self (bot_lt_iff_ne_bot.1 ‹0 < ε›) (lt_top_iff_ne_top.1 ‹ε < ⊤›) },
    have : ball x (C⁻¹ * (ε/2)) ⊆ {y : α | f y < e},
    { rintros y hy,
      have htop : f x ≠ ⊤ := ne_top_of_lt he,
      show f y < e, from calc
        f y ≤ f x + C * edist y x : h y x
        ... ≤ f x + C * (C⁻¹ * (ε/2)) :
            add_le_add_left (canonically_ordered_semiring.mul_le_mul (le_refl _) (le_of_lt hy)) _
        ... < f x + ε : (ennreal.add_lt_add_iff_left (lt_top_iff_ne_top.2 htop)).2 I
        ... ≤ f x + (e - f x) : add_le_add_left (min_le_left _ _) _
        ... = e : by simp [le_of_lt he] },
    apply filter.mem_sets_of_superset (ball_mem_nhds _ (‹0 < C⁻¹ * (ε/2)›)) this },
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

theorem continuous.edist [topological_space β] {f g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λb, edist (f b) (g b)) :=
continuous_edist.comp (hf.prod_mk hg)

theorem filter.tendsto.edist {f g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (𝓝 a)) (hg : tendsto g x (𝓝 b)) :
  tendsto (λx, edist (f x) (g x)) x (𝓝 (edist a b)) :=
(continuous_edist.tendsto (a, b)).comp (hf.prod_mk_nhds hg)

lemma cauchy_seq_of_edist_le_of_tsum_ne_top {f : ℕ → α} (d : ℕ → ennreal)
  (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) (hd : tsum d ≠ ∞) :
  cauchy_seq f :=
begin
  lift d to (ℕ → nnreal) using (λ i, ennreal.ne_top_of_tsum_ne_top hd i),
  rw ennreal.tsum_coe_ne_top_iff_summable at hd,
  exact cauchy_seq_of_edist_le_of_summable d hf hd
end

lemma emetric.is_closed_ball {a : α} {r : ennreal} : is_closed (closed_ball a r) :=
is_closed_le (continuous_id.edist continuous_const) continuous_const

/-- If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ennreal`,
then the distance from `f n` to the limit is bounded by `∑'_{k=n}^∞ d k`. -/
lemma edist_le_tsum_of_edist_le_of_tendsto {f : ℕ → α} (d : ℕ → ennreal)
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

/-- If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ennreal`,
then the distance from `f 0` to the limit is bounded by `∑'_{k=0}^∞ d k`. -/
lemma edist_le_tsum_of_edist_le_of_tendsto₀ {f : ℕ → α} (d : ℕ → ennreal)
  (hf : ∀ n, edist (f n) (f n.succ) ≤ d n)
  {a : α} (ha : tendsto f at_top (𝓝 a)) :
  edist (f 0) a ≤ ∑' m, d m :=
by simpa using edist_le_tsum_of_edist_le_of_tendsto d hf ha 0

end --section
