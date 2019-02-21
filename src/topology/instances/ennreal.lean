/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Extended non-negative reals
-/
import topology.instances.nnreal data.real.ennreal
noncomputable theory
open classical set lattice filter metric
local attribute [instance] prop_decidable
variables {α : Type*} {β : Type*} {γ : Type*}

local notation `∞` := ennreal.infinity

namespace ennreal
variables {a b c d : ennreal} {r p q : nnreal}

section topological_space
open topological_space

/-- Topology on `ennreal`.

Note: this is different from the `emetric_space` topology. The `emetric_space` topology has
`is_open {⊤}`, while this topology doesn't have singleton elements. -/
instance : topological_space ennreal :=
topological_space.generate_from {s | ∃a, s = {b | a < b} ∨ s = {b | b < a}}

instance : orderable_topology ennreal := ⟨rfl⟩

instance : t2_space ennreal := by apply_instance

instance : second_countable_topology ennreal :=
⟨⟨⋃q ≥ (0:ℚ), {{a : ennreal | a < nnreal.of_real q}, {a : ennreal | ↑(nnreal.of_real q) < a}},
  countable_bUnion (countable_encodable _) $ assume a ha, countable_insert (countable_singleton _),
  le_antisymm
    (generate_from_le $ λ s h, begin
      rcases h with ⟨a, hs | hs⟩;
      [ rw show s = ⋃q∈{q:ℚ | 0 ≤ q ∧ a < nnreal.of_real q}, {b | ↑(nnreal.of_real q) < b},
           from set.ext (assume b, by simp [hs, @ennreal.lt_iff_exists_rat_btwn a b, and_assoc]),
        rw show s = ⋃q∈{q:ℚ | 0 ≤ q ∧ ↑(nnreal.of_real q) < a}, {b | b < ↑(nnreal.of_real q)},
           from set.ext (assume b, by simp [hs, @ennreal.lt_iff_exists_rat_btwn b a, and_comm, and_assoc])];
      { apply is_open_Union, intro q,
        apply is_open_Union, intro hq,
        exact generate_open.basic _ (mem_bUnion hq.1 $ by simp) }
    end)
    (generate_from_le $ by simp [or_imp_distrib, is_open_lt', is_open_gt'] {contextual := tt})⟩⟩

lemma embedding_coe : embedding (coe : nnreal → ennreal) :=
and.intro (assume a b, coe_eq_coe.1) $
begin
  refine le_antisymm _ _,
  { rw [orderable_topology.topology_eq_generate_intervals nnreal],
    refine generate_from_le (assume s ha, _),
    rcases ha with ⟨a, rfl | rfl⟩,
    exact ⟨{b : ennreal | ↑a < b}, @is_open_lt' ennreal ennreal.topological_space _ _ _, by simp⟩,
    exact ⟨{b : ennreal | b < ↑a}, @is_open_gt' ennreal ennreal.topological_space _ _ _, by simp⟩, },
  { rw [orderable_topology.topology_eq_generate_intervals ennreal,
      induced_le_iff_le_coinduced],
    refine generate_from_le (assume s ha, _),
    rcases ha with ⟨a, rfl | rfl⟩,
    show is_open {b : nnreal | a < ↑b},
    { cases a; simp [none_eq_top, some_eq_coe, is_open_lt'] },
    show is_open {b : nnreal | ↑b < a},
    { cases a; simp [none_eq_top, some_eq_coe, is_open_gt', is_open_const] } }
end

lemma is_open_ne_top : is_open {a : ennreal | a ≠ ⊤} :=
is_open_neg (is_closed_eq continuous_id continuous_const)

lemma coe_range_mem_nhds : range (coe : nnreal → ennreal) ∈ (nhds (r : ennreal)).sets :=
have {a : ennreal | a ≠ ⊤} = range (coe : nnreal → ennreal),
  from set.ext $ assume a, by cases a; simp [none_eq_top, some_eq_coe],
this ▸ mem_nhds_sets is_open_ne_top coe_ne_top

lemma tendsto_coe {f : filter α} {m : α → nnreal} {a : nnreal} :
  tendsto (λa, (m a : ennreal)) f (nhds ↑a) ↔ tendsto m f (nhds a) :=
embedding_coe.tendsto_nhds_iff.symm

lemma continuous_coe {α} [topological_space α] {f : α → nnreal} :
continuous (λa, (f a : ennreal)) ↔ continuous f :=
embedding_coe.continuous_iff.symm

lemma nhds_coe {r : nnreal} : nhds (r : ennreal) = (nhds r).map coe :=
by rw [embedding_coe.2, map_nhds_induced_eq coe_range_mem_nhds]

lemma nhds_coe_coe {r p : nnreal} : nhds ((r : ennreal), (p : ennreal)) =
  (nhds (r, p)).map (λp:nnreal×nnreal, (p.1, p.2)) :=
begin
  rw [(embedding_prod_mk embedding_coe embedding_coe).map_nhds_eq],
  rw [← prod_range_range_eq],
  exact prod_mem_nhds_sets coe_range_mem_nhds coe_range_mem_nhds
end

lemma continuous_of_real : continuous ennreal.of_real :=
continuous.comp nnreal.continuous_of_real (continuous_coe.2 continuous_id)

lemma tendsto_of_real {f : filter α} {m : α → ℝ} {a : ℝ} (h : tendsto m f (nhds a)) :
  tendsto (λa, ennreal.of_real (m a)) f (nhds (ennreal.of_real a)) :=
tendsto.comp h (continuous.tendsto continuous_of_real _)

lemma tendsto_to_nnreal {a : ennreal} : a ≠ ⊤ →
  tendsto (ennreal.to_nnreal) (nhds a) (nhds a.to_nnreal) :=
begin
  cases a; simp [some_eq_coe, none_eq_top, nhds_coe, tendsto_map'_iff, (∘)],
  exact tendsto_id
end

lemma tendsto_nhds_top {m : α → ennreal} {f : filter α}
  (h : ∀n:ℕ, {a | ↑n < m a} ∈ f.sets) : tendsto m f (nhds ⊤) :=
tendsto_nhds_generate_from $ assume s hs,
match s, hs with
| _, ⟨none,   or.inl rfl⟩, hr := (lt_irrefl ⊤ hr).elim
| _, ⟨some r, or.inl rfl⟩, hr :=
  let ⟨n, hrn⟩ := exists_nat_gt r in
  mem_sets_of_superset (h n) $ assume a hnma, show ↑r < m a, from
    lt_trans (show (r : ennreal) < n, from (coe_nat n) ▸ coe_lt_coe.2 hrn) hnma
| _, ⟨a,      or.inr rfl⟩, hr := (not_top_lt $ show ⊤ < a, from hr).elim
end

lemma tendsto_coe_nnreal_nhds_top {α} {l : filter α} {f : α → nnreal} (h : tendsto f l at_top) :
  tendsto (λa, (f a : ennreal)) l (nhds (⊤:ennreal)) :=
tendsto_nhds_top $ assume n,
have {a : α | ↑(n+1) ≤ f a} ∈ l.sets := h $ mem_at_top _,
mem_sets_of_superset this $ assume a (ha : ↑(n+1) ≤ f a),
begin
  rw [← coe_nat],
  dsimp,
  exact coe_lt_coe.2 (lt_of_lt_of_le (nat.cast_lt.2 (nat.lt_succ_self _)) ha)
end

instance : topological_add_monoid ennreal :=
⟨ continuous_iff_continuous_at.2 $
  have hl : ∀a:ennreal, tendsto (λ (p : ennreal × ennreal), p.fst + p.snd) (nhds (⊤, a)) (nhds ⊤), from
    assume a, tendsto_nhds_top $ assume n,
    have set.prod {a | ↑n < a } univ ∈ (nhds ((⊤:ennreal), a)).sets, from
      prod_mem_nhds_sets (lt_mem_nhds $ coe_nat n ▸ coe_lt_top) univ_mem_sets,
    begin filter_upwards [this] assume ⟨a₁, a₂⟩ ⟨h₁, h₂⟩, lt_of_lt_of_le h₁ (le_add_right $ le_refl _) end,
  begin
    rintro ⟨a₁, a₂⟩,
    cases a₁, { simp [continuous_at, none_eq_top, hl a₂], },
    cases a₂, { simp [continuous_at, none_eq_top, some_eq_coe, nhds_swap (a₁ : ennreal) ⊤,
                      tendsto_map'_iff, (∘), hl ↑a₁] },
    simp [continuous_at, some_eq_coe, nhds_coe_coe, tendsto_map'_iff, (∘)],
    simp only [coe_add.symm, tendsto_coe, tendsto_add']
  end ⟩

protected lemma tendsto_mul' (ha : a ≠ 0 ∨ b ≠ ⊤) (hb : b ≠ 0 ∨ a ≠ ⊤) :
  tendsto (λp:ennreal×ennreal, p.1 * p.2) (nhds (a, b)) (nhds (a * b)) :=
have ht : ∀b:ennreal, b ≠ 0 → tendsto (λp:ennreal×ennreal, p.1 * p.2) (nhds ((⊤:ennreal), b)) (nhds ⊤),
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
    have ha' : a ≠ 0, from mt coe_eq_coe.2 ha,
    simp [*, nhds_swap (a : ennreal) ⊤, none_eq_top, some_eq_coe, top_mul, tendsto_map'_iff, (∘), mul_comm] },
  simp [some_eq_coe, nhds_coe_coe, tendsto_map'_iff, (∘)],
  simp only [coe_mul.symm, tendsto_coe, tendsto_mul']
end

protected lemma tendsto_mul {f : filter α} {ma : α → ennreal} {mb : α → ennreal} {a b : ennreal}
  (hma : tendsto ma f (nhds a)) (ha : a ≠ 0 ∨ b ≠ ⊤) (hmb : tendsto mb f (nhds b)) (hb : b ≠ 0 ∨ a ≠ ⊤) :
  tendsto (λa, ma a * mb a) f (nhds (a * b)) :=
show tendsto ((λp:ennreal×ennreal, p.1 * p.2) ∘ (λa, (ma a, mb a))) f (nhds (a * b)), from
tendsto.comp (tendsto_prod_mk_nhds hma hmb) (ennreal.tendsto_mul' ha hb)

protected lemma tendsto_mul_right {f : filter α} {m : α → ennreal} {a b : ennreal}
  (hm : tendsto m f (nhds b)) (hb : b ≠ 0 ∨ a ≠ ⊤) : tendsto (λb, a * m b) f (nhds (a * b)) :=
by_cases
  (assume : a = 0, by simp [this, tendsto_const_nhds])
  (assume ha : a ≠ 0, ennreal.tendsto_mul tendsto_const_nhds (or.inl ha) hm hb)

lemma Sup_add {s : set ennreal} (hs : s ≠ ∅) : Sup s + a = ⨆b∈s, b + a :=
have Sup ((λb, b + a) '' s) = Sup s + a,
  from is_lub_iff_Sup_eq.mp $ is_lub_of_is_lub_of_tendsto
    (assume x _ y _ h, add_le_add' h (le_refl _))
    is_lub_Sup
    hs
    (tendsto_add (tendsto_id' inf_le_left) tendsto_const_nhds),
by simp [Sup_image, -add_comm] at this; exact this.symm

lemma supr_add {ι : Sort*} {s : ι → ennreal} [h : nonempty ι] : supr s + a = ⨆b, s b + a :=
let ⟨x⟩ := h in
calc supr s + a = Sup (range s) + a : by simp [Sup_range]
  ... = (⨆b∈range s, b + a) : Sup_add $ ne_empty_iff_exists_mem.mpr ⟨s x, x, rfl⟩
  ... = _ : by simp [supr_range, -mem_range]

lemma add_supr {ι : Sort*} {s : ι → ennreal} [h : nonempty ι] : a + supr s = ⨆b, a + s b :=
by rw [add_comm, supr_add]; simp

lemma supr_add_supr {ι : Sort*} {f g : ι → ennreal} (h : ∀i j, ∃k, f i + g j ≤ f k + g k) :
  supr f + supr g = (⨆ a, f a + g a) :=
begin
  by_cases hι : nonempty ι,
  { letI := hι,
    refine le_antisymm _ (supr_le $ λ a, add_le_add' (le_supr _ _) (le_supr _ _)),
    simpa [add_supr, supr_add] using
      λ i j:ι, show f i + g j ≤ ⨆ a, f a + g a, from
      let ⟨k, hk⟩ := h i j in le_supr_of_le k hk },
  { have : ∀f:ι → ennreal, (⨆i, f i) = 0 := assume f, bot_unique (supr_le $ assume i, (hι ⟨i⟩).elim),
    rw [this, this, this, zero_add] }
end

lemma supr_add_supr_of_monotone {ι : Sort*} [semilattice_sup ι]
  {f g : ι → ennreal} (hf : monotone f) (hg : monotone g) :
  supr f + supr g = (⨆ a, f a + g a) :=
supr_add_supr $ assume i j, ⟨i ⊔ j, add_le_add' (hf $ le_sup_left) (hg $ le_sup_right)⟩

lemma finset_sum_supr_nat {α} {ι} [semilattice_sup ι] {s : finset α} {f : α → ι → ennreal}
  (hf : ∀a, monotone (f a)) :
  s.sum (λa, supr (f a)) = (⨆ n, s.sum (λa, f a n)) :=
begin
  refine finset.induction_on s _ _,
  { simp,
    exact (bot_unique $ supr_le $ assume i, le_refl ⊥).symm },
  { assume a s has ih,
    simp only [finset.sum_insert has],
    rw [ih, supr_add_supr_of_monotone (hf a)],
    assume i j h,
    exact (finset.sum_le_sum' $ assume a ha, hf a h) }
end

lemma mul_Sup {s : set ennreal} {a : ennreal} : a * Sup s = ⨆i∈s, a * i :=
begin
  by_cases hs : ∀x∈s, x = (0:ennreal),
  { have h₁ : Sup s = 0 := (bot_unique $ Sup_le $ assume a ha, (hs a ha).symm ▸ le_refl 0),
    have h₂ : (⨆i ∈ s, a * i) = 0 :=
      (bot_unique $ supr_le $ assume a, supr_le $ assume ha, by simp [hs a ha]),
    rw [h₁, h₂, mul_zero] },
  { simp only [not_forall] at hs,
    rcases hs with ⟨x, hx, hx0⟩,
    have s₀ : s ≠ ∅ := not_eq_empty_iff_exists.2 ⟨x, hx⟩,
    have s₁ : Sup s ≠ 0 :=
      zero_lt_iff_ne_zero.1 (lt_of_lt_of_le (zero_lt_iff_ne_zero.2 hx0) (le_Sup hx)),
    have : Sup ((λb, a * b) '' s) = a * Sup s :=
      is_lub_iff_Sup_eq.mp (is_lub_of_is_lub_of_tendsto
        (assume x _ y _ h, canonically_ordered_semiring.mul_le_mul (le_refl _) h)
        is_lub_Sup
        s₀
        (ennreal.tendsto_mul_right (tendsto_id' inf_le_left) (or.inl s₁))),
    rw [this.symm, Sup_image] }
end

lemma mul_supr {ι : Sort*} {f : ι → ennreal} {a : ennreal} : a * supr f = ⨆i, a * f i :=
by rw [← Sup_range, mul_Sup, supr_range]

lemma supr_mul {ι : Sort*} {f : ι → ennreal} {a : ennreal} : supr f * a = ⨆i, f i * a :=
by rw [mul_comm, mul_supr]; congr; funext; rw [mul_comm]

protected lemma tendsto_coe_sub : ∀{b:ennreal}, tendsto (λb:ennreal, ↑r - b) (nhds b) (nhds (↑r - b)) :=
begin
  refine (forall_ennreal.2 $ and.intro (assume a, _) _),
  { simp [@nhds_coe a, tendsto_map'_iff, (∘), tendsto_coe, coe_sub.symm],
    exact nnreal.tendsto_sub tendsto_const_nhds tendsto_id },
  simp,
  exact (tendsto_cong tendsto_const_nhds $ mem_sets_of_superset (lt_mem_nhds $ @coe_lt_top r) $
    by simp [le_of_lt] {contextual := tt})
end

lemma sub_supr {ι : Sort*} [hι : nonempty ι] {b : ι → ennreal} (hr : a < ⊤) :
  a - (⨆i, b i) = (⨅i, a - b i) :=
let ⟨i⟩ := hι in
let ⟨r, eq, _⟩ := lt_iff_exists_coe.mp hr in
have Inf ((λb, ↑r - b) '' range b) = ↑r - (⨆i, b i),
  from is_glb_iff_Inf_eq.mp $ is_glb_of_is_lub_of_tendsto
    (assume x _ y _, sub_le_sub (le_refl _))
    is_lub_supr
    (ne_empty_of_mem ⟨i, rfl⟩)
    (tendsto.comp (tendsto_id' inf_le_left) ennreal.tendsto_coe_sub),
by rw [eq, ←this]; simp [Inf_image, infi_range, -mem_range]; exact le_refl _

end topological_space

section tsum

variables {f g : α → ennreal}

protected lemma is_sum_coe {f : α → nnreal} {r : nnreal} :
  is_sum (λa, (f a : ennreal)) ↑r ↔ is_sum f r :=
have (λs:finset α, s.sum (coe ∘ f)) = (coe : nnreal → ennreal) ∘ (λs:finset α, s.sum f),
  from funext $ assume s, ennreal.coe_finset_sum.symm,
by unfold is_sum; rw [this, tendsto_coe]

protected lemma tsum_coe_eq {f : α → nnreal} (h : is_sum f r) : (∑a, (f a : ennreal)) = r :=
tsum_eq_is_sum $ ennreal.is_sum_coe.2 $ h

protected lemma tsum_coe {f : α → nnreal} : has_sum f → (∑a, (f a : ennreal)) = ↑(tsum f)
| ⟨r, hr⟩ := by rw [tsum_eq_is_sum hr, ennreal.tsum_coe_eq hr]

protected lemma is_sum : is_sum f (⨆s:finset α, s.sum f) :=
tendsto_orderable.2
  ⟨assume a' ha',
    let ⟨s, hs⟩ := lt_supr_iff.mp ha' in
    mem_at_top_sets.mpr ⟨s, assume t ht, lt_of_lt_of_le hs $ finset.sum_le_sum_of_subset ht⟩,
  assume a' ha',
    univ_mem_sets' $ assume s,
    have s.sum f ≤ ⨆(s : finset α), s.sum f,
      from le_supr (λ(s : finset α), s.sum f) s,
    lt_of_le_of_lt this ha'⟩

@[simp] protected lemma has_sum : has_sum f := ⟨_, ennreal.is_sum⟩

protected lemma tsum_eq_supr_sum : (∑a, f a) = (⨆s:finset α, s.sum f) :=
tsum_eq_is_sum ennreal.is_sum

protected lemma tsum_sigma {β : α → Type*} (f : Πa, β a → ennreal) :
  (∑p:Σa, β a, f p.1 p.2) = (∑a b, f a b) :=
tsum_sigma (assume b, ennreal.has_sum) ennreal.has_sum

protected lemma tsum_prod {f : α → β → ennreal} : (∑p:α×β, f p.1 p.2) = (∑a, ∑b, f a b) :=
let j : α × β → (Σa:α, β) := λp, sigma.mk p.1 p.2 in
let i : (Σa:α, β) → α × β := λp, (p.1, p.2) in
let f' : (Σa:α, β) → ennreal := λp, f p.1 p.2 in
calc (∑p:α×β, f' (j p)) = (∑p:Σa:α, β, f p.1 p.2) :
    tsum_eq_tsum_of_iso j i (assume ⟨a, b⟩, rfl) (assume ⟨a, b⟩, rfl)
   ... = (∑a, ∑b, f a b) : ennreal.tsum_sigma f

protected lemma tsum_comm {f : α → β → ennreal} : (∑a, ∑b, f a b) = (∑b, ∑a, f a b) :=
let f' : α×β → ennreal := λp, f p.1 p.2 in
calc (∑a, ∑b, f a b) = (∑p:α×β, f' p) : ennreal.tsum_prod.symm
  ... = (∑p:β×α, f' (prod.swap p)) :
    (tsum_eq_tsum_of_iso prod.swap (@prod.swap α β) (assume ⟨a, b⟩, rfl) (assume ⟨a, b⟩, rfl)).symm
  ... = (∑b, ∑a, f' (prod.swap (b, a))) : @ennreal.tsum_prod β α (λb a, f' (prod.swap (b, a)))

protected lemma tsum_add : (∑a, f a + g a) = (∑a, f a) + (∑a, g a) :=
tsum_add ennreal.has_sum ennreal.has_sum

protected lemma tsum_le_tsum (h : ∀a, f a ≤ g a) : (∑a, f a) ≤ (∑a, g a) :=
tsum_le_tsum h ennreal.has_sum ennreal.has_sum

protected lemma tsum_eq_supr_nat {f : ℕ → ennreal} :
  (∑i:ℕ, f i) = (⨆i:ℕ, (finset.range i).sum f) :=
calc _ = (⨆s:finset ℕ, s.sum f) : ennreal.tsum_eq_supr_sum
  ... = (⨆i:ℕ, (finset.range i).sum f) : le_antisymm
    (supr_le_supr2 $ assume s,
      let ⟨n, hn⟩ := finset.exists_nat_subset_range s in
      ⟨n, finset.sum_le_sum_of_subset hn⟩)
    (supr_le_supr2 $ assume i, ⟨finset.range i, le_refl _⟩)

protected lemma le_tsum (a : α) : f a ≤ (∑a, f a) :=
calc f a = ({a} : finset α).sum f : by simp
  ... ≤ (⨆s:finset α, s.sum f) : le_supr (λs:finset α, s.sum f) _
  ... = (∑a, f a) : by rw [ennreal.tsum_eq_supr_sum]

protected lemma mul_tsum : (∑i, a * f i) = a * (∑i, f i) :=
if h : ∀i, f i = 0 then by simp [h] else
let ⟨i, (hi : f i ≠ 0)⟩ := classical.not_forall.mp h in
have sum_ne_0 : (∑i, f i) ≠ 0, from ne_of_gt $
  calc 0 < f i : lt_of_le_of_ne (zero_le _) hi.symm
    ... ≤ (∑i, f i) : ennreal.le_tsum _,
have tendsto (λs:finset α, s.sum ((*) a ∘ f)) at_top (nhds (a * (∑i, f i))),
  by rw [← show (*) a ∘ (λs:finset α, s.sum f) = λs, s.sum ((*) a ∘ f),
         from funext $ λ s, finset.mul_sum];
  exact ennreal.tendsto_mul_right (is_sum_tsum ennreal.has_sum) (or.inl sum_ne_0),
tsum_eq_is_sum this

protected lemma tsum_mul : (∑i, f i * a) = (∑i, f i) * a :=
by simp [mul_comm, ennreal.mul_tsum]

@[simp] lemma tsum_supr_eq {α : Type*} (a : α) {f : α → ennreal} :
  (∑b:α, ⨆ (h : a = b), f b) = f a :=
le_antisymm
  (by rw [ennreal.tsum_eq_supr_sum]; exact supr_le (assume s,
    calc s.sum (λb, ⨆ (h : a = b), f b) ≤ (finset.singleton a).sum (λb, ⨆ (h : a = b), f b) :
        finset.sum_le_sum_of_ne_zero $ assume b _ hb,
          suffices a = b, by simpa using this.symm,
          classical.by_contradiction $ assume h,
            by simpa [h] using hb
      ... = f a : by simp))
  (calc f a ≤ (⨆ (h : a = a), f a) : le_supr (λh:a=a, f a) rfl
    ... ≤ (∑b:α, ⨆ (h : a = b), f b) : ennreal.le_tsum _)

lemma is_sum_iff_tendsto_nat {f : ℕ → ennreal} (r : ennreal) :
  is_sum f r ↔ tendsto (λn:ℕ, (finset.range n).sum f) at_top (nhds r) :=
begin
  refine ⟨tendsto_sum_nat_of_is_sum, assume h, _⟩,
  rw [← supr_eq_of_tendsto _ h, ← ennreal.tsum_eq_supr_nat],
  { exact is_sum_tsum ennreal.has_sum },
  { exact assume s t hst, finset.sum_le_sum_of_subset (finset.range_subset.2 hst) }
end

end tsum

end ennreal

namespace nnreal

lemma exists_le_is_sum_of_le {f g : β → nnreal} {r : nnreal}
  (hgf : ∀b, g b ≤ f b) (hfr : is_sum f r) : ∃p≤r, is_sum g p :=
have (∑b, (g b : ennreal)) ≤ r,
begin
  refine is_sum_le (assume b, _) (is_sum_tsum ennreal.has_sum) (ennreal.is_sum_coe.2 hfr),
  exact ennreal.coe_le_coe.2 (hgf _)
end,
let ⟨p, eq, hpr⟩ := ennreal.le_coe_iff.1 this in
⟨p, hpr, ennreal.is_sum_coe.1 $ eq ▸ is_sum_tsum ennreal.has_sum⟩

lemma has_sum_of_le {f g : β → nnreal} (hgf : ∀b, g b ≤ f b) : has_sum f → has_sum g
| ⟨r, hfr⟩ := let ⟨p, _, hp⟩ := exists_le_is_sum_of_le hgf hfr in has_sum_spec hp

lemma is_sum_iff_tendsto_nat {f : ℕ → nnreal} (r : nnreal) :
  is_sum f r ↔ tendsto (λn:ℕ, (finset.range n).sum f) at_top (nhds r) :=
begin
  rw [← ennreal.is_sum_coe, ennreal.is_sum_iff_tendsto_nat],
  simp only [ennreal.coe_finset_sum.symm],
  exact ennreal.tendsto_coe
end

end nnreal

lemma has_sum_of_nonneg_of_le {f g : β → ℝ}
  (hg : ∀b, 0 ≤ g b) (hgf : ∀b, g b ≤ f b) (hf : has_sum f) : has_sum g :=
let f' (b : β) : nnreal := ⟨f b, le_trans (hg b) (hgf b)⟩ in
let g' (b : β) : nnreal := ⟨g b, hg b⟩ in
have has_sum f', from nnreal.has_sum_coe.1 hf,
have has_sum g', from
  nnreal.has_sum_of_le (assume b, (@nnreal.coe_le (g' b) (f' b)).2 $ hgf b) this,
show has_sum (λb, g' b : β → ℝ), from nnreal.has_sum_coe.2 this

lemma is_sum_iff_tendsto_nat_of_nonneg {f : ℕ → ℝ} (hf : ∀i, 0 ≤ f i) (r : ℝ) :
  is_sum f r ↔ tendsto (λn:ℕ, (finset.range n).sum f) at_top (nhds r) :=
⟨tendsto_sum_nat_of_is_sum,
  assume hfr,
  have 0 ≤ r := ge_of_tendsto at_top_ne_bot hfr $ univ_mem_sets' $ assume i,
    show 0 ≤ (finset.range i).sum f, from finset.zero_le_sum $ assume i _, hf i,
  let f' (n : ℕ) : nnreal := ⟨f n, hf n⟩, r' : nnreal := ⟨r, this⟩ in
  have f_eq : f = (λi:ℕ, (f' i : ℝ)) := rfl,
  have r_eq : r = r' := rfl,
  begin
    rw [f_eq, r_eq, nnreal.is_sum_coe, nnreal.is_sum_iff_tendsto_nat, ← nnreal.tendsto_coe],
    simp only [nnreal.sum_coe],
    exact hfr
  end⟩

lemma infi_real_pos_eq_infi_nnreal_pos {α : Type*} [complete_lattice α] {f : ℝ → α} :
  (⨅(n:ℝ) (h : n > 0), f n) = (⨅(n:nnreal) (h : n > 0), f n) :=
le_antisymm
  (le_infi $ assume n, le_infi $ assume hn, infi_le_of_le n $ infi_le _ (nnreal.coe_pos.2 hn))
  (le_infi $ assume r, le_infi $ assume hr, infi_le_of_le ⟨r, le_of_lt hr⟩ $ infi_le _ hr)

section
variables [emetric_space β]
open lattice ennreal filter emetric

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
  nhds x = map (coe : ball a r → β) (nhds ⟨x, h⟩) :=
(map_nhds_subtype_val_eq _ $ mem_nhds_sets emetric.is_open_ball h).symm
end

section
variable [emetric_space α]
open emetric

/-- Yet another metric characterization of Cauchy sequences on integers. This one is often the
most efficient. -/
lemma emetric.cauchy_seq_iff_le_tendsto_0 [inhabited β] [semilattice_sup β] {s : β → α} :
  cauchy_seq s ↔ (∃ (b: β → ennreal), (∀ n m N : β, N ≤ n → N ≤ m → edist (s n) (s m) ≤ b N)
                    ∧ (tendsto b at_top (nhds 0))) :=
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
  have D : tendsto b at_top (nhds 0),
  { refine tendsto_orderable.2 ⟨λa ha, absurd ha (ennreal.not_lt_zero), λε εpos, _⟩,
    rcases dense εpos with ⟨δ, δpos, δlt⟩,
    rcases hs δ δpos with ⟨N, hN⟩,
    refine filter.mem_at_top_sets.2 ⟨N, λn hn, _⟩,
    have : b n ≤ δ := Sup_le begin
      simp only [and_imp, set.mem_image, set.mem_set_of_eq, exists_imp_distrib, prod.exists],
      intros d p q hp hq hd,
      rw ← hd,
      exact le_of_lt (hN q p (le_trans hn hq) (le_trans hn hp))
    end,
    simpa using lt_of_le_of_lt this δlt },
  -- Conclude
  exact ⟨b, ⟨C, D⟩⟩
end,
begin
  rintros ⟨b, ⟨b_bound, b_lim⟩⟩,
  /-b : ℕ → ℝ, b_bound : ∀ (n m N : ℕ), N ≤ n → N ≤ m → edist (s n) (s m) ≤ b N,
    b_lim : tendsto b at_top (nhds 0)-/
  refine emetric.cauchy_seq_iff.2 (λε εpos, _),
  have : {n | b n < ε} ∈ at_top.sets := (tendsto_orderable.1 b_lim ).2 _ εpos,
  rcases filter.mem_at_top_sets.1 this with ⟨N, hN⟩,
  exact ⟨N, λm n hm hn, calc
    edist (s n) (s m) ≤ b N : b_bound n m N hn hm
    ... < ε : (hN _ (le_refl N)) ⟩
end⟩

lemma continuous_of_le_add_edist {f : α → ennreal} (C : ennreal)
  (hC : C ≠ ⊤) (h : ∀x y, f x ≤ f y + C * edist x y) : continuous f :=
begin
  refine continuous_iff_continuous_at.2 (λx, tendsto_orderable.2 ⟨_, _⟩),
  show ∀e, e < f x → {y : α | e < f y} ∈ (nhds x).sets,
  { assume e he,
    let ε := min (f x - e) 1,
    have : ε < ⊤ := lt_of_le_of_lt (min_le_right _ _) (by simp [lt_top_iff_ne_top]),
    have : 0 < ε := by simp [ε, hC, he, ennreal.zero_lt_one],
    have : 0 < C⁻¹ * (ε/2) := bot_lt_iff_ne_bot.2 (by simp [hC, (ne_of_lt this).symm, ennreal.mul_eq_zero]),
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
          e + ε ≤ e + (f x - e) : add_le_add_left' (min_le_left _ _)
          ... = f x : by simp [le_of_lt he]
          ... ≤ f y + C * edist x y : h x y
          ... = f y + C * edist y x : by simp [edist_comm]
          ... ≤ f y + C * (C⁻¹ * (ε/2)) :
            add_le_add_left' $ canonically_ordered_semiring.mul_le_mul (le_refl _) (le_of_lt hy)
          ... < f y + ε : (ennreal.add_lt_add_iff_left (lt_top_iff_ne_top.2 htop)).2 I,
        show e < f y, from
          (ennreal.add_lt_add_iff_right ‹ε < ⊤›).1 this }},
    apply filter.mem_sets_of_superset (ball_mem_nhds _ (‹0 < C⁻¹ * (ε/2)›)) this },
  show ∀e, f x < e → {y : α | f y < e} ∈ (nhds x).sets,
  { assume e he,
    let ε := min (e - f x) 1,
    have : ε < ⊤ := lt_of_le_of_lt (min_le_right _ _) (by simp [lt_top_iff_ne_top]),
    have : 0 < ε := by simp [ε, he, ennreal.zero_lt_one],
    have : 0 < C⁻¹ * (ε/2) := bot_lt_iff_ne_bot.2 (by simp [hC, (ne_of_lt this).symm, ennreal.mul_eq_zero]),
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
            add_le_add_left' $ canonically_ordered_semiring.mul_le_mul (le_refl _) (le_of_lt hy)
        ... < f x + ε : (ennreal.add_lt_add_iff_left (lt_top_iff_ne_top.2 htop)).2 I
        ... ≤ f x + (e - f x) : add_le_add_left' (min_le_left _ _)
        ... = e : by simp [le_of_lt he] },
    apply filter.mem_sets_of_superset (ball_mem_nhds _ (‹0 < C⁻¹ * (ε/2)›)) this },
end

theorem continuous_edist' : continuous (λp:α×α, edist p.1 p.2) :=
begin
  apply continuous_of_le_add_edist 2 (by simp),
  rintros ⟨x, y⟩ ⟨x', y'⟩,
  calc edist x y ≤ edist x x' + edist x' y' + edist y' y : edist_triangle4 _ _ _ _
    ... = edist x' y' + (edist x x' + edist y y') : by simp [add_comm, edist_comm]
    ... ≤ edist x' y' + (edist (x, y) (x', y') + edist (x, y) (x', y')) :
      add_le_add_left' (add_le_add' (by simp [edist, le_refl]) (by simp [edist, le_refl]))
    ... = edist x' y' + 2 * edist (x, y) (x', y') : by rw [← mul_two, mul_comm]
end

theorem continuous_edist [topological_space β] {f g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λb, edist (f b) (g b)) :=
(hf.prod_mk hg).comp continuous_edist'

theorem tendsto_edist {f g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (nhds a)) (hg : tendsto g x (nhds b)) :
  tendsto (λx, edist (f x) (g x)) x (nhds (edist a b)) :=
have tendsto (λp:α×α, edist p.1 p.2) (nhds (a, b)) (nhds (edist a b)),
  from continuous_iff_continuous_at.mp continuous_edist' (a, b),
(hf.prod_mk hg).comp (by rw [nhds_prod_eq] at this; exact this)

end --section
