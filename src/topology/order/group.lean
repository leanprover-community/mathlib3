import topology.order.basic
import topology.algebra.group.basic

open set filter
open_locale topology filter

variables {α β : Type*} [topological_space α] [linear_ordered_add_comm_group α] [order_topology α]
variables {l : filter β} {f g : β → α}

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_add_comm_group.topological_add_group : topological_add_group α :=
{ continuous_add :=
    begin
      refine continuous_iff_continuous_at.2 _,
      rintro ⟨a, b⟩,
      refine linear_ordered_add_comm_group.tendsto_nhds.2 (λ ε ε0, _),
      rcases dense_or_discrete 0 ε with (⟨δ, δ0, δε⟩|⟨h₁, h₂⟩),
      { -- If there exists `δ ∈ (0, ε)`, then we choose `δ`-nhd of `a` and `(ε-δ)`-nhd of `b`
        filter_upwards [(eventually_abs_sub_lt a δ0).prod_nhds
          (eventually_abs_sub_lt b (sub_pos.2 δε))],
        rintros ⟨x, y⟩ ⟨hx : |x - a| < δ, hy : |y - b| < ε - δ⟩,
        rw [add_sub_add_comm],
        calc |x - a + (y - b)| ≤ |x - a| + |y - b| : abs_add _ _
        ... < δ + (ε - δ) : add_lt_add hx hy
        ... = ε : add_sub_cancel'_right _ _ },
      { -- Otherwise `ε`-nhd of each point `a` is `{a}`
        have hε : ∀ {x y}, |x - y| < ε → x = y,
        { intros x y h,
          simpa [sub_eq_zero] using h₂ _ h },
        filter_upwards [(eventually_abs_sub_lt a ε0).prod_nhds (eventually_abs_sub_lt b ε0)],
        rintros ⟨x, y⟩ ⟨hx : |x - a| < ε, hy : |y - b| < ε⟩,
        simpa [hε hx, hε hy] }
    end,
  continuous_neg := continuous_iff_continuous_at.2 $ λ a,
    linear_ordered_add_comm_group.tendsto_nhds.2 $ λ ε ε0,
      (eventually_abs_sub_lt a ε0).mono $ λ x hx, by rwa [neg_sub_neg, abs_sub_comm] }

@[continuity]
lemma continuous_abs : continuous (abs : α → α) := continuous_id.max continuous_neg

lemma filter.tendsto.abs {f : β → α} {a : α} {l : filter β} (h : tendsto f l (𝓝 a)) :
  tendsto (λ x, |f x|) l (𝓝 (|a|)) :=
(continuous_abs.tendsto _).comp h

lemma tendsto_zero_iff_abs_tendsto_zero (f : β → α) {l : filter β} :
  tendsto f l (𝓝 0) ↔ tendsto (abs ∘ f) l (𝓝 0) :=
begin
  refine ⟨λ h, (abs_zero : |(0 : α)| = 0) ▸ h.abs, λ h, _⟩,
  have : tendsto (λ a, -|f a|) l (𝓝 0) := (neg_zero : -(0 : α) = 0) ▸ h.neg,
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le this h
    (λ x, neg_abs_le_self $ f x) (λ x, le_abs_self $ f x),
end

lemma nhds_basis_Ioo_pos [no_min_order α] [no_max_order α] (a : α) :
  (𝓝 a).has_basis (λ ε : α, (0 : α) < ε) (λ ε, Ioo (a-ε) (a+ε)) :=
⟨begin
  refine λ t, (nhds_basis_Ioo a).mem_iff.trans ⟨_, _⟩,
  { rintros ⟨⟨l, u⟩, ⟨hl : l < a, hu : a < u⟩, h' : Ioo l u ⊆ t⟩,
    refine ⟨min (a-l) (u-a), by apply lt_min; rwa sub_pos, _⟩,
    rintros x ⟨hx, hx'⟩,
    apply h',
    rw [sub_lt_comm, lt_min_iff, sub_lt_sub_iff_left] at hx,
    rw [← sub_lt_iff_lt_add', lt_min_iff, sub_lt_sub_iff_right] at hx',
    exact ⟨hx.1, hx'.2⟩ },
  { rintros ⟨ε, ε_pos, h⟩,
    exact ⟨(a-ε, a+ε), by simp [ε_pos], h⟩ },
end⟩

lemma nhds_basis_abs_sub_lt [no_min_order α] [no_max_order α] (a : α) :
  (𝓝 a).has_basis (λ ε : α, (0 : α) < ε) (λ ε, {b | |b - a| < ε}) :=
begin
  convert nhds_basis_Ioo_pos a,
  { ext ε,
    change |x - a| < ε ↔ a - ε < x ∧ x < a + ε,
    simp [abs_lt, sub_lt_iff_lt_add, add_comm ε a, add_comm x ε] }
end

variable (α)

lemma nhds_basis_zero_abs_sub_lt [no_min_order α] [no_max_order α] :
  (𝓝 (0 : α)).has_basis (λ ε : α, (0 : α) < ε) (λ ε, {b | |b| < ε}) :=
by simpa using nhds_basis_abs_sub_lt (0 : α)

variable {α}

/-- If `a` is positive we can form a basis from only nonnegative `Ioo` intervals -/
lemma nhds_basis_Ioo_pos_of_pos [no_min_order α] [no_max_order α]
  {a : α} (ha : 0 < a) :
  (𝓝 a).has_basis (λ ε : α, (0 : α) < ε ∧ ε ≤ a) (λ ε, Ioo (a-ε) (a+ε)) :=
⟨ λ t, (nhds_basis_Ioo_pos a).mem_iff.trans
  ⟨λ h, let ⟨i, hi, hit⟩ := h in
    ⟨min i a, ⟨lt_min hi ha, min_le_right i a⟩, trans (Ioo_subset_Ioo
    (sub_le_sub_left (min_le_left i a) a) (add_le_add_left (min_le_left i a) a)) hit⟩,
  λ h, let ⟨i, hi, hit⟩ := h in ⟨i, hi.1, hit⟩ ⟩ ⟩

section

variables [topological_space β] {b : β} {a : α} {s : set β}

lemma continuous.abs (h : continuous f) : continuous (λ x, |f x|) := continuous_abs.comp h

lemma continuous_at.abs (h : continuous_at f b) : continuous_at (λ x, |f x|) b := h.abs

lemma continuous_within_at.abs (h : continuous_within_at f s b) :
  continuous_within_at (λ x, |f x|) s b := h.abs

lemma continuous_on.abs (h : continuous_on f s) : continuous_on (λ x, |f x|) s :=
λ x hx, (h x hx).abs

lemma tendsto_abs_nhds_within_zero : tendsto (abs : α → α) (𝓝[≠] 0) (𝓝[>] 0) :=
(continuous_abs.tendsto' (0 : α) 0 abs_zero).inf $ tendsto_principal_principal.2 $ λ x, abs_pos.2

end

/-- In a linearly ordered additive commutative group with the order topology, if `f` tends to `C`
and `g` tends to `at_top` then `f + g` tends to `at_top`. -/
lemma filter.tendsto.add_at_top {C : α} (hf : tendsto f l (𝓝 C)) (hg : tendsto g l at_top) :
  tendsto (λ x, f x + g x) l at_top :=
begin
  nontriviality α,
  obtain ⟨C', hC'⟩ : ∃ C', C' < C := exists_lt C,
  refine tendsto_at_top_add_left_of_le' _ C' _ hg,
  exact (hf.eventually (lt_mem_nhds hC')).mono (λ x, le_of_lt)
end

/-- In a linearly ordered additive commutative group with the order topology, if `f` tends to `C`
and `g` tends to `at_bot` then `f + g` tends to `at_bot`. -/
lemma filter.tendsto.add_at_bot {C : α} (hf : tendsto f l (𝓝 C)) (hg : tendsto g l at_bot) :
  tendsto (λ x, f x + g x) l at_bot :=
@filter.tendsto.add_at_top αᵒᵈ _ _ _ _ _ _ _ _ hf hg

/-- In a linearly ordered additive commutative group with the order topology, if `f` tends to
`at_top` and `g` tends to `C` then `f + g` tends to `at_top`. -/
lemma filter.tendsto.at_top_add {C : α} (hf : tendsto f l at_top) (hg : tendsto g l (𝓝 C)) :
  tendsto (λ x, f x + g x) l at_top :=
by { conv in (_ + _) { rw add_comm }, exact hg.add_at_top hf }

/-- In a linearly ordered additive commutative group with the order topology, if `f` tends to
`at_bot` and `g` tends to `C` then `f + g` tends to `at_bot`. -/
lemma filter.tendsto.at_bot_add {C : α} (hf : tendsto f l at_bot) (hg : tendsto g l (𝓝 C)) :
  tendsto (λ x, f x + g x) l at_bot :=
by { conv in (_ + _) { rw add_comm }, exact hg.add_at_bot hf }
