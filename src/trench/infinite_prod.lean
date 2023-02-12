import topology.algebra.infinite_sum

noncomputable theory
open finset filter function classical
open_locale topology classical big_operators nnreal

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section
variables [comm_monoid α] [topological_space α]

structure has_prod (f : β → α) (a : α) : Prop :=
(finite_not_unit : {b | ¬ is_unit (f b)}.finite)
(tendsto_units : ∃ x : αˣ, tendsto (λ s : finset β, ∏ b in (s.filter (λ i, is_unit (f i))), f b) at_top (𝓝 x))
(prod_eq : a = tendsto_units.some * ∏ b in finite_not_unit.to_finset, f b)

def converges_prod (f : β → α) : Prop := ∃ (a : α), has_prod f a

lemma has_prod_zero_iff_converges_prod_and_exists_zero {f : β → ℝ} :
  has_prod f 0 ↔ converges_prod f ∧ ∃ i, f i = 0 :=
begin
  split,
  { intro h,
    have := h.prod_eq,
    simp only [zero_eq_mul, false_or, prod_eq_zero_iff, units.ne_zero, set.finite.mem_to_finset,
               set.mem_set_of_eq, exists_prop] at this,
    obtain ⟨i, -, hi⟩ := this,
    exact ⟨⟨_, h⟩, i, hi⟩ },
  { rintro ⟨⟨a, hf⟩, i, h⟩,
    refine ⟨hf.finite_not_unit, hf.tendsto_units, _⟩,
    simp only [prod_eq_zero_iff, zero_eq_mul, units.ne_zero, set.finite.mem_to_finset,
               set.mem_set_of_eq, exists_prop, false_or],
    use i,
    simp [h] }
end

lemma has_prod_ratio {f : β → ℝ} {a : ℝ} (hf : has_prod f a) :
  tendsto (λ sb : finset β × β, (∏ b in (sb.1.filter (λ i, is_unit (f i))), f b) / ∏ b in (sb.1.filter (λ i, is_unit (f i))).erase sb.2, f b) cofinite (𝓝 1) :=
begin
  obtain ⟨x, hx⟩ := hf.tendsto_units,
  simp_rw div_eq_mul_inv,
  rw ←mul_inv_cancel x.is_unit.ne_zero,
  -- have := tendsto.fst
  -- have := hx.imp _,
  -- rw tendsto_prod_iff
  -- intros U hU,
  -- rw filter.mem_map,
  -- simp,
  -- refine (tendsto_mul _).map,
end
#exit

lemma thm11 (f g : β → ℝ) (ξ η : ℝ) (hf : tendsto f cofinite (𝓝 ξ))
  (hg : tendsto g cofinite (𝓝 η)) (hx : ∀ x, is_unit (f x)) (hξ : is_unit ξ) :
  tendsto (λ i, g i / f i) cofinite (𝓝 (η / ξ)) :=
begin
  simp_rw div_eq_mul_inv,
  refine hg.mul ((real.tendsto_inv hξ.ne_zero).comp hf),
  -- refine tendsto.mul
  -- have := real.continuous_
  -- intros s hs,
  -- rw filter.mem_map,
end

lemma thm11a (f : β → ℝ) (ξ : ℝ) (hf : tendsto f cofinite (𝓝 ξ))
  (hx : ∀ x, is_unit (f x)) (hξ : is_unit ξ) :
  tendsto (λ x, (f x)⁻¹) cofinite (𝓝 ξ⁻¹) :=
-- sorry
begin
  refine (real.tendsto_inv hξ.ne_zero).comp hf,
  -- refine real.continuous_inv.continous_on
  -- refine (continuous.tendsto _ _).comp hf,
end


#exit
  -- is_unit a ∧
  -- (∀ᶠ b in cofinite, is_unit (f b)) ∧
  -- tendsto (λs:finset β, ∏ b in s, f b) at_top (𝓝 a)

variables {f : β → α} {a : α}

lemma has_prod.is_unit (h : has_prod f a) : is_unit a := h.left
lemma has_prod.eventually_is_unit (h : has_prod f a) :
  ∀ᶠ b in cofinite, is_unit (f b) :=
h.right.left
lemma has_prod.tendsto (h : has_prod f a) :
  tendsto (λs:finset β, ∏ b in s, f b) at_top (𝓝 a) :=
h.right.right

end

section comm_group

variables [comm_group_with_zero α] [topological_space α]
variables {f : β → α} {a : α}

lemma has_prod.ne_zero (h : has_prod f a) : a ≠ 0 := h.is_unit.ne_zero

lemma has_prod.eventually_ne_zero (h : has_prod f a) :
  ∀ᶠ b in cofinite, f b ≠ 0 :=
h.eventually_is_unit.mono (λ _, is_unit.ne_zero)

end comm_group

section
variables [comm_monoid α] [topological_space α]

def converges (f : β → α) : Prop := ∃ a, has_prod f a
def converges_absolutely [has_add α] [has_abs α] (f : β → α) : Prop :=
  ∃ a, has_prod (λ b, 1 + |f b|) a

variables {f : β → α} {a : α}

-- lemma converges_iff_summable_log :
--   converges f ↔ summable (λ i, real.log (f i))

lemma converges_absolutely.converges [has_add α] [has_abs α] (h : converges_absolutely f) :
  converges f :=
begin
  obtain ⟨a, h⟩ := h,

end

-- lemma has_prod.is_unit (h : has_prod f a) : is_unit a := h.left
-- lemma has_prod.eventually_is_unit (h : has_prod f a) :
--   ∀ᶠ b in cofinite, is_unit (f b) :=
-- h.right.left
-- lemma has_prod.tendsto (h : has_prod f a) :
--   tendsto (λs:finset β, ∏ b in s, f b) at_top (𝓝 a) :=
-- h.right.right

end
