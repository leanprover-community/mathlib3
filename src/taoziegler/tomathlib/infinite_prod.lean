import topology.algebra.infinite_sum

noncomputable theory
open finset filter function classical
open_locale topology classical big_operators nnreal

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section has_prod
variables [comm_monoid α] [topological_space α]

def has_prod (f : β → α) (a : α) : Prop := tendsto (λs:finset β, ∏ b in s, f b) at_top (𝓝 a)

/-- `proddable f` means that `f` has some (infinite) product. Use `tprod` to get the value. -/
def proddable (f : β → α) : Prop := ∃a, has_prod f a

/-- `∏' i, f i` is the product of `f` it exists, or 1 otherwise -/
@[irreducible] def tprod {β} (f : β → α) := if h : proddable f then classical.some h else 1

notation `∏'` binders `, ` r:(scoped:67 f, tprod f) := r

lemma proddable.has_prod {f : β → α} (ha : proddable f) : has_prod f (∏' b, f b) :=
by simp [ha, tprod]; exact some_spec ha

lemma has_prod.proddable {f : β → α} {a : α} (h : has_prod f a) : proddable f := ⟨a, h⟩

lemma has_sum_of_mul_iff_has_prod {f : β → α} {a : α} :
  has_sum (additive.of_mul ∘ f) (additive.of_mul a) ↔ has_prod f a := iff.rfl

lemma summable_of_mul_iff_proddable {f : β → α} :
  summable (additive.of_mul ∘ f) ↔ proddable f := iff.rfl

lemma tsum_of_mul_eq_of_mul_tprod (f : β → α) :
  ∑' i, additive.of_mul (f i) = additive.of_mul (∏' i, f i) :=
begin
  rw [tprod, tsum],
  by_cases h : proddable f,
  { rw [dif_pos h, dif_pos],
    refl },
  { rw [dif_neg h, dif_neg],
    { refl },
    { rwa summable_of_mul_iff_proddable } }
end

lemma to_mul_tsum_of_mul_eq_tprod (f : β → α) :
  additive.to_mul (∑' i, additive.of_mul (f i)) = ∏' i, f i := tsum_of_mul_eq_of_mul_tprod f

lemma proddable_of_zero {R : Type*} [comm_semiring R] [topological_space R]
  (f : β → R) (hf : ∃ b, f b = 0) : proddable f :=
begin
  refine ⟨0, _⟩,
  obtain ⟨b, hb⟩ := hf,
  rw has_prod,
  rw tendsto_at_top_nhds,
  intros U hU hU',
  refine ⟨{b}, λ V hV, _⟩,
  have hb' : b ∈ V := singleton_subset_iff.mp hV,
  rwa prod_eq_zero hb' hb
end

lemma has_prod.mul_compl [has_continuous_mul α] {s : set β} {f : β → α} {a b : α}
  (ha : has_prod (f ∘ coe : s → α) a) (hb : has_prod (f ∘ coe : sᶜ → α) b) :
  has_prod f (a * b) :=
begin
  have : ∀ α (g : α → β), additive.to_mul ∘ f ∘ g = (additive.to_mul ∘ f) ∘ g,
  { intros, refl },
  rw ←has_sum_of_mul_iff_has_prod at ha hb ⊢,
  replace ha : has_sum ((additive.of_mul ∘ f) ∘ (coe : s → β)) (additive.of_mul a),
  { exact ha },
  replace hb : has_sum ((additive.of_mul ∘ f) ∘ (coe : sᶜ → β)) (additive.of_mul b),
  { exact hb },
  exact ha.add_compl hb
end

lemma proddable.mul_compl [has_continuous_mul α] {s : set β} {f : β → α}
  (hs : proddable (f ∘ coe : s → α)) (hsc : proddable (f ∘ coe : sᶜ → α)) :
  proddable f :=
(hs.has_prod.mul_compl hsc.has_prod).proddable

end has_prod
