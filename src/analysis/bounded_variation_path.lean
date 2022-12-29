import data.real.ennreal
import topology.metric_space.emetric_space
import .length_on
import topology.instances.ennreal

open emetric nnreal set ennreal

open_locale big_operators nnreal ennreal

variables {α β E : Type*} [pseudo_emetric_space E] [linear_order α] [linear_order β]

namespace function

variables (f : α → E) (s : set α)

noncomputable def evariation_on : ennreal :=
  ⨆ l ∈ {l : list α | l.pairwise (≤) ∧ ∀ x ∈ l, x ∈ s}, f.length_on l

lemma length_on_le_evariation_on {l : list α} (hl :  l.pairwise (≤) ∧ ∀ x ∈ l, x ∈ s) :
  f.length_on l ≤ f.evariation_on s := le_supr₂ l hl

def _root_.has_bounded_variation_on := f.evariation_on s ≠ ∞

def _root_.has_locally_bounded_variation_on :=
∀ a b, a ∈ s → b ∈ s → has_bounded_variation_on f (s ∩ Icc a b)

namespace evariation_on

def sorted_list_nonempty : set.nonempty {l : list α | l.pairwise (≤) ∧ ∀ x∈l, x∈s} :=
  ⟨[], list.pairwise.nil, λ x h, (list.not_mem_nil _ h).elim⟩

variables {f} {s} {t : set α}

lemma eps_approx (h : f.evariation_on s ≠ ⊤) (ε : ennreal) (hε : ε ≠ 0) :
  ∃ ll : {l : list α | l.pairwise (≤) ∧ ∀ x ∈ l, x ∈ s},
    f.evariation_on s < f.length_on ll.val + ε  :=
begin
  by_contra' hn,
  apply (ennreal.lt_add_right h hε).not_le,
  dsimp only [evariation_on],
  rw [bsupr_add (sorted_list_nonempty s), supr₂_le_iff],
  rw [set_coe.forall] at hn, exact hn,
end

lemma eq_of_eq_on {f f' : α → E} {s : set α} (h : set.eq_on f f' s) :
  f.evariation_on s = f'.evariation_on s :=
begin
  dsimp only [evariation_on],
  congr' 1 with l : 1,
  congr' 1 with hl : 1,
  exact length_on_congr (λ x xl, h (hl.right x xl)),
end

lemma mono  (hst : t ⊆ s) : f.evariation_on t ≤ f.evariation_on s :=
begin
  apply supr₂_le _,
  exact λ l lp, f.length_on_le_evariation_on s ⟨lp.1, λ _ xh, hst (lp.2 _ xh)⟩,
end

lemma _root_.has_bounded_variation_on.mono
  (h : has_bounded_variation_on f s) (hst : t ⊆ s) : has_bounded_variation_on f t :=
(lt_of_le_of_lt (evariation_on.mono hst) (lt_top_iff_ne_top.2 h)).ne

lemma _root_.has_bounded_variation_on.has_locally_bounded_variation_on
  (h : has_bounded_variation_on f s) : has_locally_bounded_variation_on f s :=
λ x y hx hy, h.mono (inter_subset_left _ _)

lemma constant_on {f : α → E} {s : set α}
  (hf : (f '' s).subsingleton) : f.evariation_on s = 0 :=
begin
  refine le_antisymm (supr₂_le _) zero_le',
  rintros l ⟨lm,ls⟩,
  refine le_of_eq (f.length_on_const _),
  rintro x hx y hy, apply hf; apply set.mem_image_of_mem; apply ls; assumption,
end

@[simp] protected lemma subsingleton (f : α → E) {s : set α} (hs : s.subsingleton) :
  f.evariation_on s = 0 := constant_on (hs.image f)

lemma edist_le {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
  edist (f x) (f y) ≤ f.evariation_on s :=
begin
  rw ←f.length_on_pair,
  wlog hxy : x ≤ y := le_total x y using [x y, y x] tactic.skip, swap,
  { assume hx hy,
    rw [f.length_on_pair, edist_comm,←f.length_on_pair],
    exact this hy hx },
  apply f.length_on_le_evariation_on,
  simp only [hxy, hx, hy, list.pairwise_cons, list.not_mem_nil, is_empty.forall_iff,
             implies_true_iff, list.pairwise.nil, and_self, list.mem_cons_iff, forall_eq_or_imp],
end

lemma _root_.has_bounded_variation_on.dist_le {E : Type*} [pseudo_metric_space E]
  {f : α → E} {s : set α} (h : has_bounded_variation_on f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
  dist (f x) (f y) ≤ (f.evariation_on s).to_real :=
begin
  rw [← ennreal.of_real_le_of_real_iff ennreal.to_real_nonneg, ennreal.of_real_to_real h,
      ← edist_dist],
  exact edist_le hx hy
end

lemma _root_.function.has_bounded_variation_on.sub_le
  {f : α → ℝ} {s : set α} (h : has_bounded_variation_on f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
  f x - f y ≤ (f.evariation_on s).to_real :=
begin
  apply (le_abs_self _).trans,
  rw ← real.dist_eq,
  exact h.dist_le hx hy
end

lemma add_le_union (h : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) :
  f.evariation_on s + f.evariation_on t ≤ f.evariation_on (s ∪ t) :=
begin
  dsimp only [evariation_on],
  apply ennreal.bsupr_add_bsupr_le (sorted_list_nonempty s) (sorted_list_nonempty t),
  rintro ll ⟨llm,lls⟩ lr ⟨lrm,lrt⟩,
  apply (f.length_on_append _ _).trans,
  apply f.length_on_le_evariation_on,
  simp only [list.pairwise_append, list.mem_append, mem_union],
  split,
  { exact ⟨llm, lrm, λ x xl y yr, h x (lls x xl) y (lrt y yr)⟩,  },
  { rintro x (xl|xr), exact or.inl (lls x xl), exact or.inr (lrt x xr), },
end

set_option profiler true

-- TODO : golf some parts with `show_term`
lemma union {x : α} (hs : is_greatest s x) (ht : is_least t x) :
  f.evariation_on (s ∪ t) = f.evariation_on s + f.evariation_on t :=
begin
  apply le_antisymm _ (add_le_union (λ u us v vt, (hs.2 us).trans (ht.2 vt))),
  apply supr₂_le _,
  rintro l ⟨lm,lst⟩,
  rw ←list.take_while_append_drop (≤x) l,
  apply (length_on_le_append_singleton_append f _ x _).trans,
  rw length_on_append_singleton_append,
  refine add_le_add _ _,
  { apply f.length_on_le_evariation_on,
    split,
    { simp only [list.pairwise_append, list.pairwise_cons, list.not_mem_nil, is_empty.forall_iff,
                 implies_true_iff, list.pairwise.nil, list.mem_singleton, forall_eq, true_and],
      split,
      { apply @list.pairwise.sublist _ _ _ l,
        refine list.is_prefix.sublist (list.take_while_prefix _),
        exact lm, },
      { apply list.mem_take_while_imp, }, },
    { simp only [list.mem_append, list.mem_singleton],
      rintro u (ul|rfl),
      { let := list.mem_take_while_imp ul,
        specialize lst u (list.mem_of_mem_take_while ul),
        change u ∈ s ∨ u ∈ t at lst, cases lst,
        { assumption, },
        { cases le_antisymm this (ht.right lst), exact hs.left, }, },
      { exact hs.left, }, } },
  { apply f.length_on_le_evariation_on,
    split,
    { simp only [list.singleton_append, list.pairwise_cons],
      exact ⟨ λ u ul, (lt_of_not_le (list.pairwise_le_drop_while_le_not_le x l lm u ul)).le,
              list.pairwise.sublist (list.drop_while_suffix (≤x)).sublist lm⟩, },
    { simp only [list.singleton_append, list.mem_cons_iff, forall_eq_or_imp],
      refine ⟨ht.left, λ u ul, _⟩,
      specialize lst u (list.mem_of_mem_drop_while ul),
      change u ∈ s ∨ u ∈ t at lst, cases lst,
      { exact ((list.pairwise_le_drop_while_le_not_le x l lm u ul) (hs.right lst)).elim, },
      { assumption, }, }, },
end

lemma Icc_add_Icc {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) (hb : b ∈ s) :
  f.evariation_on (s ∩ Icc a b) + f.evariation_on (s ∩ Icc b c) = f.evariation_on (s ∩ Icc a c) :=
begin
  have A : is_greatest (s ∩ Icc a b) b :=
    ⟨⟨hb, hab, le_rfl⟩, (inter_subset_right _ _).trans (Icc_subset_Iic_self)⟩,
  have B : is_least (s ∩ Icc b c) b :=
    ⟨⟨hb, le_rfl, hbc⟩, (inter_subset_right _ _).trans (Icc_subset_Ici_self)⟩,
  rw [← union A B, ← inter_union_distrib_left, Icc_union_Icc_eq_Icc hab hbc],
end

lemma comp_le_of_monotone_on {φ : β → α} {t :set β}
  (mφ : monotone_on φ t) (φst : t.maps_to φ s) : (f ∘ φ).evariation_on t ≤ f.evariation_on s :=
begin
  simp only [evariation_on, supr₂_le_iff, ←f.length_on_map φ],
  rintro l ls,
  apply f.length_on_le_evariation_on,
  exact ⟨list.pairwise.map_of_maps_to_of_forall φ mφ ls.2 ls.1, list.forall_mem.map φ φst ls.2⟩,
end

lemma comp_le_of_antitone_on {φ : β → α} {t :set β}
  (mφ : antitone_on φ t) (φst : t.maps_to φ s) :
  (f ∘ φ).evariation_on t ≤ f.evariation_on s :=
begin
  simp only [evariation_on, supr₂_le_iff, ←f.length_on_map φ],
  rintro l ⟨lm,ls⟩,
  rw [←f.length_on_reverse, ←list.map_reverse],
  apply f.length_on_le_evariation_on,
  split,
  { apply list.pairwise.map_of_maps_to_of_forall' φ mφ,
    simp only [list.mem_reverse], exact ls,
    simp only [list.pairwise_reverse, ge_iff_le], exact lm, },
  { simp only [list.mem_reverse, list.mem_map, forall_exists_index, and_imp,
               forall_apply_eq_imp_iff₂],
    rintro a al, apply φst (ls a al), },
end

lemma comp_eq_of_monotone_on {t : set β} [nonempty β] {φ : β → α}
  (hφ : monotone_on φ t) (φst : set.maps_to φ t s) (φsur : set.surj_on φ t s) :
  evariation_on (f ∘ φ) t = f.evariation_on s :=
begin
  apply le_antisymm (comp_le_of_monotone_on hφ φst) _,
  let ψ := φ.inv_fun_on t,
  have ψφs : set.eq_on (φ ∘ ψ) id s := φsur.right_inv_on_inv_fun_on,
  have ψts : set.maps_to ψ s t := φsur.maps_to_inv_fun_on,
  have hψ : monotone_on ψ s :=
    function.monotone_on_of_right_inv_on_of_maps_to hφ ψφs ψts,
  change evariation_on (f ∘ id) s ≤ evariation_on (f ∘ φ) t,
  rw ←eq_of_eq_on (ψφs.comp_left : set.eq_on (f ∘ (φ ∘ ψ)) (f ∘ id) s),
  exact comp_le_of_monotone_on hψ ψts,
end

lemma comp_eq_of_antitone_on {t : set β} [nonempty β] {φ : β → α}
  (hφ : antitone_on φ t) (φst : set.maps_to φ t s) (φsur : set.surj_on φ t s) :
  evariation_on (f ∘ φ) t = f.evariation_on s :=
begin
  apply le_antisymm (comp_le_of_antitone_on hφ φst),
  let ψ := φ.inv_fun_on t,
  have ψφs : set.eq_on (φ ∘ ψ) id s := φsur.right_inv_on_inv_fun_on,
  have ψts : set.maps_to ψ s t := φsur.maps_to_inv_fun_on,
  have hψ : antitone_on ψ s :=
    function.antitone_on_of_right_inv_on_of_maps_to hφ ψφs ψts,
  change evariation_on (f ∘ id) s ≤ evariation_on (f ∘ φ) t,
  rw ←eq_of_eq_on (ψφs.comp_left : set.eq_on (f ∘ (φ ∘ ψ)) (f ∘ id) s),
  exact comp_le_of_antitone_on hψ ψts,
end

end evariation_on

end function

/-! ## Monotone functions and bounded variation -/

lemma monotone_on.evariation_on_le {f : α → ℝ} {s : set α} (hf : monotone_on f s) {a b : α}
  (as : a ∈ s) (bs : b ∈ s) :
  f.evariation_on (s ∩ Icc a b) ≤ ennreal.of_real (f b - f a) := sorry

lemma monotone_on.has_locally_bounded_variation_on {f : α → ℝ} {s : set α} (hf : monotone_on f s) :
  has_locally_bounded_variation_on f s :=
λ a b as bs, ((hf.evariation_on_le as bs).trans_lt ennreal.of_real_lt_top).ne

-- TODO : define `p` outside of this: it's the arc-length of `f`.
/-- If a real valued function has bounded variation on a set, then it is a difference of monotone
functions there. -/
lemma has_locally_bounded_variation_on.exists_monotone_on_sub_monotone_on {f : α → ℝ} {s : set α}
  (h : has_locally_bounded_variation_on f s) :
  ∃ (p q : α → ℝ), monotone_on p s ∧ monotone_on q s ∧ f = p - q :=
begin
  rcases eq_empty_or_nonempty s with rfl|hs,
  { exact ⟨f, 0, subsingleton_empty.monotone_on _, subsingleton_empty.monotone_on _,
            by simp only [tsub_zero]⟩ },
  rcases hs with ⟨c, cs⟩,
  let p := λ x, if c ≤ x then (f.evariation_on (s ∩ Icc c x)).to_real
    else -(f.evariation_on (s ∩ Icc x c)).to_real,
  have hp : monotone_on p s,
  { assume x xs y ys hxy,
    dsimp only [p],
    split_ifs with hcx hcy hcy,
    { have : f.evariation_on (s ∩ Icc c x) + f.evariation_on (s ∩ Icc x y)
        = f.evariation_on (s ∩ Icc c y), from function.evariation_on.Icc_add_Icc hcx hxy xs,
      rw [← this, ennreal.to_real_add (h c x cs xs) (h x y xs ys)],
      exact le_add_of_le_of_nonneg le_rfl ennreal.to_real_nonneg },
    { exact (lt_irrefl _ ((not_le.1 hcy).trans_le (hcx.trans hxy))).elim },
    { exact (neg_nonpos.2 ennreal.to_real_nonneg).trans ennreal.to_real_nonneg },
    { simp only [neg_le_neg_iff],
      have : f.evariation_on (s ∩ Icc x y) + f.evariation_on (s ∩ Icc y c)
        = f.evariation_on (s ∩ Icc x c), from function.evariation_on.Icc_add_Icc hxy (not_le.1 hcy).le ys,
      rw [← this, ennreal.to_real_add (h x y xs ys) (h y c ys cs), add_comm],
      exact le_add_of_le_of_nonneg le_rfl ennreal.to_real_nonneg } },
  have hq : monotone_on (λ x, p x - f x) s,
  { assume x xs y ys hxy,
    dsimp only [p],
    split_ifs with hcx hcy hcy,
    { have : f.evariation_on (s ∩ Icc c x) + f.evariation_on (s ∩ Icc x y)
        = f.evariation_on (s ∩ Icc c y), from function.evariation_on.Icc_add_Icc hcx hxy xs,
      rw [← this, ennreal.to_real_add (h c x cs xs) (h x y xs ys)],
      suffices : f y - f x ≤ (f.evariation_on (s ∩ Icc x y)).to_real, by linarith,
      exact (h x y xs ys).sub_le ⟨ys, hxy, le_rfl⟩ ⟨xs, le_rfl, hxy⟩ },
    { exact (lt_irrefl _ ((not_le.1 hcy).trans_le (hcx.trans hxy))).elim },
    { suffices : f y - f x ≤ (f.evariation_on (s ∩ Icc x c)).to_real
        + (f.evariation_on (s ∩ Icc c y)).to_real, by linarith,
      rw [← ennreal.to_real_add (h x c xs cs) (h c y cs ys),
          evariation_on.Icc_add_Icc f (not_le.1 hcx).le hcy cs],
      exact (h x y xs ys).sub_le ⟨ys, hxy, le_rfl⟩ ⟨xs, le_rfl, hxy⟩ },
    { have : f.evariation_on (s ∩ Icc x y) + f.evariation_on (s ∩ Icc y c)
        = f.evariation_on (s ∩ Icc x c), from evariation_on.Icc_add_Icc f hxy (not_le.1 hcy).le ys,
      rw [← this, ennreal.to_real_add (h x y xs ys) (h y c ys cs)],
      suffices : f y - f x ≤ (f.evariation_on (s ∩ Icc x y)).to_real, by linarith,
      exact (h x y xs ys).sub_le ⟨ys, hxy, le_rfl⟩ ⟨xs, le_rfl, hxy⟩ } },
  refine ⟨p, λ x, p x - f x, hp, hq, _⟩,
  ext x,
  dsimp,
  abel,
end


/-! ## Lipschitz functions and bounded variation -/

lemma lipschitz_on_with.comp_evariation_on_le {f : E → F} {C : ℝ≥0} {t : set E}
  (h : lipschitz_on_with C f t) {g : α → E} {s : set α} (hg : maps_to g s t) :
  (f ∘ g).evariation_on s ≤ C * g.evariation_on s :=
begin
  apply supr_le _,
  rintros ⟨n, ⟨u, hu, us⟩⟩,
  calc
  ∑ i in finset.range n, edist (f (g (u (i+1)))) (f (g (u i)))
      ≤ ∑ i in finset.range n, C * edist (g (u (i+1))) (g (u i)) :
    finset.sum_le_sum (λ i hi, h (hg (us _)) (hg (us _)))
  ... = C * ∑ i in finset.range n, edist (g (u (i+1))) (g (u i)) : by rw finset.mul_sum
  ... ≤ C * evariation_on g s : mul_le_mul_left' (evariation_on.sum_le _ _ hu us) _
end

lemma lipschitz_on_with.comp_has_bounded_variation_on {f : E → F} {C : ℝ≥0} {t : set E}
  (hf : lipschitz_on_with C f t) {g : α → E} {s : set α} (hg : maps_to g s t)
  (h : has_bounded_variation_on g s) :
  has_bounded_variation_on (f ∘ g) s :=
begin
  dsimp [has_bounded_variation_on] at h,
  apply ne_of_lt,
  apply (hf.comp_evariation_on_le hg).trans_lt,
  simp [lt_top_iff_ne_top, h],
end

lemma lipschitz_on_with.comp_has_locally_bounded_variation_on {f : E → F} {C : ℝ≥0} {t : set E}
  (hf : lipschitz_on_with C f t) {g : α → E} {s : set α} (hg : maps_to g s t)
  (h : has_locally_bounded_variation_on g s) :
  has_locally_bounded_variation_on (f ∘ g) s :=
λ x y xs ys, hf.comp_has_bounded_variation_on (hg.mono_left (inter_subset_left _ _)) (h x y xs ys)

lemma lipschitz_with.comp_has_bounded_variation_on {f : E → F} {C : ℝ≥0}
  (hf : lipschitz_with C f) {g : α → E} {s : set α} (h : has_bounded_variation_on g s) :
  has_bounded_variation_on (f ∘ g) s :=
(hf.lipschitz_on_with univ).comp_has_bounded_variation_on (maps_to_univ _ _) h

lemma lipschitz_with.comp_has_locally_bounded_variation_on {f : E → F} {C : ℝ≥0}
  (hf : lipschitz_with C f) {g : α → E} {s : set α} (h : has_locally_bounded_variation_on g s) :
  has_locally_bounded_variation_on (f ∘ g) s :=
(hf.lipschitz_on_with univ).comp_has_locally_bounded_variation_on (maps_to_univ _ _) h

lemma lipschitz_on_with.has_locally_bounded_variation_on {f : ℝ → E} {C : ℝ≥0} {s : set ℝ}
  (hf : lipschitz_on_with C f s) : has_locally_bounded_variation_on f s :=
hf.comp_has_locally_bounded_variation_on (maps_to_id _)
  (@monotone_on_id ℝ _ s).has_locally_bounded_variation_on

lemma lipschitz_with.has_locally_bounded_variation_on {f : ℝ → E} {C : ℝ≥0}
  (hf : lipschitz_with C f) (s : set ℝ) : has_locally_bounded_variation_on f s :=
(hf.lipschitz_on_with s).has_locally_bounded_variation_on


/-! ## Almost everywhere differentiability of functions with locally bounded variation -/

namespace has_locally_bounded_variation_on

/-- A bounded variation function into `ℝ` is differentiable almost everywhere. Superseded by
`ae_differentiable_within_at_of_mem`. -/
theorem ae_differentiable_within_at_of_mem_real
  {f : ℝ → ℝ} {s : set ℝ} (h : has_locally_bounded_variation_on f s) :
  ∀ᵐ x, x ∈ s → differentiable_within_at ℝ f s x :=
begin
  obtain ⟨p, q, hp, hq, fpq⟩ : ∃ p q, monotone_on p s ∧ monotone_on q s ∧ f = p - q,
    from h.exists_monotone_on_sub_monotone_on,
  filter_upwards [hp.ae_differentiable_within_at_of_mem, hq.ae_differentiable_within_at_of_mem]
    with x hxp hxq xs,
  have fpq : ∀ x, f x = p x - q x, by simp [fpq],
  refine ((hxp xs).sub (hxq xs)).congr (λ y hy, fpq y) (fpq x),
end

/-- A bounded variation function into a finite dimensional product vector space is differentiable
almost everywhere. Superseded by `ae_differentiable_within_at_of_mem`. -/
theorem ae_differentiable_within_at_of_mem_pi {ι : Type*} [fintype ι]
  {f : ℝ → (ι → ℝ)} {s : set ℝ} (h : has_locally_bounded_variation_on f s) :
  ∀ᵐ x, x ∈ s → differentiable_within_at ℝ f s x :=
begin
  have A : ∀ (i : ι), lipschitz_with 1 (λ (x : ι → ℝ), x i) := λ i, lipschitz_with.eval i,
  have : ∀ (i : ι), ∀ᵐ x, x ∈ s → differentiable_within_at ℝ (λ (x : ℝ), f x i) s x,
  { assume i,
    apply ae_differentiable_within_at_of_mem_real,
    exact lipschitz_with.comp_has_locally_bounded_variation_on (A i) h },
  filter_upwards [ae_all_iff.2 this] with x hx xs,
  exact differentiable_within_at_pi.2 (λ i, hx i xs),
end

/-- A real function into a finite dimensional real vector space with bounded variation on a set
is differentiable almost everywhere in this set. -/
theorem ae_differentiable_within_at_of_mem
  {f : ℝ → V} {s : set ℝ} (h : has_locally_bounded_variation_on f s) :
  ∀ᵐ x, x ∈ s → differentiable_within_at ℝ f s x :=
begin
  let A := (basis.of_vector_space ℝ V).equiv_fun.to_continuous_linear_equiv,
  suffices H : ∀ᵐ x, x ∈ s → differentiable_within_at ℝ (A ∘ f) s x,
  { filter_upwards [H] with x hx xs,
    have : f = (A.symm ∘ A) ∘ f,
      by simp only [continuous_linear_equiv.symm_comp_self, function.comp.left_id],
    rw this,
    exact A.symm.differentiable_at.comp_differentiable_within_at x (hx xs) },
  apply ae_differentiable_within_at_of_mem_pi,
  exact A.lipschitz.comp_has_locally_bounded_variation_on h,
end

/-- A real function into a finite dimensional real vector space with bounded variation on a set
is differentiable almost everywhere in this set. -/
theorem ae_differentiable_within_at
  {f : ℝ → V} {s : set ℝ} (h : has_locally_bounded_variation_on f s) (hs : measurable_set s) :
  ∀ᵐ x ∂(volume.restrict s), differentiable_within_at ℝ f s x :=
begin
  rw ae_restrict_iff' hs,
  exact h.ae_differentiable_within_at_of_mem
end

/-- A real function into a finite dimensional real vector space with bounded variation
is differentiable almost everywhere. -/
theorem ae_differentiable_at {f : ℝ → V} (h : has_locally_bounded_variation_on f univ) :
  ∀ᵐ x, differentiable_at ℝ f x :=
begin
  filter_upwards [h.ae_differentiable_within_at_of_mem] with x hx,
  rw differentiable_within_at_univ at hx,
  exact hx (mem_univ _),
end

end has_locally_bounded_variation_on

/-- A real function into a finite dimensional real vector space which is Lipschitz on a set
is differentiable almost everywhere in this set . -/
lemma lipschitz_on_with.ae_differentiable_within_at_of_mem
  {C : ℝ≥0} {f : ℝ → V} {s : set ℝ} (h : lipschitz_on_with C f s) :
  ∀ᵐ x, x ∈ s → differentiable_within_at ℝ f s x :=
h.has_locally_bounded_variation_on.ae_differentiable_within_at_of_mem

/-- A real function into a finite dimensional real vector space which is Lipschitz on a set
is differentiable almost everywhere in this set. -/
lemma lipschitz_on_with.ae_differentiable_within_at
  {C : ℝ≥0} {f : ℝ → V} {s : set ℝ} (h : lipschitz_on_with C f s) (hs : measurable_set s) :
  ∀ᵐ x ∂(volume.restrict s), differentiable_within_at ℝ f s x :=
h.has_locally_bounded_variation_on.ae_differentiable_within_at hs

/-- A real Lipschitz function into a finite dimensional real vector space is differentiable
almost everywhere. -/
lemma lipschitz_with.ae_differentiable_at
  {C : ℝ≥0} {f : ℝ → V} (h : lipschitz_with C f) :
  ∀ᵐ x, differentiable_at ℝ f x :=
(h.has_locally_bounded_variation_on univ).ae_differentiable_at
