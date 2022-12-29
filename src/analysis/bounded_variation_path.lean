import data.real.ennreal
import topology.metric_space.emetric_space
import .length_on
import topology.instances.ennreal

open emetric nnreal set ennreal

set_option profiler true


namespace function

variables {α β E : Type*} [pseudo_emetric_space E] [linear_order α] [linear_order β]
variables (f : α → E) (s : set α)


def sorted_list_nonempty : set.nonempty {l : list α | l.pairwise (≤) ∧ ∀ x∈l, x∈s} :=
  ⟨[], list.pairwise.nil, λ x h, (list.not_mem_nil _ h).elim⟩

noncomputable def evariation_on :=
  ⨆ l ∈ {l : list α | l.pairwise (≤) ∧ ∀ x ∈ l, x ∈ s}, f.length_on l

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

def has_bounded_variation_on := evariation_on f s ≠ ⊤

def has_locally_bounded_variation_on :=
∀ a b, a ∈ s → b ∈ s → has_bounded_variation_on f (s ∩ Icc a b)

lemma eq_of_eq_on {f f' : α → E} {s : set α} (h : set.eq_on f f' s) :
  evariation_on f s = evariation_on f' s :=
begin
  dsimp only [evariation_on],
  congr' 1 with l : 1,
  congr' 1 with hl : 1,
  exact length_on_congr (λ x xl, h (hl.right x xl)),
end

end function


/-



lemma sum_le
  (f : α → E) {s : set α} (n : ℕ) {u : ℕ → α} (hu : monotone u) (us : ∀ i, u i ∈ s) :
  ∑ i in finset.range n, edist (f (u (i+1))) (f (u i)) ≤ evariation_on f s :=


lemma sum_le_of_monotone_on_Iic
  (f : α → E) {s : set α} {n : ℕ} {u : ℕ → α} (hu : monotone_on u (Iic n))
  (us : ∀ i ≤ n, u i ∈ s) :
  ∑ i in finset.range n, edist (f (u (i+1))) (f (u i)) ≤ evariation_on f s :=


lemma sum_le_of_monotone_on_Icc
  (f : α → E) {s : set α} {m n : ℕ} {u : ℕ → α} (hu : monotone_on u (Icc m n))
  (us : ∀ i ∈ Icc m n, u i ∈ s) :
  ∑ i in finset.Ico m n, edist (f (u (i+1))) (f (u i)) ≤ evariation_on f s :=


lemma mono (f : α → E) {s t : set α} (hst : t ⊆ s) :
  evariation_on f t ≤ evariation_on f s :=


lemma _root_.has_bounded_variation_on.mono {f : α → E} {s : set α}
  (h : has_bounded_variation_on f s) {t : set α} (ht : t ⊆ s) :
  has_bounded_variation_on f t :=

lemma _root_.has_bounded_variation_on.has_locally_bounded_variation_on {f : α → E} {s : set α}
  (h : has_bounded_variation_on f s) : has_locally_bounded_variation_on f s :=

lemma constant_on {f : α → E} {s : set α}
  (hf : (f '' s).subsingleton) : evariation_on f s = 0 :=


@[simp] protected lemma subsingleton (f : α → E) {s : set α} (hs : s.subsingleton) :
  evariation_on f s = 0 := constant_on (hs.image f)

lemma edist_le (f : α → E) {s : set α} {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
  edist (f x) (f y) ≤ evariation_on f s :=


lemma _root_.has_bounded_variation_on.dist_le {E : Type*} [pseudo_metric_space E]
  {f : α → E} {s : set α} (h : has_bounded_variation_on f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
  dist (f x) (f y) ≤ (evariation_on f s).to_real :=


lemma _root_.has_bounded_variation_on.sub_le
  {f : α → ℝ} {s : set α} (h : has_bounded_variation_on f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
  f x - f y ≤ (evariation_on f s).to_real :=


/-- Consider a monotone function `u` parameterizing some points of a set `s`. Given `x ∈ s`, then
one can find another monotone function `v` parameterizing the same points as `u`, with `x` added.
In particular, the variation of a function along `u` is bounded by its variation along `v`. -/
lemma add_point (f : α → E) {s : set α} {x : α} (hx : x ∈ s)
  (u : ℕ → α) (hu : monotone u) (us : ∀ i, u i ∈ s) (n : ℕ) :
  ∃ (v : ℕ → α) (m : ℕ), monotone v ∧ (∀ i, v i ∈ s) ∧ x ∈ v '' (Iio m) ∧
    ∑ i in finset.range n, edist (f (u (i+1))) (f (u i)) ≤
      ∑ j in finset.range m, edist (f (v (j+1))) (f (v j)) :=


/-- The variation of a function on the union of two sets `s` and `t`, with `s` to the left of `t`,
bounds the sum of the variations along `s` and `t`. -/
lemma add_le_union (f : α → E) {s t : set α} (h : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) :
  evariation_on f s + evariation_on f t ≤ evariation_on f (s ∪ t) :=


/-- If a set `s` is to the left of a set `t`, and both contain the boundary point `x`, then
the variation of `f` along `s ∪ t` is the sum of the variations. -/
lemma union (f : α → E) {s t : set α} {x : α} (hs : is_greatest s x) (ht : is_least t x) :
  evariation_on f (s ∪ t) = evariation_on f s + evariation_on f t :=


lemma Icc_add_Icc (f : α → E) {s : set α} {a b c : α}
  (hab : a ≤ b) (hbc : b ≤ c) (hb : b ∈ s) :
  evariation_on f (s ∩ Icc a b) + evariation_on f (s ∩ Icc b c) = evariation_on f (s ∩ Icc a c) :=


lemma comp_le_of_monotone_on (f : α → E) {s : set α} {t : set β} (φ : β → α)
  (hφ : monotone_on φ t) (φst : set.maps_to φ t s) :
  evariation_on (f ∘ φ) t ≤ evariation_on f s :=


lemma comp_le_of_antitone_on (f : α → E) {s : set α} {t : set β} (φ : β → α)
  (hφ : antitone_on φ t) (φst : set.maps_to φ t s) :
  evariation_on (f ∘ φ) t ≤ evariation_on f s :=


lemma comp_eq_of_monotone_on (f : α → E) {s : set α} {t : set β} [nonempty β] (φ : β → α)
  (hφ : monotone_on φ t) (φst : set.maps_to φ t s) (φsur : set.surj_on φ t s) :
  evariation_on (f ∘ φ) t = evariation_on f s :=

lemma comp_eq_of_antitone_on (f : α → E) {s : set α} {t : set β} [nonempty β] (φ : β → α)
  (hφ : antitone_on φ t) (φst : set.maps_to φ t s) (φsur : set.surj_on φ t s) :
  evariation_on (f ∘ φ) t = evariation_on f s :=


end evariation_on

/-! ## Monotone functions and bounded variation -/

lemma monotone_on.evariation_on_le {f : α → ℝ} {s : set α} (hf : monotone_on f s) {a b : α}
  (as : a ∈ s) (bs : b ∈ s) :
  evariation_on f (s ∩ Icc a b) ≤ ennreal.of_real (f b - f a) :=


lemma monotone_on.has_locally_bounded_variation_on {f : α → ℝ} {s : set α} (hf : monotone_on f s) :
  has_locally_bounded_variation_on f s :=
λ a b as bs, ((hf.evariation_on_le as bs).trans_lt ennreal.of_real_lt_top).ne

/-- If a real valued function has bounded variation on a set, then it is a difference of monotone
functions there. -/
lemma has_locally_bounded_variation_on.exists_monotone_on_sub_monotone_on {f : α → ℝ} {s : set α}
  (h : has_locally_bounded_variation_on f s) :
  ∃ (p q : α → ℝ), monotone_on p s ∧ monotone_on q s ∧ f = p - q :=



/-! ## Lipschitz functions and bounded variation -/

lemma lipschitz_on_with.comp_evariation_on_le {f : E → F} {C : ℝ≥0} {t : set E}
  (h : lipschitz_on_with C f t) {g : α → E} {s : set α} (hg : maps_to g s t) :
  evariation_on (f ∘ g) s ≤ C * evariation_on g s :=


lemma lipschitz_on_with.comp_has_bounded_variation_on {f : E → F} {C : ℝ≥0} {t : set E}
  (hf : lipschitz_on_with C f t) {g : α → E} {s : set α} (hg : maps_to g s t)
  (h : has_bounded_variation_on g s) :
  has_bounded_variation_on (f ∘ g) s :=


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

/-- A bounded variation function into `ℝ` is differentiable almost everywhere. Superseded by
`ae_differentiable_within_at_of_mem`. -/
theorem ae_differentiable_within_at_of_mem_real
  {f : ℝ → ℝ} {s : set ℝ} (h : has_locally_bounded_variation_on f s) :
  ∀ᵐ x, x ∈ s → differentiable_within_at ℝ f s x :=

/-- A bounded variation function into a finite dimensional product vector space is differentiable
almost everywhere. Superseded by `ae_differentiable_within_at_of_mem`. -/
theorem ae_differentiable_within_at_of_mem_pi {ι : Type*} [fintype ι]
  {f : ℝ → (ι → ℝ)} {s : set ℝ} (h : has_locally_bounded_variation_on f s) :
  ∀ᵐ x, x ∈ s → differentiable_within_at ℝ f s x :=

/-- A real function into a finite dimensional real vector space with bounded variation on a set
is differentiable almost everywhere in this set. -/
theorem ae_differentiable_within_at_of_mem
  {f : ℝ → V} {s : set ℝ} (h : has_locally_bounded_variation_on f s) :
  ∀ᵐ x, x ∈ s → differentiable_within_at ℝ f s x :=

/-- A real function into a finite dimensional real vector space with bounded variation on a set
is differentiable almost everywhere in this set. -/
theorem ae_differentiable_within_at
  {f : ℝ → V} {s : set ℝ} (h : has_locally_bounded_variation_on f s) (hs : measurable_set s) :
  ∀ᵐ x ∂(volume.restrict s), differentiable_within_at ℝ f s x :=

/-- A real function into a finite dimensional real vector space with bounded variation
is differentiable almost everywhere. -/
theorem ae_differentiable_at {f : ℝ → V} (h : has_locally_bounded_variation_on f univ) :
  ∀ᵐ x, differentiable_at ℝ f x :=

end has_locally_bounded_variation_on

lemma lipschitz_on_with.ae_differentiable_within_at_of_mem
  {C : ℝ≥0} {f : ℝ → V} {s : set ℝ} (h : lipschitz_on_with C f s) :
  ∀ᵐ x, x ∈ s → differentiable_within_at ℝ f s x :=
h.has_locally_bounded_variation_on.ae_differentiable_within_at_of_mem

lemma lipschitz_on_with.ae_differentiable_within_at
  {C : ℝ≥0} {f : ℝ → V} {s : set ℝ} (h : lipschitz_on_with C f s) (hs : measurable_set s) :
  ∀ᵐ x ∂(volume.restrict s), differentiable_within_at ℝ f s x :=

lemma lipschitz_with.ae_differentiable_at
  {C : ℝ≥0} {f : ℝ → V} (h : lipschitz_with C f) :
  ∀ᵐ x, differentiable_at ℝ f x :=

-/

/--
The path length of `f` is the supremum over all strictly increasing partitions `l`
of the length of `f` for `l`
-/

lemma path_length_comp_mono (φ : γ → β)  (t :set γ) (mφ : monotone_on φ t) (φst : t.maps_to φ s) :
  (f ∘ φ).evariation_on t ≤ f.evariation_on s :=
begin
  simp only [evariation_on, supr₂_le_iff, ←f.length_on_map φ],
  rintro l ls,
  refine @le_supr₂ _ _ _ _ (λ l H, f.length_on l) (l.map φ) _,
  exact ⟨list.pairwise.map_of_maps_to_of_forall φ mφ ls.2 ls.1, list.forall_mem.map φ φst ls.2⟩,
end

lemma path_length_comp_anti (φ : γ → β)  (t :set γ) (mφ : antitone_on φ t) (φst : t.maps_to φ s) :
  (f ∘ φ).evariation_on t ≤ f.evariation_on s :=
begin
  simp only [evariation_on, supr₂_le_iff, ←f.length_on_map φ],
  rintro l ls,
  rw [←f.length_on_reverse, ←list.map_reverse],
  refine @le_supr₂ _ _ _ _  (λ l H, f.length_on l) _ _,
  split,
  apply list.pairwise.map_of_maps_to_of_forall' φ mφ sorry (list.pairwise_reverse.mpr ls.1),
  sorry,
end

lemma path_length_reparametrize_mono (φ : γ → β) (mφ : monotone φ) (sφ : surjective φ) :
  (f ∘ φ).path_length = f.path_length :=
begin
  apply le_antisymm,
  apply f.path_length_comp_mono φ mφ,

  obtain ⟨ψ,φψ⟩ := sφ.has_right_inverse,

  convert (f ∘ φ).path_length_comp_mono ψ (right_inverse_monotone φ mφ ψ φψ),
  ext x,
  simp only [comp_app, φψ x],
end

lemma path_length_reparametrize_anti (φ : γ → β) (mφ : antitone φ) (sφ : surjective φ) :
  (f ∘ φ).path_length = f.path_length :=
begin
  apply le_antisymm,
  apply f.path_length_comp_anti φ mφ,

  obtain ⟨ψ,φψ⟩ := sφ.has_right_inverse,

  convert (f ∘ φ).path_length_comp_anti ψ (right_inverse_antitone φ mφ ψ φψ),
  ext x,
  simp only [comp_app, φψ x],
end

lemma path_length_ge_parts (l r : set β) (lr : ∀ x ∈ l, ∀ y ∈ r, x ≤ y) :
  (f ∘ (coe : subtype l → β)).path_length
  + (f ∘ (coe : subtype r → β)).path_length ≤ (f.path_length) :=
begin
  apply ennreal.bsupr_add_bsupr_le sorted_list_nonempty sorted_list_nonempty,
  rintro left lefts right rights,
  simp_rw [←length_on_map f coe],
  apply (f.length_on_append _ _).trans,
  dsimp only [path_length],
  refine @le_supr₂ _ _ _ _ (λ l H, f.length_on l) _ _,
  rw [mem_set_of, list.pairwise_append],
  refine ⟨list.pairwise.map _ (λ a b h, h) lefts,
          list.pairwise.map _ (λ a b h, h) rights,
          λ x xleft y yright, _⟩,
  simp only [list.mem_map, subtype.exists, subtype.coe_mk, exists_and_distrib_right,
             exists_eq_right] at xleft yright,
  obtain ⟨xl,xleft⟩ := xleft,
  obtain ⟨yr,yright⟩ := yright,
  exact lr x xl y yr,
end

lemma path_length_glue_split (m : β) :
  f.path_length = (f ∘ (coe : {x // x ≤ m} → β)).path_length
                + (f ∘ (coe : {x // m ≤ x} → β)).path_length :=
begin
  dsimp only [path_length],
  apply le_antisymm,
  { rw supr₂_le_iff,
    rintro l ls,
    rw ←list.take_while_append_drop (≤m) l,
    apply (length_on_le_append_singleton_append f _ m _).trans,
    rw length_on_append_singleton_append,
    refine add_le_add _ _,
    { transitivity' (f ∘ coe).length_on (l.take_while_subtype m ++ [⟨m,le_refl m⟩]),
      { rw [←f.length_on_map coe, list.map_append, list.take_while_subtype_map_coe,
            list.map, subtype.coe_mk],
        exact le_refl _, },
      { refine @le_supr₂ _ _ _ _ (λ l H, length_on (f ∘ coe) l) _ _,
        simp only [list.pairwise_append, mem_set_of_eq, list.mem_singleton],
        refine ⟨list.take_while_subtype_pairwise_le _ _, list.pairwise_singleton _ _, _⟩,
        rintro y yl _ rfl,
        exact list.take_while_subtype_le_base m l y yl, }, },
    { transitivity' (f ∘ coe).length_on
        ([(⟨m,le_refl m⟩ : {x // m ≤ x})] ++ (l.drop_while_subtype_ge m ls)),
      { rw [←f.length_on_map coe, list.map_append, list.drop_while_subtype_ge_map_coe,
            list.map, subtype.coe_mk],
        exact le_refl _, },
      { refine @le_supr₂ _ _ _ _ (λ l H, length_on (f ∘ coe) l) _ _,
        simp only [list.singleton_append, mem_set_of_eq, list.pairwise_cons,
                   subtype.mk_le_mk],
        refine ⟨list.drop_while_subtype_ge_ge_base _ _ _,
                list.drop_while_subtype_ge_pairwise_le _ _ _⟩, }, }, },
  { apply path_length_ge_parts,
    rintro x xm y my, apply le_trans xm my, }, -- `xm.trans my` doesn't work
end

/--
A path is rectifiable if any of its restriction to a close interval has finite length
-/
def is_rectifiable :=
  ∀ (a b : β), (f ∘ (λ x : Icc a b, x.val)).path_length ≠ ⊤

end path_length



end function
