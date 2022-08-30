import data.real.basic
import data.real.pointwise
import dynamics.periodic_pts
import topology.continuous_function.basic
import topology.instances.real
import data.list.cycle
import linear_algebra.affine_space.midpoint
import data.seq.seq
import data.stream.init

open set

section prereq

variables {f : ℝ → ℝ} {I I₁ I₂ I₃ J J₁ J₂ : set ℝ}

lemma finset.inj_on_iff_surj_on {α β : Type*} {f : α → β} {s : finset α} {t : finset β}
  (hst : s.card = t.card) (hf : set.maps_to f s t) :
  set.inj_on f s ↔ set.surj_on f s t :=
begin
  split,
  { intros hinj x hx,
    obtain ⟨y, hy, rfl⟩ := finset.surj_on_of_inj_on_of_card_le _ hf _ hst.ge x hx,
    refine ⟨_, hy, rfl⟩,
    intros i j hi hj,
    exact hinj hi hj },
  intros hsurj i hi j hj,
  refine finset.inj_on_of_surj_on_of_card_le _ hf (λ b hb, _) hst.le hi hj,
  obtain ⟨_, h', rfl⟩ := hsurj hb,
  exact ⟨_, h', rfl⟩,
end

lemma finset.min'_le_max' {α : Type*} [linear_order α] {s : finset α} (hs : s.nonempty) :
  s.min' hs ≤ s.max' hs :=
finset.min'_le s _ (finset.max'_mem _ _)

lemma set.inj_on.iterate {α : Type*} {f : α → α} {s : set α}
  (hf : set.maps_to f s s) (f' : set.inj_on f s) :
  ∀ {n}, set.inj_on (f^[n]) s
| 0 x hx y hy t := t
| (n+1) x hx y hy t := f' hx hy $ set.inj_on.iterate (hf hx) (hf hy) t

lemma iterate_inj_on_aux__aux {α : Type*} {f : α → α} {s : set α}
  (hf : set.maps_to f s s) (hf' : set.inj_on f s) {x : α} (hx : x ∈ s) {n k : ℕ} :
  (f^[n+k] x) = (f^[n] x) → (f^[k] x) = x :=
begin
  intro h,
  rw function.iterate_add_apply at h,
  apply set.inj_on.iterate hf hf' (hf.iterate _ hx) hx h,
end

lemma iterate_inj_on_aux {α : Type*} {f : α → α} {s : set α}
  (hf : set.maps_to f s s) (hf' : set.inj_on f s) {x : α} (hx : x ∈ s) :
  ∀ {m n}, m ≤ n → (f^[m] x) = (f^[n] x) → (f^[n-m] x) = x :=
begin
  intros m n hmn i,
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le hmn,
  rw [add_tsub_cancel_left, iterate_inj_on_aux__aux hf hf' hx i.symm],
end

lemma has_period_of_maps_to {α : Type*} {f : α → α} {s : finset α}
  (hf : set.maps_to f s s) (hf' : set.inj_on f s) {x : α} (hx : x ∈ s) :
  ∃ n, 0 < n ∧ n ≤ s.card ∧ function.is_periodic_pt f n x :=
begin
  classical,
  let t := (finset.range s.card).image (λ i, f^[i+1] x),
  by_contra',
  have st : t.card = s.card,
  { rw [finset.card_image_of_inj_on, finset.card_range],
    rintro m₁ hm₁ m₂ hm₂ (h : (f^[_] _) = (f^[_] _)),
    simp only [finset.mem_coe, finset.mem_range] at hm₁ hm₂,
    by_contra,
    wlog := ne.lt_or_lt h using m₁ m₂,
    refine this _ _ _ (iterate_inj_on_aux hf hf' hx _ h),
    { rwa [nat.succ_sub_succ_eq_sub, tsub_pos_iff_lt] },
    { simp only [nat.succ_sub_succ_eq_sub],
      exact (nat.sub_le _ _).trans hm₂.le },
    rw [add_le_add_iff_right],
    apply case.le },
  have ts : t ⊆ s,
  { simp only [finset.subset_iff, finset.mem_image, finset.mem_range,
      forall_exists_index, forall_apply_eq_imp_iff₂],
    intros n hn,
    exact hf.iterate _ hx },
  have : x ∉ t,
  { simp only [finset.mem_image, finset.mem_range, exists_prop, not_exists, not_and],
    intros n hn,
    exact this (n+1) nat.succ_pos' hn },
  apply this,
  rwa finset.eq_of_subset_of_card_le ts st.ge,
end

def is_interval (I : set ℝ) := ∃ a b, a ≤ b ∧ I = Icc a b
lemma is_interval.bdd_below : is_interval I → bdd_below I :=
by { rintro ⟨a, b, h, rfl⟩, exact bdd_below_Icc }
lemma is_interval.bdd_above : is_interval I → bdd_above I :=
by { rintro ⟨a, b, h, rfl⟩, exact bdd_above_Icc }
lemma is_interval.neg : is_interval I → is_interval (-I) :=
by { rintro ⟨a, b, h, rfl⟩, exact ⟨-b, -a, by simpa⟩ }
lemma is_interval.nonempty : is_interval I → I.nonempty :=
by { rintro ⟨a, b, h, rfl⟩, exact ⟨a, by simpa⟩ }
lemma is_interval.closed : is_interval I → is_closed I :=
by { rintro ⟨a, b, h, rfl⟩, exact is_closed_Icc }
lemma is_interval.ord_connected : is_interval I → ord_connected I :=
by { rintro ⟨a, b, h, rfl⟩, exact ord_connected_Icc }
lemma is_interval.image (hf : continuous_on f I) : is_interval I → is_interval (f '' I) :=
begin
  rintro ⟨a, b, h, rfl⟩,
  refine ⟨_, _, _, hf.image_Icc h⟩,
  exact (hf.Inf_image_Icc_le (left_mem_Icc.2 h)).trans (hf.le_Sup_image_Icc (left_mem_Icc.2 h)),
end

lemma set.surj_on.neg (h : surj_on f I J) : surj_on (-f) I (-J) :=
λ x hx, let ⟨y, hy₁, hy₂⟩ := h hx in ⟨y, hy₁, by simp [hy₂]⟩
lemma set.surj_on.of_neg (h : surj_on (-f) I (-J)) : surj_on f I J := by simpa using h.neg
lemma set.maps_to.neg (h : maps_to f I J) : maps_to (-f) I (-J) := λ x hx, by simpa using h hx
lemma set.maps_to.of_neg (h : maps_to (-f) I (-J)) : maps_to f I J := by simpa using h.neg

lemma set.surj_on.exists_maps_to_aux (hI : is_interval I) (hJ : is_interval J)
  (hf : continuous_on f I) (hfJ : surj_on f I J)
  (h : Inf (I ∩ f ⁻¹' {Inf J}) ≤ Sup (I ∩ f ⁻¹' {Sup J})) :
  ∃ K ⊆ I, is_interval K ∧ surj_on f K J ∧ maps_to f K J :=
begin
  set bots := I ∩ f ⁻¹' {Inf J},
  set tops := I ∩ f ⁻¹' {Sup J},
  have : bdd_below tops := hI.bdd_below.mono (λ x, and.left),
  have : bdd_below bots := hI.bdd_below.mono (λ x, and.left),
  have : bdd_above tops := hI.bdd_above.mono (λ x, and.left),
  have : bdd_above bots := hI.bdd_above.mono (λ x, and.left),
  have : bots.nonempty := hfJ (hJ.closed.cInf_mem hJ.nonempty hJ.bdd_below),
  have : tops.nonempty := hfJ (hJ.closed.cSup_mem hJ.nonempty hJ.bdd_above),
  have : is_closed bots := hf.preimage_closed_of_closed hI.closed is_closed_singleton,
  have : is_closed tops := hf.preimage_closed_of_closed hI.closed is_closed_singleton,
  obtain ⟨a, b, ab, rfl⟩ := hI,
  obtain ⟨y₁, y₂, hy, rfl⟩ := hJ,
  have : a ≤ Inf bots := le_cInf ‹_› (λ x hx, hx.1.1),
  have : Sup tops ≤ b := cSup_le ‹_› (λ x hx, hx.1.2),
  let bots' := {x ∈ bots | x ≤ Sup tops},
  have : bdd_below bots' := ‹bdd_below bots›.mono (λ _, and.left),
  have : bdd_above bots' := ‹bdd_above bots›.mono (λ _, and.left),
  have : Inf bots ∈ bots' := ⟨‹is_closed bots›.cInf_mem ‹_› ‹_›, h⟩,
  have : bots'.nonempty := ⟨Inf bots, ‹_›⟩,
  have : is_closed bots' := ‹is_closed bots›.inter (is_closed_le' _),
  have : Sup bots' ≤ Sup tops := cSup_le ‹bots'.nonempty› (by simp),
  have : Inf bots ≤ Sup bots' := le_cSup ‹bdd_above bots'› ‹_›,
  let tops' := {x ∈ tops | Sup bots' ≤ x},
  have : bdd_below tops' := ‹bdd_below tops›.mono (λ _, and.left),
  have : bdd_above tops' := ‹bdd_above tops›.mono (λ _, and.left),
  have : Sup tops ∈ tops' := ⟨‹is_closed tops›.cSup_mem ‹_› ‹_›, ‹_›⟩,
  have : tops'.nonempty := ⟨Sup tops, ‹_›⟩,
  have : is_closed tops' := ‹is_closed tops›.inter (is_closed_ge' _),
  have i : Sup bots' ≤ Inf tops' := le_cInf ‹_› (by simp),
  have : Inf tops' ≤ Sup tops := cInf_le ‹_› ‹_›,
  have : f (Sup bots') = y₁,
  { simpa [cInf_Icc, hy] using (‹is_closed bots'›.cSup_mem ‹_› ‹_›).1.2 },
  have : f (Inf tops') = y₂,
  { simpa [cSup_Icc, hy] using (‹is_closed tops'›.cInf_mem ‹_› ‹_›).1.2 },
  have : Icc (Sup bots') (Inf tops') ⊆ Icc a b :=  Icc_subset_Icc (by linarith) (by linarith),
  refine ⟨_, this, ⟨_, _, i, rfl⟩, _, _⟩,
  { intros y hy,
    exact intermediate_value_Icc i (hf.mono ‹_›) (by simp only *) },
  rintro x ⟨h₁x, h₂x⟩,
  split,
  { by_contra',
    suffices : ∃ x', x' ∈ Icc x (Inf tops') ∧ f x' = y₁,
    { obtain ⟨x', ⟨hx₁, hx₂⟩, hx⟩ := this,
      refine hx.not_lt (this.trans_eq' $ congr_arg f $ hx₁.antisymm' $ h₁x.trans' $ le_cSup ‹_› _),
      exact ⟨⟨⟨by linarith, by linarith⟩, by simp [cInf_Icc, hy, hx]⟩, hx₂.trans ‹_›⟩ },
    refine intermediate_value_Icc h₂x (hf.mono (Icc_subset_Icc _ _)) ⟨_, _⟩;
    linarith },
  { by_contra',
    suffices : ∃ x', x' ∈ Icc (Sup bots') x ∧ f x' = y₂,
    { obtain ⟨x', ⟨hx₁, hx₂⟩, hx⟩ := this,
      refine hx.not_gt (this.trans_eq $ congr_arg f $ hx₂.antisymm' $ h₂x.trans $ cInf_le ‹_› _),
      exact ⟨⟨⟨by linarith, by linarith⟩, by simp [cSup_Icc, hy, hx]⟩, hx₁⟩ },
    refine intermediate_value_Icc h₁x (hf.mono (Icc_subset_Icc _ _)) ⟨_, _⟩;
    linarith },
end

open_locale pointwise

lemma real.Inf_neg (s : set ℝ) : Inf (-s) = -Sup s :=
by simpa using real.Inf_smul_of_nonpos (show (-1 : ℝ) ≤ 0, by norm_num) s

lemma real.Sup_neg (s : set ℝ) : Sup (-s) = -Inf s :=
by rw [eq_neg_iff_eq_neg, ←real.Inf_neg, neg_neg]

lemma neg_preimage_neg {s : set ℝ} : (-f) ⁻¹' (-s) = f ⁻¹' s :=
by { ext x, simp }
lemma neg_preimage_singleton_neg {a : ℝ} : (-f) ⁻¹' {-a} = f ⁻¹' {a} :=
by { ext x, simp }

lemma set.surj_on.exists_maps_to (hI : is_interval I) (hJ : is_interval J) (hf : continuous_on f I)
  (hfJ : surj_on f I J) :
  ∃ K ⊆ I, is_interval K ∧ surj_on f K J ∧ maps_to f K J :=
begin
  by_cases h : Inf (I ∩ f ⁻¹' {Inf J}) ≤ Sup (I ∩ f ⁻¹' {Sup J}),
  { exact hfJ.exists_maps_to_aux hI hJ hf h },
  have hJ' : is_interval (-J) := hJ.neg,
  have hfJ' : surj_on (-f) I (-J),
  { intros y hy,
    obtain ⟨x, hx₁, hx₂⟩ := hfJ hy,
    exact ⟨x, hx₁, by simp [hx₂]⟩ },
  have : Inf (I ∩ (-f) ⁻¹' {Inf (-J)}) ≤ Sup (I ∩ (-f) ⁻¹' {Sup (-J)}),
  { rw [real.Inf_neg, real.Sup_neg, neg_preimage_singleton_neg, neg_preimage_singleton_neg],
    have := real.Inf_le_Sup (I ∩ f ⁻¹' {Inf J}) (hI.bdd_below.mono (λ x, and.left))
      (hI.bdd_above.mono (λ x, and.left)),
    have := real.Inf_le_Sup (I ∩ f ⁻¹' {Sup J}) (hI.bdd_below.mono (λ x, and.left))
      (hI.bdd_above.mono (λ x, and.left)),
    linarith },
  obtain ⟨K, KI, hK, h₁, h₂⟩ := hfJ'.exists_maps_to_aux hI hJ' hf.neg this,
  exact ⟨K, KI, hK, h₁.of_neg, h₂.of_neg⟩,
end

def is_loop (f : ℝ → ℝ) (j : list (set ℝ)) := list.chain' (surj_on f) (j ++ [j.head])

lemma list.forall₂.append {α β : Type*} (r : α → β → Prop) {l₁ l₂ l₃ l₄}
  (h₁ : list.forall₂ r l₁ l₂) (h₂ : list.forall₂ r l₃ l₄) :
  list.forall₂ r (l₁ ++ l₃) (l₂ ++ l₄) :=
begin
  rw [list.forall₂_iff_zip, list.length_append, list.length_append],
  simp only [list.forall₂_length_eq h₁, list.forall₂_length_eq h₂, list.zip_append,
    eq_self_iff_true, list.mem_append, true_and, or_imp_distrib],
  intros a b,
  exact ⟨list.forall₂_zip h₁, list.forall₂_zip h₂⟩,
end

lemma is_loop_singleton_iff : is_loop f [I] ↔ surj_on f I I :=
by simp [is_loop]

lemma is_loop_pair_iff : is_loop f [I, J] ↔ surj_on f I J ∧ surj_on f J I :=
by simp [is_loop]

lemma is_loop_triple_iff :
  is_loop f [I₁, I₂, I₃] ↔ surj_on f I₁ I₂ ∧ surj_on f I₂ I₃ ∧ surj_on f I₃ I₁ :=
by simp [is_loop]

def follows_loop (f : ℝ → ℝ) (j : list (set ℝ)) (p : ℝ) : Prop :=
  function.is_periodic_pt f j.length p ∧ ∀ i < j.length, f^[i] p ∈ j.nth_le i H

def is_elementary (f : ℝ → ℝ) (j : list (set ℝ)) : Prop :=
  ∀ p, follows_loop f j p → function.minimal_period f p = j.length

lemma singleton_elementary {f : ℝ → ℝ} : is_elementary f [J] :=
begin
  rintro p ⟨hp₁, hp₂⟩,
  simpa only [list.length_singleton, function.is_fixed_point_iff_minimal_period_eq_one] using hp₁
end

lemma list.forall₂.nth_le {α β : Type*} {l₁ l₂} {r : α → β → Prop} (h : list.forall₂ r l₁ l₂) :
  ∀ i < l₁.length, r (l₁.nth_le i H) (l₂.nth_le i (list.forall₂_length_eq h ▸ H)) :=
begin
  intros i hi,
  have : i < (l₁.zip l₂).length,
  { rwa [list.length_zip, ←list.forall₂_length_eq h, min_self] },
  have : (l₁.zip l₂).nth_le i this = (l₁.nth_le i hi, l₂.nth_le i (list.forall₂_length_eq h ▸ hi)),
  { rw list.nth_le_zip },
  apply list.forall₂_zip h,
  rw ←this,
  apply list.nth_le_mem
end

lemma list.forall₂_iff_nth_le {α β : Type*} {l₁ l₂} {r : α → β → Prop} :
  list.forall₂ r l₁ l₂ ↔
    ∃ (h : l₁.length = l₂.length), ∀ i < l₁.length, r (l₁.nth_le i H) (l₂.nth_le i (h ▸ H)) :=
begin
  rw [list.forall₂_iff_zip, ←exists_prop],
  apply exists_congr,
  intro h,
  split,
  { intros h' i hi,
    apply h',
    rw ←list.nth_le_zip,
    apply list.nth_le_mem,
    rwa [list.length_zip, ←h, min_self] },
  intros h' a b,
  simp only [list.mem_iff_nth_le, list.nth_le_zip, prod.mk.inj_iff, bex_imp_distrib, and_imp,
    list.length_zip, ←h, min_self],
  rintro _ _ rfl rfl,
  apply h',
end

lemma follows_loop_iff {f : ℝ → ℝ} {j : list (set ℝ)} {p : ℝ} :
  follows_loop f j p ↔
    function.is_periodic_pt f j.length p ∧
      list.forall₂ (λ i J, f^[i] p ∈ J) (list.range j.length) j :=
begin
  refine and_congr_right' _,
  rw list.forall₂_iff_nth_le,
  simp only [list.length_range, eq_self_iff_true, list.nth_le_range, exists_true_left],
end

lemma itinerary_ind {J₀ : set ℝ} (hJ₀ : is_interval J₀) :
∀ j : list (set ℝ), (∀ J ∈ j, is_interval J) → (∀ J ∈ j, continuous_on f J) →
  (list.chain' (surj_on f) (j ++ [J₀])) → ∃ k, (∀ K ∈ k, is_interval K) ∧ list.forall₂ (⊆) k j ∧
    list.chain' (surj_on f) (k ++ [J₀]) ∧ list.chain' (maps_to f) (k ++ [J₀])
| [] _ _ _ := ⟨[], by simp⟩
| [J₁] h₁ h₂ h₃ :=
  begin
    simp only [list.mem_singleton, forall_eq] at h₁,
    simp only [list.mem_singleton, forall_eq] at h₂,
    simp only [list.singleton_append, list.chain'_cons, list.chain'_singleton, and_true] at h₃,
    obtain ⟨K₁, h₄, h₅, h₆, h₇⟩ := h₃.exists_maps_to h₁ hJ₀ h₂,
    exact ⟨[K₁], by simp [h₄, h₅, h₆, h₇]⟩,
  end
| (J₁ :: J₂ :: j) h₁ h₂ h₃ :=
  begin
    simp only [list.mem_cons_iff _ J₁, forall_eq_or_imp] at h₁ h₂,
    rw [list.cons_append, list.cons_append, list.chain'_cons] at h₃,
    obtain ⟨(rfl | ⟨K₂, k⟩), h₄, h₅, h₆, h₇⟩ := itinerary_ind _ h₁.2 h₂.2 h₃.2,
    { simpa using h₅ },
    rw list.forall₂_cons at h₅,
    simp only [list.mem_cons_iff _ K₂, forall_eq_or_imp] at h₄,
    obtain ⟨K₁, _, _, _, _⟩ := (h₃.1.mono subset.rfl h₅.1).exists_maps_to h₁.1 h₄.1 h₂.1,
    refine ⟨K₁ :: K₂ :: k, _, _, _, _⟩,
    { simp only [list.mem_cons_iff _ _ (K₂ :: _), forall_eq_or_imp],
      exact ⟨‹is_interval K₁›, by simpa⟩ },
    { rw list.forall₂_cons,
      exact ⟨‹K₁ ⊆ J₁›, by simpa⟩ },
    { rw [list.cons_append, list.cons_append, list.chain'_cons, ←list.cons_append],
      exact ⟨‹surj_on f K₁ K₂›, h₆⟩ },
    { rw [list.cons_append, list.cons_append, list.chain'_cons, ←list.cons_append],
      exact ⟨‹maps_to f K₁ K₂›, h₇⟩ }
  end

lemma induction_along_list {J₀ K₀ : set ℝ} (k : list (set ℝ))
  (h₁ : list.chain' (surj_on f) (K₀ :: (k ++ [J₀])))
  (h₂ : list.chain' (maps_to f) (K₀ :: (k ++ [J₀]))) :
  f^[k.length + 1] '' K₀ = J₀ :=
begin
  induction k with K₁ k generalizing K₀,
  { simp only [list.nil_append, list.chain'_cons, list.chain'_singleton, and_true] at h₁ h₂,
    simpa using h₁.image_eq_of_maps_to h₂ },
  rw [list.cons_append, list.chain'_cons] at h₁ h₂,
  rw [function.iterate_succ, set.image_comp, h₁.1.image_eq_of_maps_to h₂.1, list.length_cons,
    k_ih h₁.2 h₂.2],
end

lemma exists_fixed_point {I : set ℝ} (hI : is_interval I) (hf : continuous_on f I)
  (hfI : surj_on f I I) :
  ∃ c ∈ I, function.is_fixed_pt f c :=
begin
  obtain ⟨a₁, a₂, a, rfl⟩ := hI,
  obtain ⟨b₁, hb₁, rfl⟩ := hfI (left_mem_Icc.2 a),
  obtain ⟨b₂, hb₂, rfl⟩ := hfI (right_mem_Icc.2 a),
  have : interval b₁ b₂ ⊆ Icc (f b₁) (f b₂) := interval_subset_Icc hb₁ hb₂,
  have : continuous_on f (interval b₁ b₂) := hf.mono this,
  have hg : continuous_on (λ x, f x - x) (interval b₁ b₂) := this.sub continuous_on_id,
  have : (0 : ℝ) ∈ interval (f b₁ - b₁) (f b₂ - b₂),
  { have : f b₁ - b₁ ≤ f b₂ - b₂,
    { linarith [hb₁.1, hb₂.2] },
    simp only [mem_Icc, interval_of_le this, sub_nonpos, sub_nonneg],
    exact ⟨hb₁.1, hb₂.2⟩ },
  obtain ⟨c, hc₁, hc₂⟩ := intermediate_value_interval hg this,
  refine ⟨c, ‹interval b₁ b₂ ⊆ _› hc₁, _⟩,
  simpa [function.is_fixed_pt, sub_eq_zero] using hc₂,
end

lemma continuous_on.iterate {K₀ : set ℝ} (k : list (set ℝ)) (hK₀ : continuous_on f K₀)
  (hf : ∀ K ∈ k, continuous_on f K) (h : list.chain' (maps_to f) (K₀ :: k)) :
  continuous_on (f^[k.length + 1]) K₀ :=
begin
  induction k generalizing K₀,
  { simpa },
  simp only [list.mem_cons_iff, forall_eq_or_imp] at hf,
  rw list.chain'_cons at h,
  rw [function.iterate_succ, list.length_cons],
  exact continuous_on.comp (k_ih hf.2 hf.1 h.2) hK₀ h.1,
end

lemma list.chain.init {α : Type*} {r : α → α → Prop} :
  ∀ {x : α} {l : list α}, l.chain r x → l.init.chain r x
| x [] h := by simp [list.init]
| x [y] h := by simp [list.init]
| x (a :: b :: c) h :=
  begin
    rw list.init,
    rw list.chain_cons at h ⊢,
    exact ⟨h.1, h.2.init⟩,
  end

lemma list.chain'.init {α : Type*} {r} :
  ∀ {l : list α}, l.chain' r → l.init.chain' r
| [] := by simp
| [x] := by simp
| (x :: y :: xs) := list.chain.init

lemma list.forall₂_and_right {α β : Type*} {r : α → β → Prop} {p : β → Prop} :
  ∀ l u, list.forall₂ (λ a b, p b ∧ r a b) l u ↔ (∀ a ∈ u, p a) ∧ list.forall₂ r l u
| u [] := by simp
| [] (y :: ys) := by simp
| (x :: xs) (y :: ys) := by simp [list.forall₂_and_right xs, and.left_comm, and_assoc]

lemma list.forall₂_const_right {α β : Type*} {p : α → Prop} :
  ∀ l (u : list β), list.forall₂ (λ a b, p a) l u ↔ (∀ a ∈ l, p a) ∧ l.length = u.length
| [] u := by simp [←list.length_eq_zero, eq_comm]
| (x :: xs) [] := by simp
| (x :: xs) (y :: ys) := by simp [list.forall₂_cons, list.forall₂_const_right xs ys, and_assoc]

lemma list.forall₂_const_left {α β : Type*} {p : β → Prop} :
  ∀ (l : list α) u, list.forall₂ (λ a b, p b) l u ↔ (∀ b ∈ u, p b) ∧ l.length = u.length
| u [] := by simp [list.length_eq_zero]
| [] (y :: ys) := by simp [ys.length.succ_ne_zero.symm]
| (x :: xs) (y :: ys) := by simp [list.forall₂_cons, list.forall₂_const_left xs, and_assoc]

lemma itinerary (j : list (set ℝ)) (hj : ∀ J ∈ j, is_interval J) (hfj : ∀ J ∈ j, continuous_on f J)
  (hf : is_loop f j) : ∃ p, follows_loop f j p :=
begin
  cases j with J₀ j,
  { exact ⟨0, by simp [follows_loop, function.is_periodic_pt, function.is_fixed_pt]⟩ },
  obtain ⟨(rfl | ⟨K₀, k⟩), hki, hkj, hks, hkm⟩ := itinerary_ind (hj _ (by simp)) _ hj hfj hf,
  { simpa using hkj },
  simp only [list.head_cons, list.cons_append] at hkm hks,
  simp only [list.mem_cons_iff, forall_eq_or_imp] at hki,
  simp only [list.forall₂_cons] at hkj,
  have := induction_along_list _ hks hkm,
  have h : surj_on (f^[k.length + 1]) K₀ K₀,
  { rw [surj_on, this],
    exact hkj.1 },
  simp only [list.mem_cons_iff, forall_eq_or_imp] at hfj,
  have : continuous_on (f^[k.length + 1]) K₀,
  { refine continuous_on.iterate _ (hfj.1.mono hkj.1) _ _,
    { have : list.forall₂ (λ a b, continuous_on f a) k j :=
        ((list.forall₂_and_right _ _).2 ⟨hfj.2, hkj.2⟩).imp (λ a b h, h.1.mono h.2),
      exact ((list.forall₂_const_right _ _).1 this).1 },
    simpa [list.init] using hkm.init },
  obtain ⟨p, hp₁, hp₂⟩ := exists_fixed_point hki.1 this h,
  simp only [follows_loop_iff],
  have t : k.length = j.length := list.forall₂_length_eq hkj.2,
  refine ⟨p, _, _⟩,
  { rwa [list.length_cons, ←t] },
  rw ←list.forall₂_cons at hkj,
  rw list.length_cons,
  rw ←list.cons_append at hkm,
  change list.chain _ _ (k ++ [J₀]) at hkm,
  rw list.chain_append_singleton_iff_forall₂ at hkm,
  simp only [list.forall₂_iff_nth_le, list.length_range, list.length_cons, t, list.length_append,
    list.length, add_right_inj, self_eq_add_left, eq_self_iff_true, exists_true_left,
    list.nth_le_range, nat.lt_add_one_iff] at hkj hkm ⊢,
  intros i hi,
  apply hkj i hi,
  induction i,
  { simpa },
  rw function.iterate_succ',
  let hi' := (nat.le_succ _).trans hi,
  convert hkm _ hi' (i_ih hi') using 1,
  rw [list.nth_le_append, list.nth_le],
end

-- Proposition 2.5
lemma itinerary' (j : list (set ℝ)) (hj : ∀ J ∈ j, is_interval J) (hfj : ∀ J ∈ j, continuous_on f J)
  (hf : is_loop f j) (hf' : is_elementary f j) :
  ∃ p, follows_loop f j p ∧ function.minimal_period f p = j.length :=
let ⟨p, hp⟩ := itinerary j hj hfj hf in ⟨p, hp, hf' _ hp⟩

def finset.is_cycle (O : finset ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ O, f x ∈ O ∧ function.minimal_period f x = O.card
end prereq

section proof
open_locale classical
open set finset function

parameters (f : ℝ → ℝ)
parameters (O : finset ℝ) (hO : 2 ≤ O.card) (hO' : O.is_cycle f)

noncomputable def p : ℝ :=
(O.filter (λ p, p < f p)).max.get_or_else 0

include hO hO'

def O_int : set ℝ :=
Icc (O.min' (by { rw ←finset.card_pos, linarith })) (O.max' (by { rw ←finset.card_pos, linarith }))

lemma O_int_is_interval : is_interval O_int := ⟨_, _, finset.min'_le_max' _, rfl⟩

lemma mem_O_int_of {x : ℝ} (hx : x ∈ O) : x ∈ O_int :=
by { rw [O_int, set.mem_Icc], exact ⟨finset.min'_le _ _ hx, finset.le_max' _ _ hx⟩ }

lemma interval_subset_O_int_of {x y : ℝ} (hx : x ∈ O) (hy : y ∈ O) : interval x y ⊆ O_int :=
ord_connected_Icc.interval_subset (mem_O_int_of hx) (mem_O_int_of hy)
lemma Icc_subset_O_int_of {x y : ℝ} (hx : x ∈ O) (hy : y ∈ O) : Icc x y ⊆ O_int :=
ord_connected_Icc.out (mem_O_int_of hx) (mem_O_int_of hy)

lemma f_bij_on : set.bij_on f O O :=
begin
  have hm : set.maps_to f O O := λ x hx, (hO' x hx).1,
  have hs : set.surj_on f O O,
  { intros x hx,
    refine ⟨f^[O.card - 1] x, hm.iterate _ hx, _⟩,
    rw [←iterate_succ_apply' f, nat.succ_eq_add_one, nat.sub_add_cancel, ←(hO' x hx).2,
      iterate_minimal_period],
    exact one_le_two.trans hO },
  exact ⟨hm, (finset.inj_on_iff_surj_on rfl hm).2 hs, hs⟩,
end

lemma no_fixed_points {r : ℝ} (hr : r ∈ O) : f r ≠ r :=
λ h, by linarith [(hO' _ hr).2, is_fixed_point_iff_minimal_period_eq_one.2 h]

lemma not_maps_to_ssubset {P : finset ℝ} (hP : P ⊂ O) (hP' : P.nonempty) :
  ¬ set.maps_to f P P :=
begin
  intro h,
  obtain ⟨x, hx⟩ := hP',
  obtain ⟨n, hn₁, hn₂, hn₃⟩ := has_period_of_maps_to h (f_bij_on.2.1.mono hP.1) hx,
  have := (hO' x (hP.1 hx)).2,
  have := is_periodic_pt.minimal_period_le hn₁ hn₃,
  have := finset.card_lt_card hP,
  linarith,
end

lemma p_filter_nonempty : (O.filter (λ p, p < f p)).nonempty :=
begin
  rw filter_nonempty_iff,
  by_contra' h,
  have hO'' : O.nonempty, { rw ←finset.card_pos, linarith },
  have := (h _ (O.min'_mem hO'')).antisymm (O.min'_le _ (hO' _ (O.min'_mem _)).1),
  exact no_fixed_points (O.min'_mem hO'') this,
end

lemma p_spec : p ∈ O ∧ p < f p ∧ ∀ r ∈ O, r < f r → r ≤ p :=
begin
  obtain ⟨a, ha : _ = _⟩ := max_of_nonempty p_filter_nonempty,
  rw [p, ha, option.get_or_else_some],
  simp only [←and_imp, ←and_assoc],
  simp only [←@mem_filter _ _ _ O],
  exact ⟨finset.mem_of_max ha, λ r hr, le_max_of_mem hr ha⟩,
end

lemma p_mem_O : p ∈ O := p_spec.1
lemma p_lt_f_p : p < f p := p_spec.2.1
lemma p_max {r : ℝ} (hr : r ∈ O) (hr' : r < f r) : r ≤ p := p_spec.2.2 _ hr hr'
lemma f_le_of_p_lt {r : ℝ} (hr : r ∈ O) (hr' : p < r) : f r ≤ r :=
le_of_not_lt (λ h, hr'.not_le (p_max hr h))
lemma f_lt_of_p_lt {r : ℝ} (hr : r ∈ O) (hr' : p < r) : f r < r :=
lt_of_le_of_ne (f_le_of_p_lt hr hr') (no_fixed_points hr)

noncomputable def q : ℝ := (O.filter (λ q, p < q)).min.get_or_else 0

lemma q_filter_nonempty : (O.filter (λ q, p < q)).nonempty :=
begin
  rw finset.filter_nonempty_iff,
  by_contra' h,
  have hO'' : O.nonempty, { rw ←finset.card_pos, linarith },
  exact (h _ (hO' _ p_mem_O).1).not_lt p_lt_f_p,
end

lemma q_spec : q ∈ O ∧ p < q ∧ ∀ r ∈ O, p < r → q ≤ r :=
begin
  obtain ⟨a, ha : _ = _⟩ := min_of_nonempty q_filter_nonempty,
  rw [q, ha, option.get_or_else_some],
  simp only [←and_imp, ←and_assoc],
  simp only [←@mem_filter _ _ _ O],
  exact ⟨finset.mem_of_min ha, λ r hr, min_le_of_mem hr ha⟩,
end

lemma q_mem_O : q ∈ O := q_spec.1
lemma p_lt_q : p < q := q_spec.2.1
lemma q_min {r : ℝ} (hr : r ∈ O) (hr' : p < r) : q ≤ r := q_spec.2.2 _ hr hr'
lemma not_mem_O_of_mem_Ioo {r : ℝ} (hr : r ∈ Ioo p q) : r ∉ O := λ h, (q_min h hr.1).not_lt hr.2

lemma q_lt_f_q : f q < q := f_lt_of_p_lt q_mem_O p_lt_q

lemma q_le_f_p : q ≤ f p := q_min (hO' _ p_mem_O).1 p_lt_f_p
lemma f_q_le_p : f q ≤ p := le_of_not_lt (λ t, (q_min (hO' _ q_mem_O).1 t).not_lt q_lt_f_q)

-- fq ≤ p < q ≤ fp

def I : set ℝ := Icc p q
lemma p_mem_I : p ∈ I := set.left_mem_Icc.2 p_lt_q.le
lemma q_mem_I : q ∈ I := set.right_mem_Icc.2 p_lt_q.le

lemma interval_eq_I : interval p q = I := interval_of_le p_lt_q.le

lemma I_surj_on (hf : continuous_on f I) : surj_on f I I :=
begin
  simp only [←interval_eq_I] at *,
  apply set.subset.trans _ (intermediate_value_interval hf),
  rw [interval_of_le p_lt_q.le, interval_of_ge ((f_q_le_p.trans p_lt_q.le).trans q_le_f_p)],
  apply set.Icc_subset_Icc f_q_le_p q_le_f_p,
end

noncomputable def c := p / 2 + q / 2
lemma c_mem_I : c ∈ Ioo p q := by { rw [set.mem_Ioo, c], split; linarith [p_lt_q] }
lemma c_not_mem_O : c ∉ O := not_mem_O_of_mem_Ioo c_mem_I

def same_side (x y : ℝ) : Prop := 0 < (x - c) * (y - c)
lemma same_side.symm {x y : ℝ} (h : same_side x y) : same_side y x :=
by simpa [same_side, mul_comm] using h
lemma same_side_iff {x y : ℝ} : same_side x y ↔ (c < x ∧ c < y) ∨ (x < c ∧ y < c) :=
by { simp only [same_side, mul_pos_iff, sub_neg, sub_pos] }
lemma not_same_side_c {x : ℝ} : ¬ same_side x c :=
by simp [same_side_iff, le_total x c]
lemma not_same_side_c' {x : ℝ} : ¬ same_side c x :=
by simp [same_side_iff, le_total c x]

def opposite_side (x y : ℝ) : Prop := (x - c) * (y - c) < 0
lemma opposite_side.symm {x y : ℝ} (h : opposite_side x y) : opposite_side y x :=
by simpa [opposite_side, mul_comm] using h
lemma opposite_side_iff {x y : ℝ} : opposite_side x y ↔ c < x ∧ y < c ∨ x < c ∧ c < y :=
by { simp only [opposite_side, mul_neg_iff, sub_neg, sub_pos] }
lemma not_opposite_side_c {x : ℝ} : ¬ opposite_side x c :=
by simp [opposite_side_iff, le_total x c]
lemma not_opposite_side_c' {x : ℝ} : ¬ opposite_side c x :=
by simp [opposite_side_iff, le_total c x]

lemma not_opposite_side_self {x : ℝ} : ¬ opposite_side x x :=
begin
  rw [opposite_side, not_lt],
  apply mul_self_nonneg,
end

lemma opposite_side.ne {x y : ℝ} : opposite_side x y → x ≠ y :=
by { rintro h rfl, exact not_opposite_side_self h }

lemma opposite_side.not_same_side {x y : ℝ} : opposite_side x y → ¬same_side x y := lt_asymm
lemma same_side.not_opposite_side {x y : ℝ} : same_side x y → ¬opposite_side x y := lt_asymm

lemma same_side_of_not_opposite_side {x y : ℝ} (hx : x ≠ c) (hy : y ≠ c) :
  ¬ opposite_side x y → same_side x y :=
begin
  rw [opposite_side, not_lt, same_side],
  refine λ h, lt_of_le_of_ne h _,
  simp only [ne.def, zero_eq_mul, not_or_distrib, sub_eq_zero, hx, hy, not_false_iff, and_self],
end

def switches_sides (x : ℝ) : Prop := opposite_side x (f x)
lemma switches_sides_iff {x : ℝ} : switches_sides x ↔ c < x ∧ f x < c ∨ x < c ∧ c < f x :=
opposite_side_iff
lemma switches_sides_of_lt_c {x : ℝ} (hx : x < c) (hx' : c < f x) : switches_sides x :=
switches_sides_iff.2 $ or.inr ⟨hx, hx'⟩
lemma switches_sides_of_gt_c {x : ℝ} (hx : f x < c) (hx' : c < x) : switches_sides x :=
switches_sides_iff.2 $ or.inl ⟨hx', hx⟩
lemma p_switches_sides : switches_sides p :=
switches_sides_of_lt_c c_mem_I.1 $ c_mem_I.2.trans_le q_le_f_p
lemma q_switches_sides : switches_sides q :=
switches_sides_of_gt_c (f_q_le_p.trans_lt c_mem_I.1) c_mem_I.2

lemma same_side.trans {x y z : ℝ} (hxy : same_side x y) (hyz : same_side y z) : same_side x z :=
begin
  rw [same_side] at *,
  exact pos_of_mul_pos_left (by nlinarith) (sq_nonneg (y - c)),
end

lemma opposite_side.trans {x y z : ℝ} (hxy : opposite_side x y) (hyz : opposite_side y z) :
  same_side x z :=
begin
  rw [opposite_side] at *,
  exact pos_of_mul_pos_left (by nlinarith) (sq_nonneg (y - c)),
end

lemma opposite_side.untrans {x y z : ℝ} (hxy : opposite_side x y) (hyz : same_side y z) :
  opposite_side x z :=
begin
  simp only [opposite_side, same_side] at *,
  exact neg_of_mul_neg_left (by nlinarith) (sq_nonneg (y - c)),
end

lemma opposite_side.untrans' {x y z : ℝ} (hxy : same_side x y) (hyz : opposite_side y z) :
  opposite_side x z :=
(opposite_side.untrans (hyz.symm _ _ _ _) (hxy.symm _ _ _ _)).symm _ _ _ _

lemma subset_I_of {J : set ℝ} (hJ : is_interval J) {x y : ℝ} (hxy : opposite_side x y)
  (hx : x ∈ O) (hy : y ∈ O) (hxJ : x ∈ J) (hyJ : y ∈ J) : I ⊆ J :=
begin
  rw opposite_side_iff at hxy,
  wlog : y ≤ x,
  rcases hxy with (⟨cx, yc⟩ | ⟨xc, cy⟩),
  { have : q ≤ x := q_min hx (c_mem_I.1.trans cx),
    have : y ≤ p := le_of_not_lt (λ t, not_mem_O_of_mem_Ioo ⟨t, yc.trans c_mem_I.2⟩ hy),
    exact (Icc_subset_Icc ‹y ≤ p› ‹q ≤ x›).trans (hJ.ord_connected.out hyJ hxJ) },
  { cases case.not_lt (xc.trans cy) },
end

noncomputable def half_I_length : ℝ := (q - p) / 2
lemma half_I_length_pos : 0 < half_I_length :=
by { rw half_I_length, linarith [p_lt_q] }

lemma dist_p_c : |p - c| = half_I_length :=
by { rw [abs_of_nonpos (sub_nonpos_of_le c_mem_I.1.le), c, half_I_length], ring }

lemma dist_q_c : |q - c| = half_I_length :=
by { rw [abs_of_nonneg (sub_nonneg_of_le c_mem_I.2.le), c, half_I_length], ring }

lemma not_mem_O_of_close {r : ℝ} (hr : |r - c| < half_I_length) : r ∉ O :=
begin
  apply not_mem_O_of_mem_Ioo,
  rw [abs_lt, half_I_length, c] at hr,
  refine and.imp _ _ hr;
  { intro i, linarith [p_lt_q] }
end

lemma eq_of_dist_eq {r : ℝ} (hr : |r - c| = half_I_length) : r = p ∨ r = q :=
begin
  rw [abs_eq half_I_length_pos.le, c, half_I_length] at hr,
  refine hr.symm.imp _ _;
  { intro i, linarith }
end

noncomputable def O_ (x : ℝ) := O.filter (λ y, y ∈ interval x c)

lemma O_nonempty_of {x : ℝ} (hx : x ∈ O) : (O_ x).nonempty := ⟨x, by simp [O_, hx]⟩
lemma same_side_of_mem_O {x y : ℝ} (hx : x ∈ O) : y ∈ O_ x → same_side x y :=
begin
  intro hy,
  rw [O_, mem_filter] at hy,
  have : x ≠ c := ne_of_mem_of_not_mem hx c_not_mem_O,
  have : y ≠ c := ne_of_mem_of_not_mem hy.1 c_not_mem_O,
  cases lt_or_gt_of_ne ‹x ≠ c›,
  { rw [same_side],
    rw [interval_of_lt h] at hy,
    apply mul_pos_of_neg_of_neg (sub_neg_of_lt h) (sub_neg_of_lt _),
    apply lt_of_le_of_ne hy.2.2 ‹y ≠ c› },
  { rw [same_side],
    rw [interval_of_gt h] at hy,
    refine mul_pos (sub_pos_of_lt h) (sub_pos_of_lt _),
    apply lt_of_le_of_ne hy.2.1 ‹y ≠ c›.symm },
end

lemma eq_of_swap_interval {x y z : ℝ} : x ∈ interval y z → y ∈ interval x z → x = y :=
begin
  simp only [interval, set.mem_Icc, min_le_iff, le_max_iff],
  tauto {closer := `[linarith]},
end

lemma mem_interval_of_same_side_dist {x y : ℝ} (h₁ : same_side x y) (h₂ : |y - c| ≤ |x - c|) :
  y ∈ interval x c :=
begin
  rw same_side_iff at h₁,
  cases h₁,
  { rw [abs_of_nonneg (sub_nonneg_of_le h₁.1.le), abs_of_nonneg (sub_nonneg_of_le h₁.2.le),
      sub_le_sub_iff_right] at h₂,
    rw [interval_of_gt h₁.1, set.mem_Icc],
    exact ⟨h₁.2.le, h₂⟩ },
  { rw [abs_sub_comm, abs_sub_comm x, abs_of_nonneg (sub_nonneg_of_le h₁.1.le),
      abs_of_nonneg (sub_nonneg_of_le h₁.2.le), sub_le_sub_iff_left] at h₂,
    rw [interval_of_lt h₁.1, set.mem_Icc],
    exact ⟨h₂, h₁.2.le⟩ },
end

lemma O_p_eq : O_ p = {p} :=
begin
  simp only [finset.eq_singleton_iff_nonempty_unique_mem, O_nonempty_of p_mem_O, true_and],
  simp only [O_, mem_filter, interval_of_le c_mem_I.1.le, set.mem_Icc, and_imp],
  intros x hx₁ hx₂ hx₃,
  apply eq_of_ge_of_not_gt hx₂,
  intro hx₄,
  exact not_mem_O_of_mem_Ioo ⟨hx₄, hx₃.trans_lt c_mem_I.2⟩ hx₁,
end

lemma O_q_eq : O_ q = {q} :=
begin
  simp only [finset.eq_singleton_iff_nonempty_unique_mem, O_nonempty_of q_mem_O, true_and],
  simp only [O_, mem_filter, interval_of_ge c_mem_I.2.le, set.mem_Icc, and_imp],
  intros x hx₁ hx₂ hx₃,
  apply eq_of_le_of_not_lt hx₃,
  intro hx₄,
  exact not_mem_O_of_mem_Ioo ⟨c_mem_I.1.trans_le hx₂, hx₄⟩ hx₁,
end

parameters (h : ∃ x ∈ O, ¬ switches_sides x)
include h

noncomputable theory

def x₀ : ℝ := if f p = q then p else q
def x₁ : ℝ := if f p = q then q else p
lemma x₀_mem_O : x₀ ∈ O := by { rw [x₀], split_ifs, exacts [p_mem_O, q_mem_O] }
lemma x₁_mem_O : x₁ ∈ O := by { rw [x₁], split_ifs, exacts [q_mem_O, p_mem_O] }
lemma x₀_switches_sides : switches_sides x₀ :=
by { rw [x₀], split_ifs, exacts [p_switches_sides, q_switches_sides] }
lemma x₁_switches_sides : switches_sides x₁ :=
by { rw [x₁], split_ifs, exacts [q_switches_sides, p_switches_sides] }

lemma interval_x_eq_I : interval x₀ x₁ = I :=
by { rw [x₀, x₁, I], split_ifs, exacts [interval_of_lt p_lt_q, interval_of_gt p_lt_q] }

lemma dist_x₀_c : |x₀ - c| = half_I_length :=
by { rw [x₀], split_ifs, exacts [dist_p_c, dist_q_c] }
lemma dist_x₁_c : |x₁ - c| = half_I_length :=
by { rw [x₁], split_ifs, exacts [dist_q_c, dist_p_c] }

lemma eq_x__of_dist_eq {r : ℝ} (hr : |r - c| = half_I_length) : r = x₀ ∨ r = x₁ :=
by { rw [x₀, x₁], split_ifs, exacts [eq_of_dist_eq hr, (eq_of_dist_eq hr).symm] }

lemma opposite_sides : opposite_side x₀ x₁ :=
begin
  have : opposite_side p q,
  { rw opposite_side_iff,
    exact or.inr c_mem_I },
  rw [x₀, x₁],
  split_ifs,
  exacts [this, opposite_side.symm this],
end

lemma O_x₀_eq : O_ x₀ = {x₀} := by { rw [x₀], split_ifs, apply O_p_eq, apply O_q_eq }
lemma O_x₁_eq : O_ x₁ = {x₁} := by { rw [x₁], split_ifs, apply O_q_eq, apply O_p_eq }

lemma not_two_cycle : f p = q → f q ≠ p :=
begin
  intros h' i,
  have : is_periodic_pt f 2 p,
  { rw [is_periodic_pt, is_fixed_pt, iterate_succ, iterate_one, comp_apply, h', i] },
  have := this.minimal_period_le zero_lt_two,
  rw (hO' _ p_mem_O).2 at this,
  have : {p, q} = O,
  { apply finset.eq_of_subset_of_card_le,
    { simpa [subset_iff, q_mem_O] using p_mem_O, },
    rwa [finset.card_insert_of_not_mem, finset.card_singleton],
    simpa using p_lt_q.ne },
  have : ∃ x ∈ ({p, q} : finset ℝ), ¬switches_sides x,
  { rwa this },
  simp only [finset.mem_insert, finset.mem_singleton, exists_prop] at this,
  obtain ⟨_, (rfl | rfl), z⟩ := this,
  { apply z p_switches_sides },
  { apply z q_switches_sides },
end

lemma f_x__diff : f x₁ ≠ x₀ :=
begin
  rw [x₀, x₁],
  split_ifs with h',
  { apply not_two_cycle h' },
  { exact h' }
end

lemma x__diff : x₀ ≠ x₁ := by { rw [x₀, x₁], split_ifs, exacts [p_lt_q.ne, p_lt_q.ne'] }

lemma f_x__diff' : f x₁ ≠ x₁ := by { rw [x₁], split_ifs, exacts [q_lt_f_q.ne, p_lt_f_p.ne'] }

noncomputable def x__ : ℕ → option ℝ
| 0 := some x₀
| 1 := some x₁
| (n + 2) := option.cases_on' (x__ (n + 1)) none $ λ p,
        if ∃ i ∈ O_ p, ¬ switches_sides i
          then none
          else if h' : (O_ p).nonempty
                 then some (finset.exists_max_image _ (λ y, |y - c|) (h'.image f)).some
                 else none

@[simp] lemma x__0_eq : x__ 0 = some x₀ := rfl
@[simp] lemma x__1_eq : x__ 1 = some x₁ := rfl

lemma x__is_seq : ∀ {n : ℕ}, x__ n = none → x__ (n + 1) = none
| (n + 1) h := by { rw [x__, h], refl }

lemma eq_some_of {n : ℕ} {x : ℝ} (hx : x__ (n + 1) = some x) : ∃ y, x__ n = some y :=
begin
  rw ←option.ne_none_iff_exists',
  intro h',
  rw x__is_seq h' at hx,
  simpa using hx
end

lemma eq_some_of_le {n m : ℕ} {x : ℝ} (hx : x__ (n + m) = some x) : ∃ y, x__ n = some y :=
begin
  induction m with m ih generalizing x,
  { exact ⟨_, hx⟩ },
  obtain ⟨y, hy⟩ := eq_some_of hx,
  exact ih hy,
end

lemma each_mem_O : ∀ {n} {y : ℝ}, x__ n = some y → y ∈ O
| 0 y hy       := by { rw [x__0_eq, option.some_inj] at hy, rw ←hy, apply x₀_mem_O }
| 1 y hy       := by { rw [x__1_eq, option.some_inj] at hy, rw ←hy, apply x₁_mem_O }
| (n + 2) y hy :=
  begin
    obtain ⟨z, hz⟩ := eq_some_of hy,
    rw [x__, hz, option.cases_on'_some] at hy,
    split_ifs at hy,
    { cases hy },
    swap,
    { cases hy },
    rw ←hy,
    simp only [finset.mem_image, exists_prop, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂],
    generalize_proofs h'',
    obtain ⟨⟨a, ha₁, ha₂⟩, -⟩ := h''.some_spec,
    rw ←ha₂,
    exact (hO' _ (filter_subset _ _ ha₁)).1,
  end

lemma x__eq {n : ℕ} {y : ℝ} (hn : x__ (n + 1) = some y) (hy : ∀ i ∈ O_ y, switches_sides i) :
  x__ (n + 2) =
    some (finset.exists_max_image _ (λ y, |y - c|) ((O_nonempty_of (each_mem_O hn)).image f)).some :=
begin
  rw [x__, hn, option.cases_on'_some, if_neg, dif_pos],
  { exact (O_nonempty_of (each_mem_O hn)) },
  push_neg,
  assumption
end

lemma x__succ_defined {n : ℕ} {y z : ℝ} (hn : x__ (n + 1) = some y) (hn' : x__ (n + 2) = some z) :
  ∀ i ∈ O_ y, switches_sides i :=
begin
  by_contra',
  rw [x__, hn, option.cases_on'_some, if_pos] at hn',
  { simpa using hn' },
  { simpa using this },
end

@[simp] lemma x__2_eq : x__ 2 = some (f x₁) :=
begin
  have : ∀ (i : ℝ), i ∈ O_ x₁ → switches_sides i,
  { simp only [O_x₁_eq, finset.mem_singleton, forall_eq],
    exact x₁_switches_sides },
  simp only [x__eq x__1_eq this, O_x₁_eq, finset.mem_image, finset.mem_singleton, exists_prop,
    exists_eq_left, forall_eq'],
  generalize_proofs hy,
  exact hy.some_spec.1.symm,
end

lemma x__succ {n : ℕ} {y z : ℝ} (hn : x__ (n + 1) = some y) (hn' : x__ (n + 2) = some z) :
  (∃ (a : ℝ), a ∈ O_ y ∧ f a = z) ∧ ∀ a ∈ O_ y, |f a - c| ≤ |z - c| :=
begin
  have := x__succ_defined hn hn',
  rw [x__eq hn this, option.some_inj] at hn',
  simp only [finset.mem_image, exists_prop, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hn',
  generalize_proofs hn'' at hn',
  dsimp at hn'',
  rw ←hn',
  exact hn''.some_spec,
end

lemma swaps_sides {n : ℕ} {x y : ℝ} (hx : x__ n = some x) (hy : x__ (n + 1) = some y) :
  opposite_side x y :=
begin
  cases n,
  { simp only [x__1_eq, x__0_eq] at hx hy,
    rw [←hx, ←hy],
    apply opposite_sides },
  have := x__succ_defined hx hy,
  obtain ⟨⟨z, hz, rfl⟩, _⟩ := x__succ hx hy,
  exact opposite_side.untrans' (same_side_of_mem_O (each_mem_O hx) hz) (this _ hz),
end

lemma same_side_twice {n : ℕ} {x z : ℝ} (hx : x__ n = some x) (hz : x__ (n + 2) = some z) :
  same_side x z :=
let ⟨y, hy⟩ := eq_some_of hz in opposite_side.trans (swaps_sides hx hy) (swaps_sides hy hz)

lemma inclusion {n : ℕ} {y z : ℝ} (hy : x__ (n + 1) = some y) (hz : x__ (n + 2) = some z) :
  (O_ y).image f ⊆ O_ z :=
begin
  intros a ha,
  simp only [finset.mem_image, exists_prop] at ha,
  obtain ⟨a, ha, rfl⟩ := ha,
  simp only [O_, mem_filter],
  refine ⟨(hO' _ (finset.mem_filter.1 ha).1).1, _⟩,
  apply mem_interval_of_same_side_dist _ ((x__succ hy hz).2 a ha),
  apply opposite_side.trans _ (x__succ_defined hy hz _ ha),
  apply opposite_side.untrans _ (same_side_of_mem_O (each_mem_O hy) ha),
  exact opposite_side.symm (swaps_sides hy hz)
end

lemma four_four {n : ℕ} {x z : ℝ} (hx : x__ n = some x) (hz : x__ (n + 2) = some z) :
  |x - c| < |z - c| :=
begin
  obtain ⟨y, hy⟩ := eq_some_of hz,
  cases n with i,
  { simp only [x__2_eq, x__1_eq, x__0_eq] at hx hy hz,
    rw [←hx, ←hz, dist_x₀_c],
    apply ne.lt_of_le,
    { intro k,
      cases eq_x__of_dist_eq k.symm with h' h',
      exacts [f_x__diff h', f_x__diff' h'] },
    exact le_of_not_lt (λ h', not_mem_O_of_close h' (hO' _ x₁_mem_O).1) },
  have xz : (O_ x).card ≤ (O_ z).card,
  { suffices : (((O_ x).image f).image f).card ≤ (O_ z).card,
    { apply le_trans' this,
      rw [finset.card_image_of_inj_on, finset.card_image_of_inj_on],
      { exact f_bij_on.2.1.mono (filter_subset _ _) },
      refine f_bij_on.2.1.mono (set.subset.trans _ f_bij_on.1.image_subset),
      simp only [coe_image],
      exact image_subset _ (filter_subset _ _) },
    apply finset.card_le_of_subset,
    exact (finset.image_subset_image (inclusion hx hy)).trans (inclusion hy hz) },
  apply lt_of_not_le,
  intro h',
  have zxc := mem_interval_of_same_side_dist (same_side_twice hx hz) h',
  have zx : O_ z ⊆ O_ x,
  { refine monotone_filter_right _ _,
    exact ord_connected_interval.interval_subset zxc right_mem_interval },
  have := finset.eq_of_subset_of_card_le zx xz,
  have xzc : x ∈ interval z c,
  { have : x ∈ O_ z,
    { rw this,
      simp [O_, each_mem_O hx] },
    simp only [O_, mem_filter] at this,
    apply this.2 },
  have xz' : x = z := eq_of_swap_interval xzc zxc,
  let P := O_ x ∪ O_ y,
  have : maps_to f P P,
  { rw [maps_to', ←finset.coe_image, finset.coe_subset, finset.image_union, finset.union_comm],
    apply finset.union_subset_union,
    { rw xz', apply inclusion hy hz },
    { exact inclusion hx hy } },
  have : P ≠ O,
  { intro PO,
    suffices : ∀ j ∈ P, switches_sides j,
    { obtain ⟨j, hj, hj'⟩ := h,
      apply hj' (this _ _),
      rwa PO },
    simp only [finset.mem_union, or_imp_distrib, forall_and_distrib],
    exact ⟨x__succ_defined hx hy, x__succ_defined hy hz⟩ },
  have : P ⊂ O,
  { apply ssubset_of_subset_of_ne _ this,
    exact finset.union_subset (filter_subset _ _) (filter_subset _ _) },
  have : P.nonempty,
  { exact ⟨x, by simp [O_, each_mem_O hx]⟩ },
  exact not_maps_to_ssubset ‹P ⊂ O› ‹P.nonempty› ‹_›,
end

lemma distinctness_odd_aux {n k : ℕ} {x y : ℝ}
  (hx : x__ n = some x) (hy : x__ (n + (2 * k + 1)) = some y) :
  opposite_side x y :=
begin
  induction k with k ih generalizing y,
  { exact swaps_sides hx hy },
  obtain ⟨w, hw : x__ (n + (2 * k + 2)) = some w⟩ := eq_some_of hy,
  obtain ⟨z, hz : x__ (n + (2 * k + 1)) = some z⟩ := eq_some_of hw,
  exact opposite_side.untrans (ih hz) (same_side_twice hz hy),
end

lemma distinctness_even_aux' {n k : ℕ} {x y : ℝ}
  (hx : x__ n = some x) (hy : x__ (n + 2 * (k + 1)) = some y) : |x - c| < |y - c| :=
begin
  induction k with k ih generalizing y,
  { exact four_four hx hy },
  obtain ⟨w, hw : x__ (n + (2 * k + 3)) = some w⟩ := eq_some_of hy,
  obtain ⟨z, hz : x__ (n + (2 * k + 2)) = some z⟩ := eq_some_of hw,
  exact (ih hz).trans (four_four hz hy),
end

lemma distinctness_even_aux {n k : ℕ} {x y : ℝ} (hk : k ≠ 0)
  (hn : x__ n = some x) (hm : x__ (n + 2 * k) = some y) : |x - c| < |y - c| :=
begin
  cases k,
  { cases hk rfl },
  exact distinctness_even_aux' hn hm,
end

lemma distinctness_aux {n k : ℕ} {x y : ℝ} (hk : k ≠ 0)
  (hx : x__ n = some x) (hy : x__ (n + k) = some y) : x ≠ y :=
begin
  obtain ⟨k, rfl | rfl⟩ := nat.even_or_odd' k,
  { simp only [ne.def, nat.mul_eq_zero, bit0_eq_zero, nat.one_ne_zero, false_or] at hk,
    rintro rfl,
    exact (distinctness_even_aux hk hx hy).ne' rfl },
  exact opposite_side.ne (distinctness_odd_aux hx hy),
end

lemma distinctness {n m : ℕ} {x y : ℝ} (hnm : n ≠ m) (hx : x__ n = some x) (hy : x__ m = some y) :
  x ≠ y :=
begin
  wlog := hnm.lt_or_lt using n m,
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_lt case,
  exact distinctness_aux k.succ_ne_zero hx (by simpa using hy),
end.

lemma terminates : ∃ k, k < O.card ∧ (∃ xk, x__ k = some xk) ∧ x__ (k + 1) = none :=
begin
  by_contra',
  simp only [←ne.def, option.ne_none_iff_exists', forall_exists_index] at this,
  have : ∀ (k : ℕ), k < O.card + 1 → ∃ x : ℝ, x__ k = some x,
  { intros k hk,
    induction k with k ih,
    { exact ⟨_, x__0_eq⟩ },
    obtain ⟨y, hy⟩ := ih ((nat.le_succ _).trans hk),
    exact this k (nat.succ_lt_succ_iff.1 hk) y hy },
  choose g hg using this,
  let l := (finset.range (O.card + 1)).attach.image
    (λ (i : {x // x ∈ range (O.card + 1)}), g i.1 (finset.mem_range.1 i.2)),
  have : l.card = O.card + 1,
  { rw [finset.card_image_of_inj_on, card_attach, card_range],
    simp only [set.inj_on, finset.mem_range, subtype.val_eq_coe, subtype.coe_mk, mem_coe,
      mem_attach, forall_true_left, subtype.forall],
    intros n hn m hm i,
    by_contra t,
    exact distinctness t (hg _ hn) (hg _ hm) i },
  have : l ⊆ O,
  { simp only [finset.subset_iff, finset.mem_range, subtype.val_eq_coe, subtype.coe_mk,
      finset.mem_image, mem_attach, exists_true_left, subtype.exists, bex_imp_distrib],
    rintro x n hn rfl,
    exact each_mem_O (hg _ _) },
  linarith [card_le_of_subset this],
end

def k : ℕ := terminates.some
lemma k_lt_m : k < O.card := terminates.some_spec.1
lemma x__k_exists : ∃ xk, x__ k = some xk := terminates.some_spec.2.1
lemma x__k_succ_not_exists : x__ (k + 1) = none := terminates.some_spec.2.2

lemma x__eq_none_iff {i : ℕ} : x__ i = none ↔ k < i :=
begin
  split,
  { intro t,
    apply lt_of_not_le (λ hk, _),
    obtain ⟨q, hq⟩ := nat.exists_eq_add_of_le hk,
    obtain ⟨xk, hxk⟩ := x__k_exists,
    rw hq at hxk,
    obtain ⟨w, hw⟩ := eq_some_of_le hxk,
    rw t at hw,
    cases hw },
  intro t,
  by_contra q,
  rw [←ne.def, option.ne_none_iff_exists'] at q,
  obtain ⟨z, rfl⟩ := nat.exists_eq_add_of_le t,
  obtain ⟨w, hw⟩ := q,
  have := x__k_succ_not_exists,
  obtain ⟨m, hm⟩ := eq_some_of_le hw,
  rw this at hm,
  cases hm
end

lemma x__eq_some_iff {i : ℕ} : i ≤ k ↔ ∃ xi, x__ i = some xi :=
by rw [←option.ne_none_iff_exists', ne.def, x__eq_none_iff, not_lt]

lemma two_le_k : 2 ≤ k :=
begin
  rw x__eq_some_iff,
  exact ⟨_, x__2_eq⟩,
end

def x_ (i : ℕ) : ℝ := if h : i ≤ k then (x__eq_some_iff.1 h).some else x₀
lemma x_eq {i : ℕ} (hi : i ≤ k) : some (x_ i) = x__ i :=
by { rw [x_, dif_pos hi], exact (x__eq_some_iff.1 hi).some_spec.symm }
lemma x_neg {i : ℕ} (hi : k < i) : x_ i = x₀ := dif_neg hi.not_le
lemma x_mem_O {i : ℕ} : x_ i ∈ O :=
begin
  cases le_or_lt i k with hi hi,
  { exact each_mem_O (x_eq hi).symm },
  { rw x_neg hi, exact x₀_mem_O },
end

lemma x_0_eq : x_ 0 = x₀ :=
by { rw [←option.some_inj, x_eq, x__0_eq], exact zero_le_two.trans two_le_k }
lemma x_1_eq : x_ 1 = x₁ :=
by { rw [←option.some_inj, x_eq, x__1_eq], exact one_le_two.trans two_le_k }
lemma x_2_eq : x_ 2 = f x₁ :=
by { rw [←option.some_inj, x_eq two_le_k, x__2_eq] }
lemma x_k_not_switches : ∃ i ∈ O_ (x_ k), ¬ switches_sides i :=
begin
  have : x__ (k - 1 + 1) = some (x_ k),
  { rw [nat.sub_add_cancel, x_eq le_rfl],
    exact one_le_two.trans two_le_k },
  by_contra' hi,
  have z := x__eq this hi,
  rw [←nat.sub_add_comm (one_le_two.trans two_le_k), nat.add_succ_sub_one,
    x__k_succ_not_exists] at z,
  cases z
end

-- only useful when 1 ≤ i ≤ k
def J_ (i : ℕ) : set ℝ := if i < k then interval (x_ i) c ∪ I else interval (x_ k) c \ set.Ioo p q

lemma I_subset_J {i : ℕ} (hi : i < k) : I ⊆ J_ i :=
by { rw [J_, if_pos hi], exact set.subset_union_right _ _ }

lemma endpoints_in_J {i : ℕ} (hi : i < k) : p ∈ J_ i ∧ q ∈ J_ i :=
⟨I_subset_J hi p_mem_I, I_subset_J hi q_mem_I⟩

lemma I_subset_f_J {i : ℕ} (hi : i < k) (hf : continuous_on f O_int) : I ⊆ f '' J_ i :=
set.subset.trans
  (I_surj_on (hf.mono (Icc_subset_O_int_of p_mem_O q_mem_O)))
  (set.image_subset _ (I_subset_J hi))

lemma endpoints_in_f_J {i : ℕ} (hi : i < k) (hf : continuous_on f O_int) :
  p ∈ f '' J_ i ∧ q ∈ f '' J_ i :=
⟨I_subset_f_J hi hf p_mem_I, I_subset_f_J hi hf q_mem_I⟩

lemma O_subset_J {i : ℕ} (hi : i ≤ k) : (O_ (x_ i) : set ℝ) ⊆ J_ i :=
begin
  simp only [J_, O_, set.subset_def, coe_filter, sep_mem_eq, mem_inter_eq, mem_coe, and_imp],
  intros x hx hx',
  rcases hi.lt_or_eq with hi | rfl,
  { rw [if_pos hi, set.mem_union],
    exact or.inl ‹_› },
  rw [if_neg (lt_irrefl _), set.mem_diff],
  exact ⟨hx', λ i, not_mem_O_of_mem_Ioo i hx⟩,
end

lemma J_lt_interval {i : ℕ} (hi : i < k) : ∃ x y ∈ ({p, q, x_ i} : set ℝ), x ≤ y ∧ Icc x y = J_ i :=
begin
  rw [J_, if_pos hi, I],
  cases le_total (x_ i) c with hc hc,
  { refine ⟨x_ i, by simp [hi], q, by simp, hc.trans c_mem_I.2.le, _⟩,
    rw [interval_of_le hc, Icc_union_Icc' c_mem_I.1.le (hc.trans c_mem_I.2.le), min_eq_left,
      max_eq_right c_mem_I.2.le],
    by_contra',
    exact (hc.trans_lt c_mem_I.2).not_le (q_min x_mem_O this) },
  { refine ⟨p, by simp, x_ i, by simp [hi], c_mem_I.1.le.trans hc, _⟩,
    rw [interval_of_ge hc, set.union_comm, Icc_union_Icc' c_mem_I.2.le (c_mem_I.1.le.trans hc),
      min_eq_left c_mem_I.1.le, max_eq_right],
    exact q_min x_mem_O (c_mem_I.1.trans_le hc) },
end .

lemma J_k_interval {i : ℕ} (hi : k ≤ i) :
  (x_ k ≤ p ∧ Icc (x_ k) p = J_ i) ∨ (q ≤ x_ k ∧ Icc q (x_ k) = J_ i) :=
begin
  rw [J_, if_neg hi.not_lt],
  cases le_total (x_ k) c with hc hc,
  { refine or.inl ⟨le_of_not_lt (λ z, (hc.trans_lt c_mem_I.2).not_le (q_min x_mem_O z)), _⟩,
    ext i,
    simp only [set.mem_Icc, mem_diff, set.mem_Ioo, not_and', not_lt, interval_of_le hc],
    tauto {closer := `[linarith [c_mem_I.1, c_mem_I.2]]} },
  { refine or.inr ⟨q_min x_mem_O (c_mem_I.1.trans_le hc), _⟩,
    ext i,
    simp only [set.mem_Icc, set.mem_Ioo, mem_diff, not_and, not_lt, interval_of_ge hc],
    tauto {closer := `[linarith [c_mem_I.1, c_mem_I.2]]} },
end

lemma J_lt_subset_of {i : ℕ} (hi : i < k) {J : set ℝ} (hJ : is_interval J)
  (hp : p ∈ J) (hq : q ∈ J) (hx : x_ i ∈ J) : J_ i ⊆ J :=
begin
  obtain ⟨x, hx, y, hy, hxy, e⟩ := J_lt_interval hi,
  rw ←e,
  apply hJ.ord_connected.out,
  { revert x, simp [*] },
  { revert y, simp [*] },
end

lemma J_subset_k_of {i : ℕ} (hi : k ≤ i) {J : set ℝ} (hJ : is_interval J)
  (hpq : p ∈ J ∨ q ∈ J) (hx : x_ k ∈ J) : J_ i ⊆ J :=
begin
  rcases J_k_interval hi with (⟨hp₁, hp₂⟩ | ⟨hq₁, hq₂⟩),
  { rw ←hp₂,
    apply hJ.ord_connected.out hx,
    cases hpq,
    exacts [hpq, hJ.ord_connected.out hx hpq ⟨hp₁, p_lt_q.le⟩] },
  { rw ←hq₂,
    apply hJ.ord_connected.out _ hx,
    cases hpq,
    exacts [hJ.ord_connected.out hpq hx ⟨p_lt_q.le, hq₁⟩, hpq] }
end

lemma continuous_on_J_of {i : ℕ} (hf : continuous_on f O_int) : continuous_on f (J_ i) :=
begin
  cases lt_or_le i k with hi hi,
  { refine hf.mono (J_lt_subset_of hi O_int_is_interval _ _ _); apply mem_O_int_of,
    exacts [p_mem_O, q_mem_O, x_mem_O] },
  refine hf.mono (J_subset_k_of hi O_int_is_interval (or.inl _) _); apply mem_O_int_of,
  exacts [p_mem_O, x_mem_O]
end

lemma J_interval {i : ℕ} : is_interval (J_ i) :=
begin
  cases lt_or_le i k with hi hi,
  { obtain ⟨x, hx, y, hy, hxy, t⟩ := J_lt_interval hi,
    exact ⟨x, y, hxy, t.symm⟩ },
  { obtain ⟨i, t⟩ | ⟨i, t⟩ := J_k_interval hi;
    exact ⟨_, _, i, t.symm⟩ },
end

lemma J_one_eq : J_ 1 = I :=
begin
  rw [J_, if_pos, x_1_eq, union_eq_self_of_subset_left],
  { rw [interval_swap, ←interval_x_eq_I],
    apply interval_subset_interval_right,
    rw interval_x_eq_I,
    exact set.Ioo_subset_Icc_self c_mem_I },
  linarith [two_le_k],
end

lemma J_two_eq_of (hk : k = 2) :
  (f x₁ ≤ p ∧ Icc (f x₁) p = J_ 2) ∨ (q ≤ f x₁ ∧ Icc q (f x₁) = J_ 2) :=
by { convert J_k_interval hk.le; rw [hk, x_2_eq] }

lemma J_prop_one (hf : continuous_on f O_int) : surj_on f (J_ 1) (J_ 1) :=
begin
  rw [J_one_eq],
  apply I_surj_on (hf.mono (Icc_subset_O_int_of p_mem_O q_mem_O)),
end

lemma J_prop_two (hf : continuous_on f O_int) {i : ℕ} (hi₁ : 1 ≤ i) (hik : i < k) :
  surj_on f (J_ i) (J_ (i + 1)) :=
begin
  have h₁ : some (x_ i) = x__ (i - 1 + 1),
  { rw [nat.sub_add_cancel hi₁, x_eq hik.le] },
  have h₂ : some (x_ (i + 1)) = x__ (i - 1 + 2),
  { rw [←nat.sub_add_comm hi₁], exact x_eq hik },
  obtain ⟨⟨y, hy, hy'⟩, _⟩ := x__succ h₁.symm h₂.symm,
  have : y ∈ J_ i,
  { rw [J_, if_pos hik, set.mem_union],
    rw [O_, mem_filter] at hy,
    exact or.inl hy.2 },
  rw set.surj_on,
  have := endpoints_in_f_J hik hf,
  cases lt_or_eq_of_le (nat.add_one_le_iff.2 hik) with hik' hik',
  { refine J_lt_subset_of hik' (J_interval.image _) this.1 this.2 ⟨_, ‹_›, hy'⟩,
    exact continuous_on_J_of hf },
  refine J_subset_k_of hik'.ge (J_interval.image _) (or.inl this.1) ⟨y, ‹_›, by rwa ←hik'⟩,
  exact continuous_on_J_of hf,
end

lemma J_prop_three_two_case (hf : continuous_on f O_int) (hk : k = 2) :
  surj_on f (J_ k) (J_ (k - 1)) :=
begin
  rw [surj_on, hk, J_one_eq],
  obtain ⟨z, hz, hz'⟩ := x_k_not_switches,
  rw [hk, x_2_eq] at hz,
  rcases J_two_eq_of hk with (⟨h', hJ⟩ | ⟨h', hJ⟩),
  { have hp : p ∈ J_ 2, { rwa [←hJ, set.right_mem_Icc] },
    have hz'' := hz,
    rw [O_, mem_filter, interval_of_le (h'.trans c_mem_I.1.le)] at hz,
    have : z ∈ J_ 2,
    { rw ←hJ,
      refine ⟨hz.2.1, _⟩,
      exact le_of_not_lt (λ i, not_mem_O_of_mem_Ioo ⟨i, hz.2.2.trans_lt c_mem_I.2⟩ hz.1) },
    refine subset_I_of (J_interval.image (continuous_on_J_of hf)) _ (hO' _ hz.1).1
      (hO' _ p_mem_O).1 ⟨_, this, rfl⟩ ⟨_, hp, rfl⟩,
    have h₁ : same_side (f x₁) p,
    { rw same_side_iff, exact or.inr ⟨h'.trans_lt c_mem_I.1, c_mem_I.1⟩ },
    have h₂ : same_side (f x₁) z := same_side_of_mem_O (hO' _ x₁_mem_O).1 hz'',
    have h₃ : same_side z (f z) :=
      same_side_of_not_opposite_side (ne_of_mem_of_not_mem hz.1 c_not_mem_O)
        (ne_of_mem_of_not_mem (hO' _ hz.1).1 c_not_mem_O) hz',
    refine opposite_side.untrans' (same_side.symm h₃) _,
    refine opposite_side.untrans' (same_side.symm h₂) _,
    exact opposite_side.untrans' h₁ p_switches_sides },
  { have hq : q ∈ J_ 2, { rwa [←hJ, set.left_mem_Icc] },
    have hz'' := hz,
    rw [O_, mem_filter, interval_of_ge (c_mem_I.2.le.trans h')] at hz,
    have : z ∈ J_ 2,
    { rw ←hJ,
      exact ⟨q_min hz.1 (c_mem_I.1.trans_le hz.2.1), hz.2.2⟩ },
    refine subset_I_of (J_interval.image (continuous_on_J_of hf)) _ (hO' _ hz.1).1
      (hO' _ q_mem_O).1 ⟨_, this, rfl⟩ ⟨_, hq, rfl⟩,
    have h₁ : same_side (f x₁) q,
    { rw same_side_iff, exact or.inl ⟨c_mem_I.2.trans_le h', c_mem_I.2⟩ },
    have h₂ : same_side (f x₁) z := same_side_of_mem_O (hO' _ x₁_mem_O).1 hz'',
    have h₃ : same_side z (f z) :=
      same_side_of_not_opposite_side (ne_of_mem_of_not_mem hz.1 c_not_mem_O)
        (ne_of_mem_of_not_mem (hO' _ hz.1).1 c_not_mem_O) hz',
    refine opposite_side.untrans' (same_side.symm h₃) _,
    refine opposite_side.untrans' (same_side.symm h₂) _,
    exact opposite_side.untrans' h₁ q_switches_sides },
end

lemma J_prop_three (hf : continuous_on f O_int) : surj_on f (J_ k) (J_ (k - 1)) :=
begin
  have : k = 2 ∨ 3 ≤ k := eq_or_gt_of_le two_le_k,
  cases this,
  { exact J_prop_three_two_case hf this },
  have hx₂ : some (x_ (k - 2)) = x__ (k - 3 + 1),
  { rw [←nat.sub_add_comm this], exact x_eq (nat.sub_le _ _) },
  have hx₁ : some (x_ (k - 1)) = x__ (k - 3 + 2),
  { rw [←nat.sub_add_comm this], exact x_eq (nat.sub_le _ _) },
  have hx₀ : some (x_ k) = x__ (k - 3 + 3),
  { rw [←nat.sub_add_comm this], exact x_eq le_rfl },
  have : O_ (x_ (k - 2)) ⊆ O_ (x_ k),
  { refine monotone_filter_right _ _,
    refine ord_connected_interval.interval_subset _ right_mem_interval,
    refine mem_interval_of_same_side_dist (same_side.symm (same_side_twice hx₂.symm hx₀.symm)) _,
    exact (four_four hx₂.symm hx₀.symm).le },
  obtain ⟨⟨yk2, hyk2₁, hyk2₂⟩, -⟩ := x__succ hx₂.symm hx₁.symm,
  replace this := this hyk2₁,
  have := x__succ_defined hx₂.symm hx₁.symm _ hyk2₁,
  obtain ⟨z, hz, hz'⟩ := x_k_not_switches,
  have := O_subset_J le_rfl hz,
  have := O_subset_J le_rfl ‹yk2 ∈ _›,
  have : z ∈ O := filter_subset _ _ hz,
  rw surj_on,
  have : k - 1 < k := nat.sub_lt (by linarith) zero_lt_one,
  have hI : I ⊆ f '' J_ k,
  { refine subset_I_of (J_interval.image (continuous_on_J_of hf)) _
      (hO' _ ‹z ∈ O›).1 x_mem_O ⟨z, ‹_›, rfl⟩ ⟨yk2, ‹_›, hyk2₂⟩,
    have : same_side z (f z),
    { apply same_side_of_not_opposite_side _ _ hz',
      exact ne_of_mem_of_not_mem ‹z ∈ O› c_not_mem_O,
      exact ne_of_mem_of_not_mem (hO' _ ‹z ∈ O›).1 c_not_mem_O },
    have := same_side_of_mem_O x_mem_O hz,
    have := same_side_of_mem_O x_mem_O ‹yk2 ∈ O_ (x_ k)›,
    rw ←hyk2₂,
    refine opposite_side.untrans' (same_side.symm ‹same_side z (f z)›) _,
    refine opposite_side.untrans' (same_side.symm ‹same_side _ z›) _,
    exact opposite_side.untrans' ‹same_side (x_ k) yk2› ‹_› },
  refine J_lt_subset_of this (J_interval.image (continuous_on_J_of hf)) (hI p_mem_I) (hI q_mem_I) _,
  exact ⟨_, ‹_›, hyk2₂⟩,
end

omit h

end proof

-- lemma elementary_of_cycles (O : cycle ℝ) (j : list (set ℝ)) (hj : ∀ J ∈ j, is_interval J)

--   (hjO : )
