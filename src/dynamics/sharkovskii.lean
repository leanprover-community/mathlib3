import data.real.basic
import data.real.pointwise
import dynamics.periodic_pts
import topology.continuous_function.basic
import topology.instances.real

open set

variables {f : ℝ → ℝ} {I I₁ I₂ I₃ J J₁ J₂ : set ℝ}

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

lemma surj_on.exists_maps_to (hI : is_interval I) (hJ : is_interval J) (hf : continuous_on f I)
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

def is_loop (f : ℝ → ℝ) (j : list (set ℝ)) := j.chain (surj_on f) j.ilast
lemma is_loop_iff : ∀ {j : list (set ℝ)}, is_loop f j ↔ list.chain' (surj_on f) (j ++ [j.head])
| [] := by simp [is_loop]
| [J] := by simpa [is_loop]
| [J₁, J₂] := by simpa [is_loop] using and_comm _ _
| (J₁ :: J₂ :: J₃ :: Js) :=
  begin
    rw [is_loop, list.cons_append, list.chain', list.chain_iff_forall₂, list.chain_iff_forall₂],
    simp only [list.init_cons_of_ne_nil, ne.def, not_false_iff, list.forall₂_cons, false_or,
      list.head_cons, list.cons_append, list.append_eq_nil, and_false, list.init_append_of_ne_nil,
      list.ilast, list.init, list.append_nil],

    -- rw forall₂,
    -- rw chain_append_singleton_iff_forall₂,
    -- rw [list.head_cons, is_loop],
    -- rw list.ilast,
    -- rw [list.cons_append, list.cons_append, list.cons_append, list.chain'_cons, list.chain'_cons,
    --   list.chain_cons],
  end

lemma is_loop_singleton_iff : is_loop f [I] ↔ surj_on f I I :=
by simpa only [is_loop, list.chain_singleton, and_true]

lemma is_loop_pair_iff : is_loop f [I, J] ↔ surj_on f I J ∧ surj_on f J I :=
by { rw [is_loop, list.chain_cons, list.chain_singleton, and_comm], refl }

lemma is_loop_triple_iff :
  is_loop f [I₁, I₂, I₃] ↔ surj_on f I₁ I₂ ∧ surj_on f I₂ I₃ ∧ surj_on f I₃ I₁ :=
by { rw [is_loop, list.chain_cons, list.chain_cons, and_rotate, list.chain_singleton], refl }

def follows_loop (f : ℝ → ℝ) (j : list (set ℝ)) (p : ℝ) : Prop :=
  function.is_periodic_pt f j.length p ∧ ∀ i < j.length, f^[i] p ∈ j.nth_le i H

lemma itinerary (j : list (set ℝ)) (hj : ∀ J ∈ j, is_interval J) :
  Exists (follows_loop f j) :=
begin

end
