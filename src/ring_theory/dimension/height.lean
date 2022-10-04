import ring_theory.dimension.order_height
import ring_theory.dimension.minimal_primes
import ring_theory.dimension.min_generator_card
import ring_theory.dimension.noetherian
import algebra.order.pointwise

variables {R : Type*} [comm_ring R] (I : ideal R)

noncomputable
def ideal.prime_height [I.is_prime] : with_top ℕ :=
set.chain_height (set_of ideal.is_prime ∩ set.Iio I)

noncomputable
def ideal.height : with_top ℕ :=
⨅ (J ∈ I.minimal_primes), @@ideal.prime_height _ J (and.left H).1

lemma ideal.height_eq_prime_height [I.is_prime] : I.height = I.prime_height :=
begin
  delta ideal.height ideal.prime_height,
  rw [ideal.minimal_primes_eq_subsingleton_self],
  simp,
end

@[mk_iff]
class ideal.finite_height : Prop :=
(eq_top_or_height_ne_top : I = ⊤ ∨ I.height ≠ ⊤)

lemma ideal.finite_height_iff_lt {I : ideal R} : I.finite_height ↔ I = ⊤ ∨ I.height < ⊤ :=
by { rw ideal.finite_height_iff, congr', simp }

lemma ideal.height_ne_top {I : ideal R} (hI : I ≠ ⊤) [h : I.finite_height] : I.height ≠ ⊤ :=
(h.1 : _).resolve_left hI

lemma ideal.height_lt_top {I : ideal R} (hI : I ≠ ⊤) [h : I.finite_height] : I.height < ⊤ :=
lt_of_le_of_ne le_top (ideal.height_ne_top hI)

lemma ideal.prime_height_ne_top (I : ideal R) [I.finite_height] [h : I.is_prime] :
  I.prime_height ≠ ⊤ :=
I.height_eq_prime_height ▸ (ideal.height_ne_top h.1)

lemma ideal.prime_height_lt_top (I : ideal R) [I.finite_height] [h : I.is_prime] :
  I.prime_height < ⊤ :=
I.height_eq_prime_height ▸ (ideal.height_lt_top h.1)

lemma ideal.prime_height_succ [h : I.is_prime] :
  I.prime_height + 1 = set.chain_height (set_of ideal.is_prime ∩ set.Iic I) :=
begin
  convert (set.chain_height_insert_of_forall_ge _ I _).symm,
  { rw [set.insert_inter_distrib, set.insert_eq_of_mem], { simp }, { exact h } },
  { intros a ha, exact ha.2 }
end

lemma ideal.prime_height_mono {I J : ideal R} [I.is_prime] [J.is_prime] (e : I ≤ J) :
  I.prime_height ≤ J.prime_height :=
set.chain_height_le_of_subset (set.inter_subset_inter set.subset.rfl $ set.Iio_subset_Iio e)

lemma ideal.prime_height_add_one_le_of_lt {I J : ideal R} [I.is_prime] [J.is_prime] (e : I < J) :
  I.prime_height + 1 ≤ J.prime_height :=
I.prime_height_succ.trans_le
  (set.chain_height_le_of_subset (set.inter_subset_inter set.subset.rfl $ set.Iic_subset_Iio.mpr e))

lemma ideal.prime_height_strict_mono {I J : ideal R} [I.is_prime] [J.is_prime]
  (e : I < J) [J.finite_height] :
  I.prime_height < J.prime_height :=
begin
  have H := ideal.prime_height_add_one_le_of_lt e,
  cases hJ : J.prime_height with n,
  { exact (J.prime_height_ne_top hJ).elim },
  cases hI : I.prime_height with m; rw [hI, hJ] at H,
  { rw [with_top.none_eq_top, top_add, ← eq_top_iff] at H, cases H },
  { have : (m : with_top ℕ) + (1 : ℕ) ≤ n := H,
    rw [← with_top.coe_add, with_top.coe_le_coe, nat.add_one_le_iff] at this,
    exact with_top.coe_lt_coe.mpr this },
end

lemma ideal.minimal_primes_eq_empty_iff : I.minimal_primes = ∅ ↔ I = ⊤ :=
begin
  split,
  { intros e,
    by_contra h,
    obtain ⟨M, hM, hM'⟩ := ideal.exists_le_maximal I h,
    resetI,
    obtain ⟨p, hp, _⟩ := ideal.exists_minimal_primes_le hM',
    show p ∈ (∅ : set (ideal R)), by rwa ← e },
  { contrapose,
    intros h e,
    rw [← ne.def, set.ne_empty_iff_nonempty] at h,
    obtain ⟨p, hp⟩ := h,
    exact (hp.1.1.1 : _) (eq_top_iff.mpr (e.symm.trans_le hp.1.2)) }
end

lemma ideal.minimal_primes_top : (⊤ : ideal R).minimal_primes = ∅ :=
(ideal.minimal_primes_eq_empty_iff _).mpr rfl

lemma ideal.height_top : ideal.height (⊤ : ideal R) = ⊤ :=
begin
  simp_rw [ideal.height, ideal.prime_height, ideal.minimal_primes_top],
  simp
end

lemma ideal.height_mono {I J : ideal R} (h : I ≤ J) : I.height ≤ J.height :=
begin
  apply le_infi₂ _,
  intros p hp,
  haveI := hp.1.1,
  obtain ⟨q, hq, e⟩ := ideal.exists_minimal_primes_le (h.trans hp.1.2),
  haveI := hq.1.1,
  exact (infi₂_le q hq).trans (ideal.prime_height_mono e)
end

lemma with_top.supr_add {ι : Sort*} [nonempty ι]
  (f : ι → with_top ℕ) (x : with_top ℕ) :
  supr f + x = ⨆ i, f i + x :=
begin
  cases x, { simp_rw [with_top.none_eq_top, add_top, supr_const] },
  have : ↑x ≤ ⨆ i, f i + ↑x,
  { refine le_trans _ (le_supr _ $ classical.arbitrary _), exact le_add_left rfl.le },
  rw with_top.some_eq_coe,
  apply le_antisymm,
  { rw [← tsub_add_cancel_of_le this],
    refine add_le_add (supr_le $ λ i, _) rfl.le,
    apply (with_top.add_le_add_iff_right (with_top.coe_ne_top : (x : with_top ℕ) ≠ ⊤)).mp,
    rw [tsub_add_cancel_of_le this],
    exact le_supr _ i },
  { exact supr_le (λ i, add_le_add (le_supr f i) rfl.le) }
end

lemma with_top.supr₂_add {ι : Sort*} {p : ι → Sort*} (hs : Exists p)
  (f : ∀ (i : ι), p i → with_top ℕ) (x : with_top ℕ) :
  (⨆ (i : ι) (h : p i), f i h) + x = ⨆ (i : ι) (h : p i), f i h + x :=
begin
  haveI : nonempty { i // p i } := ⟨⟨_, hs.some_spec⟩⟩,
  rw [supr_subtype', supr_subtype', with_top.supr_add]
end

noncomputable
def krull_dimension (R : Type*) [comm_ring R] : with_top ℕ :=
⨆ (I : ideal R) [I.is_prime], by exactI I.prime_height

@[mk_iff]
class finite_krull_dimensional (R : Type*) [comm_ring R] : Prop :=
(krull_dimension_ne_top : krull_dimension R ≠ ⊤)

lemma krull_dimension_ne_top (R : Type*) [comm_ring R] [h : finite_krull_dimensional R] :
  krull_dimension R ≠ ⊤ :=
h.1

lemma krull_dimension_lt_top (R : Type*) [comm_ring R] [finite_krull_dimensional R] :
  krull_dimension R < ⊤ :=
lt_of_le_of_ne le_top (krull_dimension_ne_top R)

lemma finite_krull_dimensional_iff_lt :
  finite_krull_dimensional R ↔ krull_dimension R < ⊤ :=
by simp [finite_krull_dimensional_iff]

lemma krull_dimension_of_subsingleton (R : Type*) [comm_ring R] [subsingleton R] :
  krull_dimension R = 0 :=
begin
  apply supr₂_eq_bot.mpr,
  intros i hI,
  exact ((hI.1 : _) (subsingleton.elim _ _)).elim
end

@[priority 100]
instance finite_krull_dimensional_of_subsingleton [subsingleton R] : finite_krull_dimensional R :=
by { rw [finite_krull_dimensional_iff, krull_dimension_of_subsingleton], rintro ⟨⟩ }

lemma ideal.prime_height_le_krull_dimension [I.is_prime] : I.prime_height ≤ krull_dimension R :=
le_supr₂ _ _

@[priority 900]
instance ideal.finite_height_of_finite_dimensional [finite_krull_dimensional R] [nontrivial R] :
  I.finite_height :=
begin
  rw [ideal.finite_height_iff_lt, or_iff_not_imp_left],
  intro e,
  obtain ⟨M, hM, hM'⟩ := ideal.exists_le_maximal I e,
  refine (ideal.height_mono hM').trans_lt (has_le.le.trans_lt _ (krull_dimension_lt_top R)),
  resetI,
  rw ideal.height_eq_prime_height,
  exact M.prime_height_le_krull_dimension
end

lemma krull_dimension_succ (R : Type*) [comm_ring R] [nontrivial R] :
  krull_dimension R + 1 = set.chain_height (set_of ideal.is_prime : set (ideal R)) :=
begin
  have : ∃ I : ideal R, I.is_prime := ⟨_, (ideal.exists_maximal R).some_spec.is_prime⟩,
  rw [krull_dimension, with_top.supr₂_add this, set.chain_height_eq_supr_Iic],
  simpa only [ideal.prime_height_succ]
end

variables {I}

lemma ideal.prime_height_eq_zero_iff [I.is_prime] : I.prime_height = 0 ↔ I ∈ minimal_primes R :=
begin
  rw [ideal.prime_height, set.chain_height_eq_zero_iff],
  split,
  { intro e,
    refine ⟨⟨infer_instance, bot_le⟩, λ J hJ e', (eq_of_le_of_not_lt e' _).symm.le⟩,
    intro e'',
    show J ∈ (∅ : set (ideal R)),
    rw ← e,
    exact ⟨hJ.1, e''⟩ },
  { intro hI,
    ext J,
    suffices : J.is_prime → ¬J < I, { simpa },
    intros hJ e,
    exact not_le_of_lt e (hI.2 ⟨hJ, bot_le⟩ e.le) }
end

lemma ideal.is_maximal_of_prime_height_eq_krull_dimesion
  [h : I.is_prime] [finite_krull_dimensional R]
  (e : I.prime_height = krull_dimension R) : I.is_maximal :=
begin
  casesI subsingleton_or_nontrivial R,
  { exact ((h.1 : _) $ subsingleton.elim _ _).elim },
  have := congr_arg (λ x : with_top ℕ, x + 1) e,
  dsimp at this,
  rw [ideal.prime_height_succ] at this,
  refine ⟨⟨h.1, _⟩⟩,
  intros J hJ,
  by_contra e',
  obtain ⟨M, hM, hM'⟩ := ideal.exists_le_maximal J e',
  have H : (insert M (set_of ideal.is_prime ∩ set.Iic I)).chain_height =
    krull_dimension R + 1 + 1,
  { rw [← this, set.chain_height_insert_of_forall_ge],
    intros I' hI',
    calc I' ≤ I : hI'.2
        ... < J : hJ
        ... ≤ M : hM' },
  have : krull_dimension R + 1 + 1 ≤ set.chain_height (set_of ideal.is_prime),
  { rw ← H, apply set.chain_height_le_of_subset, rintros K (rfl|⟨h, _⟩), exacts [hM.is_prime, h] },
  cases h : krull_dimension R with x,
  { exact krull_dimension_ne_top R h },
  { rw [← krull_dimension_succ, h] at this, linarith [with_top.coe_le_coe.mp this] }
end

lemma local_ring.maximal_ideal_prime_height [local_ring R] :
  (local_ring.maximal_ideal R).prime_height = krull_dimension R :=
begin
  apply le_antisymm,
  { apply ideal.prime_height_le_krull_dimension },
  { apply supr₂_le _,
    introsI I hI,
    apply ideal.prime_height_mono,
    exact local_ring.le_maximal_ideal hI.1 }
end

lemma local_ring.maximal_ideal_height [local_ring R] :
  (local_ring.maximal_ideal R).height = krull_dimension R :=
by rw [ideal.height_eq_prime_height, local_ring.maximal_ideal_prime_height]

lemma ideal.prime_height_eq_krull_dimesion_iff [local_ring R] [I.is_prime]
  [finite_krull_dimensional R] :
  I.prime_height = krull_dimension R ↔ I = local_ring.maximal_ideal R :=
begin
  split,
  { exact λ e, local_ring.eq_maximal_ideal (ideal.is_maximal_of_prime_height_eq_krull_dimesion e) },
  { unfreezingI { rintro rfl }, rw local_ring.maximal_ideal_prime_height }
end

lemma submodule.size_eq_zero_iff : I.size = 0 ↔ I = ⊥ :=
begin
  split,
  { intro e,
    have H : submodule.fg I,
    { rw [← submodule.size_ne_top_iff, e], rintro ⟨⟩ },
    rw [H.size_eq, ← with_top.coe_zero, with_top.coe_eq_coe] at e,
    have := H.exists_generator_eq_min_generator_card,
    rw e at this,
    obtain ⟨f, hf⟩ := this,
    rwa [show set.range f = ∅, by simp, submodule.span_empty, eq_comm] at hf },
  { rintro rfl,
    rw [← bot_eq_zero, eq_bot_iff, bot_eq_zero, bot_eq_zero, ← with_top.coe_zero,
      submodule.fg.min_generator_card_le_iff_exists],
    have f : fin 0 → R := λ _, 0,
    refine ⟨f, by rw [show set.range f = ∅, by simp, submodule.span_empty, bot_eq_zero]⟩ }
end

lemma submodule.size_sup {p q : ideal R} :
  (p ⊔ q).size ≤ p.size + q.size :=
begin
  by_cases hp : submodule.fg p,
  swap,
  { rw [← submodule.size_ne_top_iff, not_ne_iff] at hp,
    rw [hp, top_add], exact le_top },
  by_cases hq : submodule.fg q,
  swap,
  { rw [← submodule.size_ne_top_iff, not_ne_iff] at hq,
    rw [hq, add_top], exact le_top },
  obtain ⟨f, hf⟩ := hp.exists_generator_eq_min_generator_card,
  obtain ⟨g, hg⟩ := hq.exists_generator_eq_min_generator_card,
  rw submodule.fg_iff_size_eq at hp hq,
  rw [hp, hq, ← with_top.coe_add, submodule.fg.min_generator_card_le_iff_exists],
  refine ⟨(sum.elim f g) ∘ fin_sum_fin_equiv.symm, _⟩,
  rw [set.range_comp, set.range_iff_surjective.mpr (equiv.surjective _), set.image_univ,
    set.sum.elim_range, submodule.span_union, hf, hg],
end

lemma submodule.min_generator_card_span_set_finite {s : set R} (hs : s.finite) :
  (submodule.span R s).size ≤ hs.to_finset.card :=
begin
  rw submodule.fg.min_generator_card_le_iff_exists,
  refine ⟨subtype.val ∘ hs.to_finset.equiv_fin.symm, _⟩,
  rw [set.range_comp, set.range_iff_surjective.mpr (equiv.surjective _), set.image_univ,
    subtype.range_val],
  congr, ext, exact hs.mem_to_finset,
end

lemma submodule.size_bot : (⊥ : ideal R).size = 0 :=
submodule.size_eq_zero_iff.mpr rfl

lemma mem_minimal_primes_of_height_eq {I J : ideal R} [J.is_prime] (e : I ≤ J)
  (e' : I.height = J.prime_height) [J.finite_height] : J ∈ I.minimal_primes :=
begin
  refine ⟨⟨infer_instance, e⟩, λ K hK e'', (eq_of_le_of_not_lt e'' _).symm.le⟩,
  intro e''',
  haveI := hK.1,
  rw ← lt_self_iff_false J.prime_height,
  calc J.prime_height = I.height       : e'.symm
                  ... ≤ K.height       : ideal.height_mono hK.2
                  ... = K.prime_height : K.height_eq_prime_height
                  ... < J.prime_height : ideal.prime_height_strict_mono e'''
end

lemma exists_size_le_and_le_height_of_le_height [is_noetherian_ring R] (I : ideal R) (r : ℕ)
  (hr : ↑r ≤ I.height) :
  ∃ J ≤ I, J.size ≤ r ∧ ↑r ≤ J.height :=
begin
  induction r with r H,
  { refine ⟨⊥, bot_le, _, zero_le _⟩, rw submodule.size_bot, exact rfl.le },
  { obtain ⟨J, h₁, h₂, h₃⟩ := H ((with_top.coe_le_coe.mpr r.le_succ).trans hr),
    let S := { K | K ∈ J.minimal_primes ∧ ideal.height K = r },
    have hS : S.finite := set.finite.subset J.minimal_primes_finite (λ _ h, h.1),
    have : ¬ ↑I ⊆ ⋃ J ∈ hS.to_finset, (J : set R),
    { refine (ideal.subset_union_prime ⊥ ⊥ _).not.mpr _,
      { rintro K hK - -, rw set.finite.mem_to_finset at hK, exact hK.1.1.1 },
      { push_neg,
        intros K hK e,
        have := hr.trans (ideal.height_mono e),
        rw set.finite.mem_to_finset at hK,
        rw [hK.2, with_top.coe_le_coe, ← not_lt] at this,
        exact this r.lt_succ_self } },
    simp_rw [set.not_subset, set.mem_Union, not_exists, set.finite.mem_to_finset] at this,
    obtain ⟨x, hx₁, hx₂⟩ := this,
    refine ⟨J ⊔ ideal.span {x}, sup_le h₁ _, _, _⟩,
    { rwa [ideal.span_le, set.singleton_subset_iff] },
    { refine submodule.size_sup.trans _,
      rw [nat.succ_eq_add_one, with_top.coe_add],
      refine add_le_add h₂ _,
      refine (submodule.min_generator_card_span_set_finite $ set.to_finite _).trans _,
      simp },
    { refine le_infi₂ _,
      intros p hp,
      haveI := hp.1.1,
      by_cases p.height = ⊤,
      { rw [← p.height_eq_prime_height, h], exact le_top },
      haveI : p.finite_height := ⟨or.inr h⟩,
      have := ideal.height_mono (le_sup_left.trans hp.1.2),
      suffices h : ↑r ≠ p.prime_height,
      { rw [nat.succ_eq_add_one, with_top.coe_add],
        have := h₃.trans this,
        rw ideal.height_eq_prime_height at this,
        exact enat.add_one_le_of_lt (lt_of_le_of_ne this h) },
      intro e,
      apply hx₂ p,
      { have : J.height = p.prime_height,
        { apply le_antisymm, { rwa ← p.height_eq_prime_height }, { rwa ← e } },
        refine ⟨mem_minimal_primes_of_height_eq (le_sup_left.trans hp.1.2) this, _⟩,
        rwa [p.height_eq_prime_height, eq_comm] },
      { apply hp.1.2,
        apply ideal.mem_sup_right,
        apply ideal.subset_span,
        exact set.mem_singleton _ } } }
end
