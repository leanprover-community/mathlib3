import ring_theory.euclidean_domain data.polynomial ring_theory.principal_ideal_domain

universes u v w

variables {α : Type u} {β : Type v} {γ : Type w}

namespace adjoin_root
open polynomial ideal

section comm_ring
variables [comm_ring α] [decidable_eq α] (f : polynomial α)

def adjoin_root (f : polynomial α) : Type u :=
ideal.quotient (span {f} : ideal (polynomial α))

instance : comm_ring (adjoin_root f) := ideal.quotient.comm_ring _

variable {f}

def mk : polynomial α → adjoin_root f := ideal.quotient.mk _

def root : adjoin_root f := mk X

def of (x : α) : adjoin_root f := mk (C x)

instance adjoin_root.has_coe_t : has_coe_t α (adjoin_root f) := ⟨of⟩

instance mk.is_ring_hom : is_ring_hom (mk : polynomial α → adjoin_root f) :=
ideal.quotient.is_ring_hom_mk _

@[simp] lemma mk_self : (mk f : adjoin_root f) = 0 :=
quotient.sound' (mem_span_singleton.2 $ by simp)

instance : is_ring_hom (coe : α → adjoin_root f) :=
@is_ring_hom.comp _ _ _ _ C _ _ _ mk mk.is_ring_hom

lemma eval₂_root (f : polynomial α) [irreducible f] : f.eval₂ coe (root : adjoin_root f) = 0 :=
quotient.induction_on' (root : adjoin_root f)
  (λ (g : polynomial α) (hg : mk g = mk X),
    show finsupp.sum f (λ (e : ℕ) (a : α), mk (C a) * mk g ^ e) = 0,
    by simp only [hg, (is_semiring_hom.map_pow (mk : polynomial α → adjoin_root f) _ _).symm,
         (is_ring_hom.map_mul (mk : polynomial α → adjoin_root f)).symm];
      rw [finsupp.sum, finset.sum_hom (mk : polynomial α → adjoin_root f),
        show finset.sum _ _ = _, from sum_C_mul_X_eq _, mk_self])
  (show (root : adjoin_root f) = mk X, from rfl)

variables [comm_ring β]

def lift (i : α → β) [is_ring_hom i] (x : β) (h : f.eval₂ i x = 0) : (adjoin_root f) → β :=
ideal.quotient.lift _ (eval₂ i x) $ λ g H,
by
  simp [mem_span_singleton] at H;
  cases H with y H;
  dsimp at H;
  rw [H, eval₂_mul];
  simp [h]

variables {i : α → β} [is_ring_hom i] {a : β} {h : f.eval₂ i a = 0}

@[simp] lemma lift_mk {g : polynomial α} : lift i a h (mk g) = g.eval₂ i a :=
ideal.quotient.lift_mk

@[simp] lemma lift_root : lift i a h root = a := by simp [root, h]

@[simp] lemma lift_of {x : α} : lift i a h x = i x :=
by show lift i a h (ideal.quotient.mk _ (C x)) = i x;
  convert ideal.quotient.lift_mk; simp

instance is_ring_hom_lift : is_ring_hom (lift i a h) :=
by unfold lift; apply_instance

end comm_ring

variables [discrete_field α] {f : polynomial α} [irreducible f]

instance is_maximal_span : is_maximal (span {f} : ideal (polynomial α)) :=
principal_ideal_domain.is_maximal_of_irreducible ‹irreducible f›

noncomputable instance field : discrete_field (adjoin_root f) :=
{ has_decidable_eq := λ p q, @quotient.rec_on_subsingleton₂ _ _ (id _) (id _)
    (λ p q, decidable (p = q)) _ p q (λ p q, show decidable (mk p = mk q),
      from decidable_of_iff ((p - q) % f = 0)
        (by simp [mk, ideal.quotient.eq, mem_span_singleton])),
  inv_zero := by convert dif_pos rfl,
  ..adjoin_root.comm_ring f,
  ..ideal.quotient.field (span {f} : ideal (polynomial α)) }

instance : is_field_hom (coe : α → adjoin_root f) := by apply_instance

instance lift_is_field_hom [field β] {i : α → β} [is_ring_hom i] {a : β}
  {h : f.eval₂ i a = 0} : is_field_hom (lift i a h) := by apply_instance

lemma coe_injective : function.injective (coe : α → adjoin_root f) :=
is_field_hom.injective _

end adjoin_root

namespace splitting_field

variables [discrete_field α] [discrete_field β] [discrete_field γ]
open polynomial adjoin_root

def irr_factor (f : polynomial α) :
  polynomial α := sorry

lemma irr_factor_irreducible {f : polynomial α} (hf : degree f ≠ 0):
  irreducible (irr_factor f) := sorry

lemma irr_factor_dvd (f : polynomial α) :
  irr_factor f ∣ f := sorry

set_option eqn_compiler.zeta true

-- local attribute [instance, priority 0] classical.prop_decidable

-- def splitting_field : Π {α : Type u} [discrete_field α], by exactI polynomial α → Type u
-- | α I f := by exactI
--   if h1 : degree f ≤ 1 then α
--   else
--   have wf : degree (f.map (coe : α → adjoin_root (irr_factor f h1)) /
--     (X - C root)) < degree f,
--     from splitting_field_wf_lemma,
--   splitting_field (f.map (coe : α → adjoin_root (irr_factor f h1)) / (X - C root))
-- using_well_founded {rel_tac := λ _ _, `[exact ⟨_, inv_image.wf
--     (λ x : Σ' (α : Type u) (I : discrete_field α), by exactI polynomial α,
--     by letI := x.2.1; exact x.2.2.degree)
--     (with_bot.well_founded_lt nat.lt_wf)⟩],
--   dec_tac := tactic.assumption}

section splits

variables (i : α → β) [is_field_hom i]

def splits (f : polynomial α) : Prop :=
f = 0 ∨ ∀ {g : polynomial β}, irreducible g → g ∣ f.map i → degree g = 1

@[simp] lemma splits_zero : splits i (0 : polynomial α) := or.inl rfl

@[simp] lemma splits_C (a : α) : splits i (C a) :=
if ha : a = 0 then ha.symm ▸ (@C_0 α _ _).symm ▸ splits_zero i
else
have hia : i a ≠ 0, from mt ((is_add_group_hom.injective_iff i).1
  (is_field_hom.injective i) _) ha,
or.inr $ λ g hg ⟨p, hp⟩, absurd hg.1 (classical.not_not.2 (is_unit_iff_degree_eq_zero.2 $
  by have := congr_arg degree hp;
    simp [degree_C hia, @eq_comm (with_bot ℕ) 0,
      nat.with_bot.add_eq_zero_iff] at this; tautology))

lemma splits_of_degree_eq_one {f : polynomial α} (hf : degree f = 1) : splits i f :=
or.inr $ λ g hg ⟨p, hp⟩,
  by have := congr_arg degree hp;
  simp [nat.with_bot.add_eq_one_iff, hf, @eq_comm (with_bot ℕ) 1,
    mt is_unit_iff_degree_eq_zero.2 hg.1] at this;
  clear _fun_match; tauto

lemma splits_of_degree_le_one {f : polynomial α} (hf : degree f ≤ 1) : splits i f :=
begin
  cases h : degree f with n,
  { rw [degree_eq_bot.1 h]; exact splits_zero i },
  { cases n with n,
    { rw [eq_C_of_degree_le_zero (trans_rel_right (≤) h (le_refl _))];
      exact splits_C _ _ },
    { have hn : n = 0,
      { rw h at hf,
        cases n, { refl }, { exact absurd hf dec_trivial } },
      exact splits_of_degree_eq_one _ (by rw [h, hn]; refl) } }
end

lemma splits_mul {f g : polynomial α} (hf : splits i f) (hg : splits i g) : splits i (f * g) :=
if h : f * g = 0 then by simp [h]
else or.inr $ λ p hp hpf, ((principal_ideal_domain.prime_of_irreducible hp).2.2 _ _
    (show p ∣ map i f * map i g, by convert hpf; rw map_mul)).elim
  (hf.resolve_left (λ hf, by simpa [hf] using h) hp)
  (hg.resolve_left (λ hg, by simpa [hg] using h) hp)

lemma splits_of_splits_mul {f g: polynomial α} (hfg : f * g ≠ 0) (h : splits i (f * g)) :
  splits i f ∧ splits i g :=
⟨or.inr $ λ g hgi hg, or.resolve_left h hfg hgi (by rw map_mul; exact dvd.trans hg (dvd_mul_right _ _)),
 or.inr $ λ g hgi hg, or.resolve_left h hfg hgi (by rw map_mul; exact dvd.trans hg (dvd_mul_left _ _))⟩

lemma splits_map_iff (j : β → γ) [is_field_hom j] {f : polynomial α} :
  splits j (f.map i) ↔ splits (λ x, j (i x)) f :=
by simp [splits, polynomial.map_map]

lemma splits_of_splits_id  : ∀ {f : polynomial α}
  (h : splits id f), splits i f
| f := λ h,
  if hf : degree f ≤ 1 then splits_of_degree_le_one _ hf
  else have hfi : ¬irreducible f := mt (h.resolve_left (λ hf0, by simpa [hf0] using hf))
    (show ¬ (f ∣ f.map id → degree f = 1),
      from λ h, absurd (h (by simp))
        (λ h, by simpa [h, lt_irrefl] using hf)),
  have hfu : ¬is_unit f,
    from λ h, by rw [is_unit_iff_degree_eq_zero] at h; rw h at hf;
      exact hf dec_trivial,
  let ⟨p, q, hpu, hqu, hpq⟩ := (irreducible_or_factor _ hfu).resolve_left hfi in
  have hpq0 : p * q ≠ 0, from λ hpq0, by simpa [hpq.symm, hpq0] using hf,
  have hf0 : f ≠ 0, from λ hf0, by simpa [hf0] using hf,
  have hwfp : degree p < degree f,
    by rw [euclidean_domain.eq_div_of_mul_eq_left (ne_zero_of_mul_ne_zero_left hpq0) hpq];
      exact degree_div_lt hf0  (degree_pos_of_ne_zero_of_nonunit
        (ne_zero_of_mul_ne_zero_left hpq0) hqu),
  have hwfp : degree q < degree f,
    by rw [euclidean_domain.eq_div_of_mul_eq_right (ne_zero_of_mul_ne_zero_right hpq0) hpq];
      exact degree_div_lt hf0  (degree_pos_of_ne_zero_of_nonunit
        (ne_zero_of_mul_ne_zero_right hpq0) hpu),
  (splits_map_iff id _).1 $ begin
    rw [map_id, ← hpq],
    rw [← hpq] at h,
    exact splits_mul _ (splits_of_splits_id (splits_of_splits_mul _ hpq0 h).1)
      (splits_of_splits_id (splits_of_splits_mul _ hpq0 h).2)
  end
using_well_founded {dec_tac := tactic.assumption}

lemma splits_comp_of_splits (j : β → γ) [is_field_hom j] {f : polynomial α}
  (h : splits i f) : splits (λ x, j (i x)) f :=
begin
  change i with (λ x, id (i x)) at h,
  rw [← splits_map_iff],
  rw [← splits_map_iff i id]  at h,
  exact splits_of_splits_id _ h
end

lemma exists_root_of_splits {f : polynomial α} (hs : splits i f) (hf0 : degree f ≠ 0) :
  ∃ x, eval₂ i x f = 0 :=
hs.elim (λ hf0, ⟨37, by simp [hf0]⟩) $
λ hs, let ⟨x, hx⟩ := exists_root_of_degree_eq_one
  (hs (splitting_field.irr_factor_irreducible (show degree (f.map i) ≠ 0, by simp [hf0]))
    (irr_factor_dvd _)) in ⟨x, let ⟨g, hg⟩ := irr_factor_dvd (f.map i) in
  by rw [← eval_map, hg, eval_mul, (show _ = _, from hx), zero_mul]⟩

end splits
set_option profiler true

noncomputable theory

lemma splitting_field_aux : Π {α : Type u} [discrete_field α] (f : by exactI polynomial α),
  by exactI Σ' (β : Type u) [discrete_field β] (i : α → β) [is_field_hom i]
  (hs : by exactI splits i f), ∀ {γ : Type u} [discrete_field γ] (j : α → γ)
  [is_field_hom j] (hj : by exactI splits j f),
  ∃ k : β → γ, (∀ x, k (i x) = j x) ∧ is_field_hom k
| α I f := by exactI
if hf : degree f ≤ 1
then ⟨α, I, id, by apply_instance, splits_of_degree_le_one _ hf,
  λ γ _ j Ij hj, ⟨j, λ _, rfl, Ij⟩⟩
else
have hif : irreducible (irr_factor f), from sorry,
have hf0 : f ≠ 0, from λ hf0, hf (by rw hf0; exact dec_trivial),
have wf : by exactI degree (f.map (coe : α → adjoin_root
    (irr_factor f)) / (X - C root)) < degree f,
  by rw [← degree_map f (coe : α → adjoin_root (irr_factor f))];
    exact degree_div_lt (mt (map_eq_zero _).1 hf0)
      (by rw degree_X_sub_C; exact dec_trivial),
begin
  resetI,
  have hf0 : f ≠ 0, from λ hf0, hf (by rw hf0; exact dec_trivial),
  have ih := splitting_field_aux (f.map (coe : α → adjoin_root
      (irr_factor f)) / (X - C root)),
  rcases ih with ⟨β, I, i, Ii, hsβ, hiβ⟩,
  letI := Ii, letI := I,
  refine ⟨β, I, λ a, i ↑a, is_ring_hom.comp _ _, _⟩,
  have hmuldiv : ((X : polynomial (adjoin_root (irr_factor f))) - C root) *
      (f.map coe / (X - C root)) = f.map coe,
    from mul_div_eq_iff_is_root.2
      (show _ = _, begin
          cases irr_factor_dvd f with j hj,
          conv_lhs { congr, skip, congr, skip, rw hj },
          rw [eval_map (coe : α → adjoin_root (irr_factor f)), eval₂_mul, eval₂_root, zero_mul],
        end),
  split,
  -- proof of splitting property
  { rw [← splits_map_iff _ i, ← hmuldiv],
    exact splits_mul _ (splits_of_degree_eq_one _ (degree_X_sub_C _)) hsβ },
  -- definition of homomorphism
  { introsI γ Iγ j Ij hjs,
    cases irr_factor_dvd f with g hg,
    -- show ∃ x, eval₂ j x (irr_factor f) = 0
    cases exists_root_of_splits j
      (splits_of_splits_mul j (λ hfi : irr_factor f * g = 0, hf
          (by rw [hg, hfi, degree_zero]; exact dec_trivial))
        (show splits j (irr_factor f * g), from hg ▸ hjs)).1
      (by rw [ne.def, ← is_unit_iff_degree_eq_zero]; exact hif.1) with x hx,

    have h₁ : splits (lift j x hx) (map coe f / (X - C root)) :=
      (splits_of_splits_mul _
        (show ((X : polynomial (adjoin_root (irr_factor f))) - C root) *
            (f.map coe / (X - C root)) ≠ 0,
          by rw [hmuldiv, ne.def, map_eq_zero]; exact hf0)
        (show splits (lift j x hx) ((X - C root) * (map coe f / (X - C root))),
          by rw [hmuldiv, splits_map_iff (coe : α → adjoin_root (irr_factor f))];
            simp only [lift_of, hjs])).2,
    cases hiβ (adjoin_root.lift j x hx) h₁ with k hk,
    exact ⟨k, λ x, by rw [hk.1, lift_of], hk.2⟩ }
end
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, inv_image.wf
    (λ x : Σ' (α : Type u) (I : discrete_field α), by exactI polynomial α,
    by letI := x.2.1; exact x.2.2.degree)
    (with_bot.well_founded_lt nat.lt_wf)⟩],
  dec_tac := tactic.assumption }

def splitting_field (f : polynomial α) : Type u :=
(splitting_field_aux.{u} f).1

instance (f : polynomial α) : discrete_field (splitting_field f) :=
(splitting_field_aux f).2.1

def mk (f : polynomial α) : α → splitting_field f :=
(splitting_field_aux f).2.2.1

instance (f : polynomial α) : has_coe α (splitting_field f) := ⟨mk f⟩

instance mk_is_field_hom (f : polynomial α) : is_field_hom (mk f) :=
by exact (splitting_field_aux f).2.2.2.1

instance coe_is_field_hom (f : polynomial α) : is_field_hom (coe : α → splitting_field f) :=
splitting_field.mk_is_field_hom f

lemma splitting_field_splits (f : polynomial α) : splits (mk f) f :=
(splitting_field_aux f).2.2.2.2.1

def splitting_field_hom {f : polynomial α} (j : α → β)
  [is_field_hom j] (hj : splits j f) : splitting_field f → β :=
classical.some ((splitting_field_aux f).2.2.2.2.2 j hj)

#exit
#print splitting_field_aux'
-- def splitting_field_aux' : Π {n : ℕ} {α : Type u} [discrete_field α] (f : by exactI polynomial α)
--   (h : by exactI nat_degree f = n), by exactI ∃ (β : Type u) [discrete_field β] (i : α → β) [is_field_hom i],
--   by exactI splits i f
-- | 0       := λ α I f h, by exactI ⟨α, I, id, is_ring_hom.id, splits_of_degree_le_one _
--   (calc degree f)⟩
-- | 1       := λ α I f h, by exactI ⟨α, I, id, is_ring_hom.id, splits_of_degree_le_one
--   (by exactI calc degree (map id f) ≤ nat_degree f :
--       by rw [degree_map]; exact degree_le_nat_degree
--     ... ≤ 1 : by rw h; exact dec_trivial)⟩
-- | (n+2) := λ α I f h,
-- begin
--   resetI,
--   letI : irreducible (irr_factor f) := sorry,
--   have wf : nat_degree (f.map (coe : α → adjoin_root
--     (irr_factor f)) / (X - C root)) = n + 1, from sorry,
--   rcases splitting_field_aux' (f.map (coe : α → adjoin_root
--     (irr_factor f)) / (X - C root)) wf with ⟨β, I, i, Ii, hβ⟩,
--   letI := Ii, letI := I,
--   refine ⟨β, I, λ a, i ↑a,
--     by haveI := Ii; letI := I; exact is_ring_hom.comp _ _, _⟩,
--   have h₁ : ((X : polynomial β) - C (i root)) *
--       (f.map (λ a, i ↑a) / (X - C (i root))) = f.map (λ a, i ↑a),
--     from mul_div_eq_iff_is_root.2
--       (show _ = _, begin
--           cases irr_factor_dvd f with j hj,
--           rw [← polynomial.map_map (coe : α → adjoin_root (irr_factor f)),
--             eval_map, eval₂_hom, eval_map],
--           conv in f { rw hj },
--           rw [eval₂_mul, eval₂_root, zero_mul, is_ring_hom.map_zero i],
--         end),
--   rw ← h₁,
--   refine splits_mul (splits_of_degree_eq_one (degree_X_sub_C _)) _,
--   rw [← polynomial.map_map coe i, ← map_C i, ← map_X i, ← map_sub i,
--        ← map_div i],
--   exact hβ
-- end

#print splitting_field_aux'


def splitting_field_aux : Π {n : ℕ} {α : Type u} [discrete_field α] (f : by exactI polynomial α),
  by exactI nat_degree f = n → Type u
| 0 := λ α I f hf, α
| 1 := λ α I f hf, α
| (n+2) := λ α I f hf, by exactI
  have hf' : nat_degree (f.map (coe : α → adjoin_root (irr_factor f
    (by rw hf; exact dec_trivial))) / (X - C root)) = n + 1, from sorry,
  splitting_field_aux (f.map (coe : α → adjoin_root (irr_factor f (by rw hf; exact dec_trivial))) /
    (X - C root)) hf'

lemma splitting_field_aux_succ_succ {n : ℕ} {α : Type u} [discrete_field α]
  (f : polynomial α) (hf : nat_degree f = n + 2) :
splitting_field_aux f hf = @splitting_field_aux (n + 1) _ _
  (f.map (coe : α → adjoin_root (irr_factor f (by rw hf; exact dec_trivial))) /
    (X - C root)) sorry := rfl

noncomputable instance splitting_field_aux.discrete_field {n : ℕ} : Π {α : Type u} [discrete_field α]
  (f : by exactI polynomial α) (hf : by exactI nat_degree f = n),
  discrete_field (by exactI splitting_field_aux f hf) :=
nat.cases_on n
  (λ α I f hf, I) -- 0
  (λ n, nat.rec_on n (λ α I f hf, I) -- 1
  (λ n ih α I f hf,
    by exactI ih (f.map (coe : α → adjoin_root (irr_factor f (by rw hf; exact dec_trivial))) /
    (X - C root)) _)) -- n + 2

noncomputable def of_field_aux {n : ℕ} : Π {α : Type u} [discrete_field α] (f : by exactI polynomial α)
  (hf : by exactI nat_degree f = n), α → by exactI splitting_field_aux f hf :=
nat.cases_on n
  (λ α I f hf a, a) -- 0
  (λ n, nat.rec_on n (λ α I f hf a, a) -- 1
  (λ n ih α I f hf a, by exactI ih _ _ (↑a : adjoin_root _))) -- n + 2

lemma of_field_aux_succ_succ {n : ℕ} {α : Type u} [discrete_field α] (f : polynomial α)
  (hf : nat_degree f = n + 2) :
of_field_aux f hf = (λ a : α, (of_field_aux (f.map (coe : α → adjoin_root (irr_factor f
  (by rw hf; exact dec_trivial))) / (X - C root)) _ (↑a : adjoin_root _) :
  @splitting_field_aux (n + 1) _ _
  (f.map (coe : α → adjoin_root (irr_factor f (by rw hf; exact dec_trivial))) /
    (X - C root)) sorry)) := rfl

lemma of_field_aux_inj {n : ℕ} : Π {α : Type u} [discrete_field α] (f : by exactI polynomial α)
  (hf : by exactI nat_degree f = n), function.injective (by exactI of_field_aux f hf) :=
nat.cases_on n
  (λ α I f hf a b, id)
  (λ n, nat.rec_on n (λ α I f hf a b, id)
  (λ n ih α I f hf, function.injective_comp (by exactI ih _ _) (by exactI adjoin_root.coe_injective)))

instance of_field_aux.is_ring_hom {n : ℕ} : Π {α : Type u} [discrete_field α] (f : by exactI polynomial α)
  (hf : by exactI nat_degree f = n), by exactI is_ring_hom (of_field_aux f hf) :=
nat.cases_on n
  (λ α I f hf, by exactI is_ring_hom.id) -- 0
  (λ n, nat.rec_on n (λ α I f hf, by exactI is_ring_hom.id) -- 1
  (λ n ih α I f hf, by exactI @is_ring_hom.comp _ _ _ _ _ adjoin_root.is_ring_hom _ _ _
      (ih (f.map (coe : α → adjoin_root (irr_factor f
        (by rw hf; exact dec_trivial))) / (X - C root)) sorry))) -- n + 2

-- def of_field : Π {α : Type u} [discrete_field α] (f : by exactI polynomial α),
--   α → by exactI splitting_field f
-- | α I f := λ a, by exactI
--   if h1 : degree f ≤ 1 then eq.rec_on (splitting_field_degree_le_one h1).symm a
--   else
--     have wf : degree (f.map (coe : α → adjoin_root (irr_factor f h1)) /
--       (X - C root)) < degree f, from splitting_field_wf_lemma,
--     eq.rec_on (splitting_field_degree_gt_one h1).symm
--       (of_field _ (a : adjoin_root (irr_factor f h1)))
-- using_well_founded {rel_tac := λ _ _, `[exact ⟨_, inv_image.wf
--     (λ x : Σ' (α : Type u) (I : discrete_field α), by exactI polynomial α,
--     by letI := x.2.1; exact x.2.2.degree)
--     (with_bot.well_founded_lt nat.lt_wf)⟩],
--   dec_tac := tactic.assumption}


def splits (f : polynomial α) : Prop := ∀ g : polynomial α, irreducible g → g ∣ f → degree g = 1

lemma splits_of_degree_eq_zero {f : polynomial α} (hf : degree f = 0) : splits f :=
λ g hg ⟨p, hp⟩,
have hp' : degree f = degree (g * p), from congr_arg degree hp,
have degree g = 0, by rw [hf, eq_comm, degree_mul_eq, with_bot.add_eq_zero_iff] at hp';
  exact hp'.1,
sorry

lemma splitting_field_splits {n : ℕ} : Π {α : Type u} [discrete_field α] (f : by exactI polynomial α)
  (hf : by exactI nat_degree f = n), by exactI splits (f.map (of_field_aux f hf)) :=
by exactI nat.cases_on n
  (λ α I f hf , _)
  (λ n, nat.rec_on n (λ α I f hf , _)
    (λ n ih α I f hf, by resetI; exact
      λ (g : polynomial (splitting_field_aux
        (f.map (coe : α → adjoin_root (irr_factor f (by rw hf; exact dec_trivial))) /
          (X - C root)) _)) hgi (hgd : g ∣ _), begin
      dsimp only [of_field_aux_succ_succ] at hgd,
      cases hgd with p hp,


    end))


end splitting_field