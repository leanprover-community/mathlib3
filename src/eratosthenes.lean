import data.nat.prime

namespace list

variables {α β γ : Type*} {R : α → β → γ → Prop}

@[mk_iff]
inductive forall₃ {α β γ : Type*} (R : α → β → γ → Prop) : list α → list β → list γ → Prop
| nil : forall₃ [] [] []
| cons {a b c l₁ l₂ l₃} : R a b c → forall₃ l₁ l₂ l₃ → forall₃ (a::l₁) (b::l₂) (c::l₃)

lemma forall₃_nil : forall₃ R [] [] [] := forall₃.nil
lemma forall₃_cons {a b c} {as bs cs} (h : R a b c) (h' : forall₃ R as bs cs) :
  forall₃ R (a::as) (b::bs) (c::cs) := forall₃.cons h h'

lemma forall₃_cons_iff {a b c} {as bs cs} :
  forall₃ R (a::as) (b::bs) (c::cs) ↔ R a b c ∧ forall₃ R as bs cs :=
begin
  rw [forall₃_iff],
  simp only [and_self, exists_and_distrib_left, false_or, and_assoc],
  split,
  { rintro ⟨_, _, _, r, _, _, _, h, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    exact ⟨r, h⟩ },
  rintro ⟨r, h⟩,
  exact ⟨_, _, _, r, _, _, _, h, rfl, rfl, rfl, rfl, rfl, rfl⟩
end

lemma forall₃_length_1_3 : ∀ {as bs cs}, forall₃ R as bs cs → as.length = cs.length
| [] [] [] forall₃.nil := rfl
| (a::as) (b::bs) (c::cs) (forall₃.cons r h) :=
    by { rw [length, length, add_left_inj], exact forall₃_length_1_3 h }

lemma forall₃_length_2_3 : ∀ {as bs cs}, forall₃ R as bs cs → bs.length = cs.length
| [] [] [] forall₃.nil := rfl
| (a::as) (b::bs) (c::cs) (forall₃.cons r h) :=
    by { rw [length, length, add_left_inj], exact forall₃_length_2_3 h }

lemma forall₂_true :
  ∀ {as : list α} {bs : list β}, forall₂ (λ _ _, true) as bs ↔ as.length = bs.length
| [] [] := by simp
| [] (b::bs) := by simpa using (nat.succ_ne_zero bs.length).symm
| (a::as) [] := by simp
| (a::as) (b::bs) := by simpa using forall₂_true

theorem forall₂.imp_of_mem {R S : α → β → Prop} :
  ∀ {l₁ l₂}, (∀ a b, a ∈ l₁ → b ∈ l₂ → R a b → S a b) → forall₂ R l₁ l₂ → forall₂ S l₁ l₂
| _ _ _ forall₂.nil := forall₂.nil
| (a::as) (b::bs) h (forall₂.cons h₁ h₂) :=
  begin
    refine forall₂.cons (h _ _ (mem_cons_self _ _) (mem_cons_self _ _) h₁) _,
    exact forall₂.imp_of_mem (λ a b ha hb, h a b (mem_cons_of_mem _ ha) (mem_cons_of_mem _ hb)) h₂
  end

lemma forall₃.imp {R S : α → β → γ → Prop} :
  ∀ {l₁ l₂ l₃}, (∀ a b c, R a b c → S a b c) → forall₃ R l₁ l₂ l₃ → forall₃ S l₁ l₂ l₃
| _ _ _ _ forall₃.nil := forall₃.nil
| _ _ _ h (forall₃.cons h' z) := forall₃.cons (h _ _ _ h') (forall₃.imp h z)

lemma forall₃.imp_of_mem {R S : α → β → γ → Prop} :
  ∀ {l₁ l₂ l₃}, (∀ a b c, a ∈ l₁ → b ∈ l₂ → c ∈ l₃ → R a b c → S a b c) → forall₃ R l₁ l₂ l₃ →
    forall₃ S l₁ l₂ l₃
| _ _ _ _ forall₃.nil := forall₃.nil
| _ _ _ h (forall₃.cons h' z) := forall₃.cons (h _ _ _ (mem_cons_self _ _) (mem_cons_self _ _)
  (mem_cons_self _ _) h') (forall₃.imp_of_mem (λ _ _ _ ha hb hc, h _ _ _ (mem_cons_of_mem _ ha)
  (mem_cons_of_mem _ hb) (mem_cons_of_mem _ hc)) z)

end list

def sieve_by (ps ns : list ℕ) : Prop := ns.sorted (≤) → ∀ (p ∈ ps) (n ∈ ns), ¬ p ∣ n

def sieve_by_aux (ps : list (ℕ × ℕ)) (ns : list ℕ) : Prop :=
ns.sorted (≤) → ∀ (ppk : ℕ × ℕ) (n : ℕ), ppk.1 ∣ ppk.2 → ppk.2 ≤ n → ppk ∈ ps → n ∈ ns → ¬ ppk.1 ∣ n

def sieved_by_aux (ps pks ns : list ℕ) : Prop :=
ns.sorted (≤) → ps.length = pks.length →
  list.forall₂ (λ p pk, p ∣ pk → ∀ n ∈ ns, pk ≤ n → ¬ p ∣ n) ps pks

lemma sieve_by_of' {ps ns : list ℕ} (h : sieved_by_aux ps ps ns) (h' : ∀ n ∈ ns, 0 < n) :
  sieve_by ps ns :=
λ hns p hp n hn hpn,
  list.forall₂_same.1 (h hns rfl) _ hp dvd_rfl _ hn (nat.le_of_dvd (h' _ hn) hpn) hpn

lemma sieve_by_of {ps ns : list ℕ} {n : ℕ} (h' : 0 < n) (h : sieved_by_aux ps ps (n :: ns)) :
  sieve_by ps (n :: ns) :=
begin
  intros h'',
  refine sieve_by_of' h _ h'',
  simp only [list.mem_cons_iff, forall_eq_or_imp],
  exact ⟨h', λ a ha, h'.trans_le (list.rel_of_sorted_cons h'' a ha)⟩,
end

open list

lemma sieved_by_aux_increment' :
  ∀ (ps pks pks' pks'' ks ns : list ℕ),
    forall₃ (λ p k r, p * k = r) ps ks pks' →
    forall₃ (λ x y z, x + y = z) pks pks' pks'' →
    forall₃ (λ p k new, k = 0 ∨ ∀ n ∈ ns, new < n + p) ps ks pks'' →
    sieved_by_aux ps pks'' ns →
    sieved_by_aux ps pks ns
| _ _ _ _ _ _ forall₃.nil forall₃.nil forall₃.nil h hn _ := forall₂.nil
| (p::ps) (pk::pks) (_::pks') (_::pks'') (k::ks) ns
    (forall₃.cons rfl h₁) (forall₃.cons rfl h₂) (forall₃.cons h₃ h₄) h₅ h₆ h₇ :=
  begin
    simp only [length, add_left_inj] at h₇,
    have h₈ : ps.length = pks''.length := forall₃_length_1_3 h₄,
    have h₉ := h₅ h₆ (by simpa using h₈),
    rw forall₂_cons at h₉,
    obtain ⟨h₉, h₁₀⟩ := h₉,
    rw forall₂_cons,
    refine ⟨_, sieved_by_aux_increment' ps pks pks' pks'' ks ns h₁ h₂ h₄ (λ _ _, h₁₀) h₆ h₇⟩,
    clear_dependent ps ks pks pks' pks'',
    rintro ⟨r, rfl⟩ n hn hprn,
    rw ←mul_add at h₃ h₉,
    specialize h₉ (dvd_mul_right _ _) n hn,
    rcases h₃ with rfl | h₃,
    { exact h₉ hprn },
    specialize h₃ _ hn,
    rintro ⟨l, rfl⟩,
    apply h₉ _ (dvd_mul_right _ _),
    rw ←mul_add_one at h₃,
    refine mul_le_mul_left' _ _,
    rw ←nat.lt_add_one_iff,
    exact _root_.lt_of_mul_lt_mul_left' h₃,
  end

lemma sieved_by_aux_increment {ps pks ns : list ℕ} (ks pks' pks'' : list ℕ) (n : ℕ)
  (h₁ : forall₃ (λ p k r, p * k = r) ps ks pks')
  (h₂ : forall₃ (λ x y z, x + y = z) pks pks' pks'')
  (h₃ : forall₃ (λ p k new, k = 0 ∨ new < n + p) ps ks pks'')
  (h : sieved_by_aux ps pks'' (n :: ns)) :
  sieved_by_aux ps pks (n :: ns) :=
begin
  intros hns t,
  refine sieved_by_aux_increment' ps pks pks' pks'' ks (n :: ns) h₁ h₂ (h₃.imp _) h hns t,
  intros p k pk,
  rintro (rfl | u),
  exact or.inl rfl,
  simp only [mem_cons_iff, forall_eq_or_imp],
  refine or.inr ⟨u, λ m hm, _⟩,
  simp only [sorted_cons] at hns,
  exact u.trans_le (add_le_add_right (hns.1 _ hm) _),
end

lemma sieved_by_aux_scrap {ps pks ns : list ℕ} {n : ℕ}
  (h' : pks.all₂ ((<) n))
  (h : sieved_by_aux ps pks ns) :
  sieved_by_aux ps pks (n :: ns) :=
begin
  rw list.all₂_iff_forall at h',
  intros h₂ h₃,
  refine (h h₂.of_cons h₃).imp_of_mem _,
  simp only [mem_cons_iff, forall_eq_or_imp],
  simp only [←not_le] at h',
  tauto
end

lemma sieved_by_aux_empty (ps pks : list ℕ) : sieved_by_aux ps pks [] :=
by { rw [sieved_by_aux], simp [forall₂_true] }

lemma ineq_helper (new n p : ℕ) (np : ℕ) (hnp : n + p = np) (hnew : new < np) : new < n + p :=
by rwa hnp

lemma all₂_nil (n : ℕ) : list.all₂ ((<) n) [] := trivial
lemma all₂_singleton (n m : ℕ) (h : n < m) : list.all₂ ((<) n) [m] := h
lemma all₂_cons (n m : ℕ) {ms : list ℕ} (h : n < m) (h' : list.all₂ ((<) n) ms) :
  list.all₂ ((<) n) (m :: ms) :=
begin
  cases ms,
  { exact h },
  exact ⟨h, h'⟩,
end

def difference (n p pk : ℕ) : ℕ :=
if pk ≤ n
  then (n - pk) / p + 1
  else 0

def mul_eq (a b c : ℕ) : Prop := a * b = c
def add_eq (a b c : ℕ) : Prop := a + b = c
def thingy_eq (n : ℕ) (a b c : ℕ) : Prop := b = 0 ∨ c < n + a

section

namespace tactic

meta def prove_forall₃_mul_eq : instance_cache → expr → tactic (instance_cache × expr)
| ic `(list.forall₃ %%a list.nil list.nil list.nil) := return (ic, `(@list.forall₃_nil ℕ ℕ ℕ %%a))
| ic `(list.forall₃ %%r (list.cons %%b %%bs) (list.cons %%c %%cs) (list.cons %%d %%ds)) := do
    (ic, _, hd) ← norm_num.prove_mul_nat ic b c,
    (ic, next_proof) ← prove_forall₃_mul_eq ic `(@list.forall₃ ℕ ℕ ℕ %%r %%bs %%cs %%ds),
    all ← mk_app ``list.forall₃_cons [hd, next_proof],
    return (ic, all)
| _ _ := fail "prove_forall₃_mul_eq bad form"

meta def prove_forall₃_add_eq : instance_cache → expr → tactic (instance_cache × expr)
| ic `(list.forall₃ %%a list.nil list.nil list.nil) := return (ic, `(@list.forall₃_nil ℕ ℕ ℕ %%a))
| ic `(list.forall₃ %%r (list.cons %%b %%bs) (list.cons %%c %%cs) (list.cons %%d %%ds)) := do
    (ic, hd) ← norm_num.prove_add_nat ic b c d,
    (ic, next_proof) ← prove_forall₃_add_eq ic `(@list.forall₃ ℕ ℕ ℕ %%r %%bs %%cs %%ds),
    all ← mk_app ``list.forall₃_cons [hd, next_proof],
    return (ic, all)
| _ _ := fail "bad form"

meta def prove_forall₃_thingy_eq (n : expr) : instance_cache → expr → tactic (instance_cache × expr)
| ic `(list.forall₃ %%a list.nil list.nil list.nil) := return (ic, `(@list.forall₃_nil ℕ ℕ ℕ %%a))
| ic `(list.forall₃ %%r (list.cons %%p %%ps) (list.cons %%k %%ks) (list.cons %%new %%news)) := do
    ik ← k.to_nat,
    this_one ←
      (if ik = 0
        then do
              j ← mk_eq_refl `(0),
              mk_app `or.inl [`((%%new : ℕ) < %%n + %%p), j]
        else do
             (ic, np, hnp) ← norm_num.prove_add_nat' ic n p,
             (ic, hn) ← norm_num.prove_lt_nat ic new np,
             return `(@or.inr (%%k = 0) _ (ineq_helper %%new %%n %%p %%np %%hnp %%hn))),
    (ic, next_proof) ← prove_forall₃_thingy_eq ic `(@list.forall₃ ℕ ℕ ℕ %%r %%ps %%ks %%news),
    all ← mk_app `list.forall₃_cons [this_one, next_proof],
    return (ic, all)
| _ _ := fail "bad form"

meta def prove_all₂ (n : expr) : instance_cache → expr → tactic (instance_cache × expr)
| ic `(list.all₂ _ []) := return (ic, `(all₂_nil %%n))
| ic `(list.all₂ %%p (%%m :: %%ms)) := do
    (ic, h) ← norm_num.prove_lt_nat ic n m,
    (ic, r) ← prove_all₂ ic `(@list.all₂ ℕ %%p %%ms),
    return (ic, `(@_root_.all₂_cons %%n %%m %%ms %%h %%r))
| _ _ := fail "prove_all₂ bad form"

meta def interactive.scrap : command :=
do
  `(sieved_by_aux %%ps %%pks (list.cons %%n %%ns)) ← target,
  nc ← mk_instance_cache `(ℕ),
  (_, h) ← prove_all₂ n nc `(@list.all₂ ℕ ((<) %%n) %%pks),
  refine ``(sieved_by_aux_scrap %%h _)

meta def interactive.increment' (iks : list ℕ) : command :=
do
  `(sieved_by_aux %%ps %%pks (list.cons %%n %%ns)) ← target,
  ips ← ps.to_list expr.to_nat,
  ipks ← pks.to_list expr.to_nat,
  n' ← n.to_nat,
  let ipks' := zip_with (*) ips iks,
  let ipks'' := zip_with (+) ipks ipks',
  let ks := reflect iks,
  let pks' := reflect ipks',
  let pks'' := reflect ipks'',
  nc ← mk_instance_cache `(ℕ),
  (nc, pf1) ← prove_forall₃_mul_eq nc `(list.forall₃ mul_eq %%ps %%ks %%pks'),
  (nc, pf2) ← prove_forall₃_add_eq nc `(list.forall₃ add_eq %%pks %%pks' %%pks''),
  (nc, pf3) ← prove_forall₃_thingy_eq n nc `(list.forall₃ (thingy_eq %%n) %%ps %%ks %%pks''),
  refine ``(sieved_by_aux_increment %%ks %%pks' %%pks'' _ %%pf1 %%pf2 %%pf3 _)

meta def interactive.increment (iks : list ℕ) : command :=
interactive.increment' iks >> (interactive.scrap <|> fail "couldn't remove")

meta def interactive.end_sieve : command :=
do
  `(sieved_by_aux %%ps %%pks list.nil) ← target,
  exact `(sieved_by_aux_empty %%ps %%pks)

meta def interactive.start_sieve : command :=
do
  `(sieve_by %%ps (%%n :: %%ns)) ← target,
  ic ← mk_instance_cache `(ℕ),
  (ic, hn) ← norm_num.prove_pos_nat ic n,
  refine ``(sieve_by_of %%hn _)

meta def interactive.step : command :=
do
  `(sieved_by_aux %%ps %%pks (%%n :: _)) ← target,
  ips ← ps.to_list expr.to_nat,
  ipks ← pks.to_list expr.to_nat,
  n' ← n.to_nat,
  interactive.increment (zip_with (difference n') ips ipks)

meta def interactive.run_sieve : command :=
do
  `(sieve_by %%ps %%ns) ← target,
  ins ← ns.to_list expr.to_nat,
  interactive.start_sieve,
  iterate_exactly' ins.length interactive.step,
  interactive.end_sieve

end tactic

end

lemma sieve_47 : sieve_by [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 47]
  [1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801,
   1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933,
   1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063,
   2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179,
   2203, 2207] :=
begin
  run_sieve
end
