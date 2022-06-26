-- Do we have this stuff?
import data.fin.basic
import tactic

namespace fin

/-- The function dsending enoted `δᵖ` by Riehl-Verity, sending`t` to `t` if `t<p` and
  `t.succ` otherwise.`-/
def delta {i j : ℕ} (hj : j = i + 1) (p : ℕ) (t : fin i) : fin j :=
-- fin.succ_above expects p : fin i.succ for some reason
⟨if (t : ℕ) < p then t else (t : ℕ).succ, begin
  subst hj,
  cases t with t ht,
  split_ifs,
  { exact ht.trans (nat.lt_succ_self _) },
  { exact nat.succ_lt_succ ht },
end⟩

lemma delta_eval {i j : ℕ} (hj : j = i + 1) (p : ℕ) (t : fin i) :
  (delta hj p t : ℕ) = if (t : ℕ) < p then t else (t : ℕ).succ := rfl

theorem delta_comm_apply  {i j k : ℕ} (hj : j = i.succ) (hk : k = j.succ) {p q : ℕ}
  (hpq : p ≤ q) (t : fin i) : delta hk q.succ (delta hj p t) = delta hk p (delta hj q t) :=
begin
  subst hk,
  subst hj,
  ext,
  cases t with t ht,
  simp only [delta_eval],
  dsimp,
  split_ifs;
  try {rw nat.succ_eq_add_one at *};
  try {push_neg at *};
  try {rw nat.succ_eq_add_one at *};
  try {linarith},
end

lemma delta_comm {i j k : ℕ} (hj : j = i.succ) (hk : k = j.succ) {p q : ℕ}
  (hpq : p ≤ q) : delta hk q.succ ∘ delta hj p = delta hk p ∘ delta hj q :=
by ext1; exact delta_comm_apply hj hk hpq _

theorem delta_comm_apply.symm {i j k : ℕ} (hj : j = i.succ) (hk : k = j.succ) {p q_succ : ℕ}
  (hpq : q_succ ≤ p) (t : fin i) :
  delta hk p.succ (delta hj q_succ t) = delta hk q_succ (delta hj p t) :=
delta_comm_apply hj hk hpq t

@[simp] lemma delta_zero_apply {i j : ℕ} (hj : j = i + 1) (t : fin i) :
  delta hj 0 t = fin.cast hj.symm t.succ :=
begin
  unfold delta,
  ext,
  dsimp,
  rw [if_neg (nat.not_lt_zero _), coe_succ],
end

@[simp] lemma delta_self_apply {i j : ℕ} (hj : j = i + 1) (t : fin i) :
  delta hj i t = fin.cast hj.symm t.cast_succ :=
begin
  unfold delta,
  ext,
  dsimp,
  erw if_pos t.2,
end

end fin
