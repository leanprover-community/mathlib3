import analysis.complex.roots_of_unity
import data.rat.order
import data.padics.padic_integers
import data.nat.totient

def is_dir_character ( to_fun : ℤ →* ℂ ) :=
 ∃ n : ℤ, ∀ i : ℤ, to_fun (i + n) = to_fun i ∧ to_fun i = 0 ↔ euclidean_domain.gcd i n > 1

namespace dir_character

def dir_char := {f : ℤ →* ℂ // is_dir_character f}

instance : has_coe (dir_char) (ℤ →* ℂ) := ⟨λ f, f.val⟩

variables {p : ℕ} [fact p.prime] (f : dir_char) (a F : ℕ)

instance : has_Inf ℤ := by apply_instance

def conductor : ℤ := Inf { n | ∀ i : ℤ, f (i + n) = f i }

lemma add : ∃ n : ℤ, ∀ i : ℤ, f (i + n) = f i ∧ f i = 0 ↔ euclidean_domain.gcd i n > 1 :=
f.2

noncomputable theory
def chi (χ : dir_char) (s : ℂ) : ℕ → ℂ := λ n, (χ(n) / (n^s))

def L_function_char : ℂ → ℂ := λ s, ∑' n, (chi f s) n

def mod_function (ha : 0 < a ∧ a < F) (s : ℂ) : ℕ → ℂ := λ n, (1/(a + n * F)^s)

def H_function_char (ha : 0 < a ∧ a < F) : ℂ → ℂ := λ s, ∑' n, (mod_function a F ha s) n

lemma totient_positive : 0 < nat.totient p := sorry

--lemma exists_root (hp : is_unit (a : ℤ_[p]) ) (hp' : p ≠ 2) : ∃ ! ( ω : roots_of_unity (nat.to_pnat (nat.totient p) (totient_positive)) ℤ_[p] ), (p : ℤ_[p]) | ((a : ℤ_[p]) - ω) :=

lemma exists_root (hp : is_unit (a : ℤ_[p]) ) (hp' : p ≠ 2) : ∃ ω : ℤ_[p], 1 ≤ padic_int.valuation ((a - ω) : ℤ_[p]) :=

end dir_character
