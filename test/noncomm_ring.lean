import tactic.noncomm_ring

local notation `⁅`a`,` b`⁆` := a * b - b * a
local infix ` ⚬ `:65 := λ a b, a * b + b * a

variables {R : Type*} [ring R]
variables (a b c : R)

example : (a + b) * c = a * c + b * c := by noncomm_ring
example : a * (b + c) = a * b + a * c := by noncomm_ring
example : a - b = a + -b := by noncomm_ring
example : a * b * c = a * (b * c) := by noncomm_ring
example : a + a = a * 2 := by noncomm_ring
example : a + a = 2 * a := by noncomm_ring
example : a ^ 2 = a * a := by noncomm_ring
example : (-a) * b = -(a * b) := by noncomm_ring
example : a * (-b) = -(a * b) := by noncomm_ring
example : a * (b + c + c - b) = 2*a*c := by noncomm_ring
example : ⁅a, a⁆ = 0 := by noncomm_ring
example : ⁅a, b⁆ = -⁅b, a⁆ := by noncomm_ring
example : ⁅a + b, c⁆ = ⁅a, c⁆ + ⁅b, c⁆ := by noncomm_ring
example : ⁅a, b + c⁆ = ⁅a, b⁆ + ⁅a, c⁆ := by noncomm_ring
example : ⁅a, ⁅b, c⁆⁆ + ⁅b, ⁅c, a⁆⁆ + ⁅c, ⁅a, b⁆⁆ = 0 := by noncomm_ring
example : ⁅⁅a, b⁆, c⁆ + ⁅⁅b, c⁆, a⁆ + ⁅⁅c, a⁆, b⁆ = 0 := by noncomm_ring
example : ⁅a, ⁅b, c⁆⁆ = ⁅⁅a, b⁆, c⁆ + ⁅b, ⁅a, c⁆⁆ := by noncomm_ring
example : ⁅⁅a, b⁆, c⁆ = ⁅⁅a, c⁆, b⁆ + ⁅a, ⁅b, c⁆⁆ := by noncomm_ring
example : ⁅a * b, c⁆ = a * ⁅b, c⁆ + ⁅a, c⁆ * b := by noncomm_ring
example : ⁅a, b * c⁆ = ⁅a, b⁆ * c + b * ⁅a, c⁆ := by noncomm_ring
example : ⁅2 * a, a⁆ = 0 := by noncomm_ring
example : ⁅a * 2, a⁆ = 0 := by noncomm_ring
example : ⁅a^2, a⁆ = 0 := by noncomm_ring
example : a ⚬ a = 2*a^2 := by noncomm_ring
example : a ⚬ b = b ⚬ a := by noncomm_ring
example : a ⚬ (b + c) = a ⚬ b + (a ⚬ c) := by noncomm_ring
example : (a + b) ⚬ c = a ⚬ c + (b ⚬ c) := by noncomm_ring
example : (a ⚬ b) ⚬ (a ⚬ a) = a ⚬ (b ⚬ (a ⚬ a)) := by noncomm_ring
