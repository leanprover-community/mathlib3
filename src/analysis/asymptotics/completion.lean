import analysis.asymptotics.theta
import analysis.normed.group.completion

/-!
-/

variables {α E F : Type*} [has_norm E] [seminormed_add_comm_group F]
  {f : α → E} {g : α → F} {l : filter α}

local postfix `̂`:100 := uniform_space.completion

open uniform_space.completion

namespace asymptotics

@[simp, norm_cast] lemma is_O_completion_left : (λ x, g x : α → F̂) =O[l] f ↔ g =O[l] f :=
by simp only [is_O_iff, norm_coe]

@[simp, norm_cast] lemma is_O_completion_right : f =O[l] (λ x, g x : α → F̂) ↔ f =O[l] g :=
by simp only [is_O_iff, norm_coe]

@[simp, norm_cast] lemma is_Theta_completion_left : (λ x, g x : α → F̂) =Θ[l] f ↔ g =Θ[l] f :=
and_congr is_O_completion_left is_O_completion_right

@[simp, norm_cast] lemma is_Theta_completion_right : f =Θ[l] (λ x, g x : α → F̂) ↔ f =Θ[l] g :=
and_congr is_O_completion_right is_O_completion_left

@[simp, norm_cast] lemma is_o_completion_left : (λ x, g x : α → F̂) =o[l] f ↔ g =o[l] f :=
by simp only [is_o_iff, norm_coe]

@[simp, norm_cast] lemma is_o_completion_right : f =o[l] (λ x, g x : α → F̂) ↔ f =o[l] g :=
by simp only [is_o_iff, norm_coe]

end asymptotics
