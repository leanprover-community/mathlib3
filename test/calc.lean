import analysis.asymptotics.asymptotic_equivalent

variables {α β γ δ : Type*}

section is_equivalent

open_locale asymptotics

#check @asymptotics.is_equivalent.trans

example {l : filter α} {u v w : α → β} [normed_group β]
  (huv : u ~[l] v) (hvw : v ~[l] w) : u ~[l] w :=
calc u ~[l] v : huv
   ... ~[l] w : hvw

end is_equivalent
