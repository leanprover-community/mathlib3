/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek
-/

import tactic.vampire

section

/- Examples from finish. -/

variables {A B C D : Prop}

example : (A → B ∨ C) → (B → D) → (C → D) → A → D :=
by vampire "n100hn1hn100hn10hn0hn11hrn1trrrr"

example : ¬ A → A → C :=
by vampire "n0hn1hr"

example : (A ∧ A ∧ B) → (A ∧ C ∧ B) → A :=
by vampire "n110hn0hr"

example : A → ¬ B → ¬ (A → B) :=
by vampire "n1hn10hn1trn0hr"

example : A ∨ B → B ∨ A :=
by vampire "n10hn1hn0hn1trr"

example : A ∧ B → B ∧ A :=
by vampire "n10hn1tn0hrn1hr"

example : A → (A → B) → (B → C) → C :=
by vampire "n11hn10hn1hn0hrrr"

example : (A ∧ B) → (C ∧ B) → C :=
by vampire "n100hn10hr"

example : A → B → C → D → (A ∧ B) ∧ (C ∧ D) :=
by vampire "n100hn11tn11hrn10tn10hrn1tn1hrn0hr"

example : (A ∧ B) → (B ∧ ¬ C) → A ∨ C :=
by vampire "n100hn0hr"

example : (A → B) ∧ (B → C) → A → C :=
by vampire "n11hn1hn0hn10hrrr"

example : (A → B) ∨ (B → A) :=
by vampire "n1hn10hr"

example : ((A → B) → A) → A :=
by vampire "n10hn0hn1tcr"

example : A → ¬ B → ¬ (A → B) :=
by vampire "n1hn10hn1trn0hr"

example : ¬ (A ↔ ¬ A) :=
by vampire "n0hn1tcn1hn1tcr"

example : (A ↔ B) → (A ∧ B → C) → (¬ A ∧ ¬ B → C) → C :=
by vampire "n100hn10hn1hrn10tcn0hn11hrn1tcrn1tcr"

example : (A ↔ B) → ((A ∧ ¬ B) ∨ (¬ A ∧ B)) → C :=
by vampire "n100hn0hn11hrn1tcrn1hn1tn0hn11hrn1tcrr"

example : (A → B) → A → B :=
by vampire "n10hn0hn1hrr"

example : (A → B) → (B → C) → A → C :=
by vampire "n11hn1hn0hn10hrrr"

example : (A → B ∨ C) → (B → D) → (C → D) → A → D :=
by vampire "n100hn1hn100hn10hn0hn11hrn1trrrr"

example : A ∨ B → B ∨ A :=
by vampire "n10hn1hn0hn1trr"

variables (α : Type) [inhabited α]
variables (a b c : α) (p q : α → Prop) (r : α → α → Prop)
variables (P Q R : Prop)
variable  (g : bool → nat)

example : (∀ x, p x → q x) → (∀ x, p x) → q a :=
by vampire
"
n10hen0n10ymsn0hen10n0mn1n0msen10n0msn1hen10n1mn0n1msen10n0m
n1n0msren1n0mn0n0msen0n10ymsr
"

example : (p a) → ∃ x, p x :=
by vampire "n1hen1n0mn0n0msen0n1ymsn0hen0n1ymsr"

example : (p a) → (p b) → (q b) → ∃ x, p x ∧ q x :=
by vampire "n11hen1n0mn0n0msn1ten0n10ymsn10hen0n10ymsrn1hr"

example : (∃ x, p x ∧ r x x) → (∀ x, r x x → q x) → ∃ x, p x ∧ q x :=
by vampire
"
n11hen10n1mn0n1msn1ten1n0ymsn10hen10n0mn1n0msen0n0ymsn1hen0n
0ymsren1n0ymsrn0hr
"

example : (∃ x, q x ∧ p x) → ∃ x, p x ∧ q x :=
by vampire "n10hen1n0mn0n0msen0n0ymsn1hen0n0ymsrn0hr"

example : (∀ x, q x → p x) → (q a) → ∃ x, p x :=
by vampire
"
n10hen10n1mn0n1msen1n10ymsn0hen10n0mn1n0msen0n10ymsn1hen0n10
ymsren1n10ymsr
"

example : (∀ x, p x → q x → false) → (p a) → (p b) → (q b) → false :=
by vampire "n0hen1n0mn0n0msn1ten0n11ymsn11hen0n11ymsrn10hr"

example : (∀ x, p x) → (∀ x, p x → q x) → ∀ x, q x :=
by vampire
"
n10hen1n0ymsn1hen10n1mn0n1msen10n1msn0hen10n0mn1n0msen10n1mn
0n1msren11n1mn1n1msen1n0ymsr
"

example : (∃ x, p x) → (∀ x, p x → q x) → ∃ x, q x :=
by vampire
"
n10hen10n1mn0n1msen1n0ymsn1hen10n0mn1n0msen0n0ymsn0hen0n0yms
ren1n0ymsr
"

example : (¬ ∀ x, ¬ p x) → (∀ x, p x → q x) → (∀ x, ¬ q x) → false :=
by vampire
"
n10hen10n1mn0n1msen1n0ymsn1hen10n0mn1n0msen0n0ymsn0hen0n0yms
ren1n0ymsr
"

example : (p a) → (p a → false) → false :=
by vampire "n1hn0hr"

example : (¬ (P → Q ∨ R)) → (¬ (Q ∨ ¬ R)) → false :=
by vampire "n10hn100hr"

example : (P → Q ∨ R) → (¬ Q) → P → R :=
by vampire "n11hn1hn0hn10hrrr"

example : (∃ x, p x → P) ↔ (∀ x, p x) → P :=
by vampire
"
n111hn1tcn10hn1tn11tcn10ten0n0ymsn0hen1n0mn0n0msn10ten0n0yms
rn1tn10tcn1tn10tcn1ten1n1ymsn100hen11n1mn1n1msn1tn101hen11n1
mn1n1msn1ten10n0ymsn11hen10n1mn11n0mn0n1mn1n0msen10n0ymn1n11
mn0n0ymsren101n1mn11n1mn1n1msn10tcn1ten1n11msren101n1mn11n1m
n1n1msn1tcen1n1ymsrr
"

example : (∃ x, P → p x) ↔ (P → ∃ x, p x) :=
by vampire
"
n111hen10n1mn11n0mn0n1mn1n0msen0n0ymsn1000hen11n1mn1n1msn1tn
11hn1tcren11n1mn1n1msn1ten0n0ymn1n11msren101n1mn11n1mn1n1msn
1tcen1n1ymsn1hen1n0mn0n0msn10ten0n0ymsn10hn10tcn10ten0n0ymsr
n1tn11tcn1tn10tcn1ten1n1ymsrn11hn1tcr
"

end

section

  /- Some harder examples, from John Harrison's
     Handbook of Practical Logic and Automated Reasoning. -/

variables (α : Type) [inhabited α]

lemma gilmore_1 {F G H : α → Prop} :
  ∃ x, ∀ y z,
      ((F y → G y) ↔ F x) ∧
      ((F y → H y) ↔ G x) ∧
      (((F y → G y) → H y) ↔ H x)
      → F z ∧ G z ∧ H z :=
by vampire
"
n1010hen1n0mn0n0msn10ten11n0yn0vmsn111hen1n0mn0n0msen11n0msn
111hen1n0mn0n0msen10n0msn101hen1n0mn0n0msen1n0msn111hen1n0mn
0n0msen10n1yn0vmsn1hen1n0mn0n0msen10n0msn110hen1n0mn0n0msen1
n0msn0hen1n0mn0n0msen1n0mn0n0msren10n1mn0n1msen10n0mn1n0msre
n10n1mn0n1msn10tcn1ten10n1yn0vmn1n1yn0vmsren1n0mn0n0msn1ten1
n0mn0n0msren10n1mn0n1msen10n0mn1n0msren10n1mn0n1msn10tcn1ten
100n1msn111hen1n0mn0n0msen10n0msn101hen1n0mn0n0msen1n0msn111
hen1n0mn0n0msen10n1yn0vmsn1hen1n0mn0n0msen10n0msn110hen1n0mn
0n0msen1n0msn0hen1n0mn0n0msen1n0mn0n0msren10n1mn0n1msen10n0m
n1n0msren10n1mn0n1msn10tcn1ten10n1yn0vmn1n1yn0vmsren1n0mn0n0
msn1ten1n0mn0n0msren10n1mn0n1msen10n0mn1n0msren10n1mn0n1msn1
0tcn1ten1n1yn10vmsn110hen1n0mn0n0msen1n0msn11hen1n0mn0n0msen
1n0mn0n0msren1n0mn0n0msen1n1yn10vmn0n10msren101n10mn10n10msn
10ten100n1mn10n1msren100n10mn1n10msn10tcn1ten11n0mn10n0msren
11n10mn0n10msn1tcen11n0yn0vmn10n0yn0vmsren11n10mn0n10msn1ten
100n0yn10vmsn100hen1n0mn0n0msen11n1yn0vmsn111hen1n0mn0n0msen
11n0msn111hen1n0mn0n0msen10n0msn101hen1n0mn0n0msen1n0msn111h
en1n0mn0n0msen10n1yn0vmsn1hen1n0mn0n0msen10n0msn110hen1n0mn0
n0msen1n0msn0hen1n0mn0n0msen1n0mn0n0msren10n1mn0n1msen10n0mn
1n0msren10n1mn0n1msn10tcn1ten10n1yn0vmn1n1yn0vmsren1n0mn0n0m
sn1ten1n0mn0n0msren10n1mn0n1msen10n0mn1n0msren10n1mn0n1msn10
tcn1ten100n1msn111hen1n0mn0n0msen10n0msn101hen1n0mn0n0msen1n
0msn111hen1n0mn0n0msen10n1yn0vmsn1hen1n0mn0n0msen10n0msn110h
en1n0mn0n0msen1n0msn0hen1n0mn0n0msen1n0mn0n0msren10n1mn0n1ms
en10n0mn1n0msren10n1mn0n1msn10tcn1ten10n1yn0vmn1n1yn0vmsren1
n0mn0n0msn1ten1n0mn0n0msren10n1mn0n1msen10n0mn1n0msren10n1mn
0n1msn10tcn1ten1n1yn10vmsn110hen1n0mn0n0msen1n0msn11hen1n0mn
0n0msen1n0mn0n0msren1n0mn0n0msen1n1yn10vmn0n10msren101n10mn1
0n10msn10ten100n1mn10n1msren100n10mn1n10msn10tcn1ten11n0mn10
n0msren11n10mn0n10msn1tcen11n1yn0vmn10n1yn0vmsren10n1mn0n1ms
en100n0yn10vmn1n0yn10vmsren101n10mn10n10msen101n0yn10vmsn1he
n1n0mn0n0msen11n0msn100hen1n0mn0n0msen1n0msn111hen1n0mn0n0ms
en10n0msn101hen1n0mn0n0msen1n0msn111hen1n0mn0n0msen10n1yn0vm
sn1hen1n0mn0n0msen10n0msn110hen1n0mn0n0msen1n0msn0hen1n0mn0n
0msen1n0mn0n0msren10n1mn0n1msen10n0mn1n0msren10n1mn0n1msn10t
cn1ten10n1yn0vmn1n1yn0vmsren1n0mn0n0msn1ten1n0mn0n0msren10n1
mn0n1msen10n0mn1n0msren10n1mn0n1msn10tcn1ten1n1yn10vmsn10hen
1n0mn0n0msen1n0msn11hen1n0mn0n0msen1n0mn0n0msren1n0mn0n0msen
1n1yn10vmn0n10msren11n0mn10n0msen1n0mn0n0msren1n0mn0n0msn10t
cn1ten0n1yn1vmsn0hen1n0mn0n0msen0n1msren100n10mn1n10msen11n0
mn10n0msren11n10mn0n10msn1tcen101n0yn10vmn10n0yn10vmsr
"

lemma gilmore_6 {F G : α → α → Prop} {H : α → α → α → Prop} :
∀ x, ∃ y,
  (∃ u, ∀ v, F u x → G v u ∧ G u x)
   → (∃ u, ∀ v, F u y → G v u ∧ G u y) ∨
       (∀ u v, ∃ w, G v u ∨ H w y u → G u w) :=
by vampire
"
n101hen100n11mn111n0mn11n0mn0n11msen100n1yn0vmn11n11yn101vms
n0hen101n0mn100n1mn11n0mn10n1msen100n11yn0vmn10n100ymsn10hen
110n0mn100n10mn1n10mn11n0msen100n11yn0vmn10n11yn0vmn0n100yms
ren10n1mn11n0mn0n1mn1n0msen100n1yn0vmn11n11yn101vmn1n101mn0n
1yn0vmsr
"

lemma gilmore_8 {G : α → Prop} {F : α → α → Prop} {H : α → α → α → Prop} :
  ∃ x, ∀ y z,
    ((F y z → (G y → (∀ u, ∃ v, H u v x))) → F x x) ∧
    ((F z x → G x) → (∀ u, ∃ v, H u v z)) ∧
    F x y → F z z :=
by vampire
"
n110hen11n0mn10n0msen1n0mn0n0msn10hen100n0mn11n1mn10n0mn1n1m
sen100n1yn10yn10vamn1n0yn10vn1yn10yn10vaamn0n10yn10vmsn100he
n101n0mn11n10mn10n0mn0n10msn1ten100n1yn10yn10vamn1n0yn10vn1y
n10yn10vaamn0n10mn10n1yn10yn10vamsren11n0mn10n0msen1n0mn0n0m
sren1n0mn0n0msen0n11yn10yn1vamsn110hen11n0mn10n0msen0n0mn1n1
0yn0vmsn1hen11n0mn10n0msn1ten1n10yn0vmn0n10yn0vmsren1n0mn0n0
msen0n1msr
"

lemma manthe_and_bry (agatha butler charles : α)
(lives : α → Prop) (killed hates richer : α → α → Prop) :
   lives agatha ∧ lives butler ∧ lives charles ∧
   (killed agatha agatha ∨ killed butler agatha ∨
    killed charles agatha) ∧
   (∀ x y, killed x y → hates x y ∧ ¬ richer x y) ∧
   (∀ x, hates agatha x → ¬ hates charles x) ∧
   (hates agatha agatha ∧ hates agatha charles) ∧
   (∀ x, lives(x) ∧ ¬ richer x agatha → hates butler x) ∧
   (∀ x, hates agatha x → hates butler x) ∧
   (∀ x, ¬ hates x agatha ∨ ¬ hates x butler ∨ ¬ hates x charles)
   → killed agatha agatha ∧
       ¬ killed butler agatha ∧
       ¬ killed charles agatha :=
by vampire
"
n1011hen110n101mn0n101msn10ten101n10ymsn1010hen110n100mn1n10
0msen100n11ymsn1000hen100n11ymsren101n10ymsrn1010hen110n100m
n1n100msen100n1ymsn111hen100n1ymsrrn101hen110n1mn111n0mn101n
0mn100n1msn1ten101n0mn1n1ymsn1001hen110n11mn10n11msn1ten101n
0mn1n1ymn11n0msren1n0mn0n0msen0n10ymsn110hen110n10mn11n10msn
1ten10n1ymsn100hen110n1mn111n0mn101n0mn100n1msen0n11ymn1n1ym
sn1100hn11hrn1tn11tcn1tn10tcn1ten0n11ymn1n1ymsren10n1ymsrn11
1hren0n10ymsrn1hrr
"

end
