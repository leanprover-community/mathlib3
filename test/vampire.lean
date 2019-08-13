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
by vampire "n100ean1ean100ean10ean1n0ean11eartrrrr"

example : ¬ A → A → C :=
by vampire "n0ean1ear"

example : (A ∧ A ∧ B) → (A ∧ C ∧ B) → A :=
by vampire "n110ean0ear"

example : A → ¬ B → ¬ (A → B) :=
by vampire "n1ean1n10eatrn0ear"

example : A ∨ B → B ∨ A :=
by vampire

example : A ∧ B → B ∧ A :=
by vampire

example : A → (A → B) → (B → C) → C :=
by vampire

example : (A ∧ B) → (C ∧ B) → C :=
by vampire

example : A → B → C → D → (A ∧ B) ∧ (C ∧ D) :=
by vampire

example : (A ∧ B) → (B ∧ ¬ C) → A ∨ C :=
by vampire

example : (A → B) ∧ (B → C) → A → C :=
by vampire

example : (A → B) ∨ (B → A) :=
by vampire

example : ((A → B) → A) → A :=
by vampire

example : A → ¬ B → ¬ (A → B) :=
by vampire

example : ¬ (A ↔ ¬ A) :=
by vampire

example : (A ↔ B) → (A ∧ B → C) → (¬ A ∧ ¬ B → C) → C :=
by vampire

example : (A ↔ B) → ((A ∧ ¬ B) ∨ (¬ A ∧ B)) → C :=
by vampire

example : (A → B) → A → B :=
by vampire "n10ean0ean1earr"

example : (A → B) → (B → C) → A → C :=
by vampire

example : (A → B ∨ C) → (B → D) → (C → D) → A → D :=
by vampire

example : A ∨ B → B ∨ A :=
by vampire

variables (α : Type) [inhabited α]
variables (a b c : α) (p q : α → Prop) (r : α → α → Prop)
variables (P Q R : Prop)
variable  (g : bool → nat)

example : (∀ x, p x → q x) → (∀ x, p x) → q a :=
by vampire "n10ean0en1n0sman1en0n0smarr"

example : (p a) → ∃ x, p x :=
by vampire

example : (p a) → (p b) → (q b) → ∃ x, p x ∧ q x :=
by vampire

example : (∃ x, p x ∧ r x x) → (∀ x, r x x → q x) → ∃ x, p x ∧ q x :=
by vampire
"
n1n11en0n0sn0spn0spmatn10en1n0sn0spn0spman1en1n0smn0n0smarrn
0en1n0smn0n0smar
"

example : (∃ x, q x ∧ p x) → ∃ x, p x ∧ q x :=
by vampire

example : (∀ x, q x → p x) → (q a) → ∃ x, p x :=
by vampire

example : (∀ x, p x → q x → false) → (p a) → (p b) → (q b) → false :=
by vampire

example : (∀ x, p x) → (∀ x, p x → q x) → ∀ x, q x :=
by vampire

example : (∃ x, p x) → (∀ x, p x → q x) → ∃ x, q x :=
by vampire

example : (¬ ∀ x, ¬ p x) → (∀ x, p x → q x) → (∀ x, ¬ q x) → false :=
by vampire

example : (p a) → (p a → false) → false :=
by vampire

example : (¬ (P → Q ∨ R)) → (¬ (Q ∨ ¬ R)) → false :=
by vampire

example : (P → Q ∨ R) → (¬ Q) → P → R :=
by vampire

example : (∃ x, p x → P) ↔ (∀ x, p x) → P :=
by vampire

example : (∃ x, P → p x) ↔ (P → ∃ x, p x) :=
by vampire

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
n1n10n1010en0n0smatn1n111en0n0sn0spman1n10n1n10n111en0n0sn0s
pman101en0n0sn0spman1n111en0n0sn0spman1n10n1en0n1sn0sn0sppma
n110en0n1sn0sn0sppman0en0n1sn0sn0sppmarrtctrtrrtctn10n1n10n1
11en0n1sn0sn0sppman101en0n1sn0sn0sppman1n111en0n1sn0sn0sppma
n1n10n1en0n1sn1sn0sn0spppman110en0n1sn1sn0sn0spppman0en0n1sn
1sn0sn0spppmarrtctrtrrtctn110en0n0sn0spman11en0n0sn0spmarrtr
tctrtcrtn100en0n0sn0spman1n111en0n1sn0sn0sppman1n10n1n10n111
en0n1sn0sn0sppman101en0n1sn0sn0sppman1n111en0n1sn0sn0sppman1
n10n1en0n1sn1sn0sn0spppman110en0n1sn1sn0sn0spppman0en0n1sn1s
n0sn0spppmarrtctrtrrtctn10n1n10n111en0n1sn1sn0sn0spppman101e
n0n1sn1sn0sn0spppman1n111en0n1sn1sn0sn0spppman1n10n1en0n1sn1
sn1sn0sn0sppppman110en0n1sn1sn1sn0sn0sppppman0en0n1sn1sn1sn0
sn0sppppmarrtctrtrrtctn110en0n1sn0sn0sppman11en0n1sn0sn0sppm
arrtrtctrtcrrn1n1en0n0sn0spman1n10n100en0n1sn0sn0sppman1n10n
111en0n1sn1sn0sn0spppman101en0n1sn1sn0sn0spppman1n111en0n1sn
1sn0sn0spppman1n10n1en0n1sn1sn1sn0sn0sppppman110en0n1sn1sn1s
n0sn0sppppman0en0n1sn1sn1sn0sn0sppppmarrtctrtrrtctn10en0n1sn
0sn0sppman11en0n1sn0sn0sppmarrrtctn0en0n0sn0spmarrtcr
"

lemma gilmore_6 {F G : α → α → Prop} {H : α → α → α → Prop} :
∀ x, ∃ y,
  (∃ u, ∀ v, F u x → G v u ∧ G u x)
   → (∃ u, ∀ v, F u y → G v u ∧ G u y) ∨
       (∀ u v, ∃ w, G v u ∨ H w y u → G u w) :=
by vampire

lemma gilmore_8 {G : α → Prop} {F : α → α → Prop} {H : α → α → α → Prop} :
  ∃ x, ∀ y z,
    ((F y z → (G y → (∀ u, ∃ v, H u v x))) → F x x) ∧
    ((F z x → G x) → (∀ u, ∃ v, H u v z)) ∧
    F x y → F z z := by vampire

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
n10n1011en0n1smatn1010en1n10sman1000earrn1010en1n0sman111ear
rn1n101en100n0smn101n1smatn1n1001en10n1smatrn1n110en11n0smat
n100en100n0smn101n10sman10n1n10n1100ean11eartcttcrrn111earrn
1earr
"

/- A logic puzzle by Raymond Smullyan. -/

lemma knights_and_knaves (me : α) (knight knave rich poor : α → α)
  (a_truth says : α → α → Prop) (and : α → α → α) :
  ( (∀ X Y, ¬ a_truth (knight X) Y ∨ ¬ a_truth (knave X) Y ) ∧
    (∀ X Y, a_truth (knight X) Y ∨ a_truth (knave X) Y ) ∧
    (∀ X Y, ¬ a_truth (rich X) Y ∨ ¬ a_truth (poor X) Y ) ∧
    (∀ X Y, a_truth (rich X) Y ∨ a_truth (poor X) Y ) ∧
    (∀ X Y Z, ¬ a_truth (knight X) Z ∨ ¬ says X Y ∨ a_truth Y Z ) ∧
    (∀ X Y Z, ¬ a_truth (knight X) Z ∨ says X Y ∨ ¬ a_truth Y Z ) ∧
    (∀ X Y Z, ¬ a_truth (knave X) Z ∨ ¬ says X Y ∨ ¬ a_truth Y Z ) ∧
    (∀ X Y Z, ¬ a_truth (knave X) Z ∨ says X Y ∨ a_truth Y Z ) ∧
    (∀ X Y Z, ¬ a_truth (and X Y) Z ∨ a_truth X Z ) ∧
    (∀ X Y Z, ¬ a_truth (and X Y) Z ∨ a_truth Y Z ) ∧
    (∀ X Y Z, a_truth (and X Y) Z ∨ ¬ a_truth X Z ∨ ¬ a_truth Y Z ) ∧
    (∀ X, ¬ says me X ∨ ¬ a_truth (and (knave me) (rich me)) X ) ∧
    (∀ X, says me X ∨ a_truth (and (knave me) (rich me)) X ) ) → false :=
by vampire

end
