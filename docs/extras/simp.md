# Simp #

The `simp` tactic works by applying "a conditional term rewriting system" (I don't know what that is), to try and simplify the goal. You can actually watch what it's doing -- which to the untrained eye might look like trying to apply a whole bunch of random lemmas one after the other until it stumbles upon the answer -- by writing `set_option trace.simplify true` in your code. If you do this in the below

```lean
namespace xena

definition cong (a b m : ℤ) : Prop := ∃ n : ℤ, b - a = m * n

notation a ` ≡ ` b ` mod ` m  := cong a b m 
set_option trace.simplify true
theorem cong_refl (m : ℤ) : ∀ a : ℤ, a ≡ a mod m :=
begin
intro a,
unfold cong,
existsi (0:ℤ),
simp
end

end xena
```

you will discover that Lean seems to apply simp when you do an unfold as well. I don't know if this is right but unfold gets a green underline too.

If you only want to see what worked rather than all the things that didn't, you could try `set_option trace.simplify.rewrite true`.

### Simp lemmas

In case you want to train simp to be better at solving the kind of arguments you are currently working on, you can add new lemmas for yourself. For example in mathlib in `algebra/field.lean` we find the line

```lean
@[simp] theorem ne_zero (u : units α) : (u : α) ≠ 0
```

This lemma is then added to `simp`'s armoury. Note several things however.

1) You can't just make a random theorem into a simp lemma. It has to be of a certain kind, the most important kinds being those of the form `A=B` and `A↔B`. Note however that if you want to add `fact` to `simp`'s weaponry, you can prove

```lean
@[simp] lemma my_lemma : fact <-> true
```

2) If you are not careful you can add a bad simp lemma of the form `foo x y = [something mentioning foo]` and then `simp` will attempt to rewrite `foo` and then end up with another one, and attempt to rewrite that, and so on. This can be fixed by using `rw` instead of `simp`, or using the config option `{single_pass := tt}`.


### When not to use simp

Don't use simp in the middle of proofs. Use it to finish proofs. If you really need to simplify a goal, use simp, and then cut and paste the goal into your code and then try something like `suffices : (simplified thing), by simpa [this]` or some such thing. This is really important because the behaviour of simp changes sometimes, and if you put simp in the middle of proofs then your code might randomly stop compiling and it will be hard to figure out why if you didn't write down the exact thing which simp used to be doing.

### How to use simp better.

Conversely, if you ever manage to close a goal with simp, then take a look at the line before you ran simp. Could you have run simp one line earlier? How far back did simp start working? Even for goals where you didn't use simp at all -- could you have used simp for your last line? What about the last-but one? And so on.


### Keeping up to date with simp tweaks

Search for simp in [the changelog](https://github.com/leanprover/lean/blob/master/doc/changes.md) to find out about more recent flags etc that get added to simp.

### TODO

We could add some notes to cover the below:

"Re: documentation. If you mention congruence, you could show off simp's support for congruence relations. If you show reflexivity and transitivity for cong, and have congruence lemmas for +, etc., then you can rewrite with congruences as if they were equations."

