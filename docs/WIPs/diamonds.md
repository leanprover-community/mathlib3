# Diamonds #

These are a bad thing which we run into in the type class inference system. Here is an example which mathematicians might find illustrative.

Say we have two typeclasses `M` and `T` (for example `M` could be metric spaces and `T` topological spaces), and we have a coercion from things of type `M` to things of type `T` (for example we could consider the topological space associated to a metric space).

Now say both typeclasses also have products. In practice we would like the type class mechanism to know about this so we might write

```lean
instance M_has_products (\alpha \beta : Type) [M\alphha : M \alpha] [M\beta : M \beta] : M (\alpha \times \beta) := [insert construction of M structure on \alpha \times \beta from H\alpha anf M\beta]

instance T_has_products (\alpha \beta : Type) [T\alpha : T \alpha] [T\beta : T \beta] : T (\alpha \times \beta) := [insert construction of T structure on \alpha \times \beta from T\alpha and T\beta]
```

For example, with metric spaces we could use the distance `d((a1,b1),(a2,b2))=sqrt(d(a1,b1)^2+d(a2,b2)^2)` to define a distance on the product, and with topological spaces we could just use the product topology. Of course at some point we are going to need the theorem that the topological space structure on the product of two metric spaces equals the structure given by the product of the underlying topological spaces, but of course this theorem is not too hard to prove.

However the proof of this theorem is extremely unlikely to be `rfl` and this is a problem for the type class inference system, as the theorem apparently can not somehow be built into the system. What happens in practice is that given two types of class M, the type class inference system now knows two possible ways of putting a structure T structure on their product, and maybe sometimes it ends up choosing one way and some times the other way, resulting in the user having spaces X and Y which look to the end user that they should be definitionally equal but which are not, the obstruction lying deep within some inferred structures. The result is situations where Lean cannot do something which looks completely obvious to the end user because some part of a structure is isomorphic to, but not equal to, what the end user thinks. This results in frustrating errors like substitutions failing in situations where they should "clearly not" fail.

[Example here of M and T failing to behave - not metric and top spaces but just bstract classes; ask Patrick or Mario what the explicit problems were.]

# A possible fix

Coercions are subtle. Often you want at most one coercion from one class to another, and if there are coersions from `X` to `Y` and from `Y` to `X` then the coercion system can get into a loop resulting in timeouts. Now if "every coercion between typeclasses was a forgetful functor" then this problem would go away, because any coercion would just be forgetting structure. So one way of fixing the diamond issue above, which sounds absurd to a mathematician but which really seems to happen in Lean, is that the moment you realise that you want to make Lean automatically realise that you want every metric space to automatically be a topological space, you put the topological space structure *as an explicit part of the metric space structure* but save the user from seeing this by inferring the extra structure internally.

[example here of M having extra fields, namely those of T, which are calculated automatically by the system. Maybe M could have two fields n : nat, and T could have one, namely their sum]




