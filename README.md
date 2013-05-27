limph
=====

lightweight monadic programming for Haskell

Perhaps we would like to have a bidirectional type system. Bidirectional type
systems are nice because they give a clear characterization of how information
ought to flow from a type annotation into the type inference algorithm. Since
we believe there are many things that are just plain ambiguous without a type
signature, this seems like an important thing to be able to handle. For
example, the following is ambiguous:

    bool :: a -> a -> a
    list :: [a]
    maybe :: Maybe a

    v = bool list maybe

We might reasonably ask for any of these types:

1. `v :: Maybe [a]`
2. `v :: [Maybe a]`
3. `v :: MaybeT [] a`
4. `v :: ListT Maybe a`

Although (2) might be argued to be "better" than (3), and (1) might be argued
to be better than (4), it seems (1) and (2) are of incomparable goodness --
sometimes you want one, and sometimes the other!

Vilhelm and Daniel propose the following bidirectional type system. Here we
should view `G |- e => M t` as saying that given a context `G`, an expression
`e`, and a monad `M`, we output a type `t`. On the other hand, in the judgment
`G |- e <= M t`, all of `G`, `e`, `M`, and `t` are inputs, and the judgment
holds when we can check that e has the given (monadic) type. Unlike many
bidirectional judgments, we are viewing `M` (a part of the "type") as input to
*both* judgments.

Here are some proposed rules for the judgments:

(dmwit asks: hum, haven't we agreed that the RHS of arrows are monadic? why
aren't they in the app rules?)

    (app-<=)
    G |- a <= M (B -> A)
    G |- b => M B
    --------------------
    G |- a b <= M A

    (app-=>)
    G |- a => M (B -> A)
    G |- b <= M B
    --------------------
    G |- a b => M A

    (morph)
    B === A
    G |- a => M B
    -------------
    G |- a <= M A

    (var)
    G(x) = s
    G |= M t <= s
    -------------
    G |- x => M t

We haven't worked out just what the `G |- A <= B` judgment should look like
yet, but it at least needs to know about return. (dmwit asks: Why? Can't
remember.) We conjecture that `(morph)`, `(var)`, and one of either `(app-<=)`
or `(app-=>)` makes a pretty decent system.

So, good next steps:
1. try to write down the `G |- A <= B` relation, which probably ought to
   include rules for "lift" and "return" and the specialized Id-"lift".
2. write down the typing rule for let
3. how annoying is type-level application?
4. can using the standard rule instead of the nonstandard one reduce the number of monad law applications we need to use to get something reasonable?
