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
    G |= s <= M t
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
4. can using the standard rule instead of the nonstandard one reduce the number
   of monad law applications we need to use to get something reasonable?

Vilhelm complains that maybe we shouldn't make the syntax of arrow
types always have a monad in them. Here is a declarative system
without that:

types
T ::= T1 -> T2
    | T1 T2
    | a

typeschemes
S ::= forall as. Cs => T

contraints
C ::=  m1 ≤ m2

terms
t ::= x
    | t1 t2
    | \x. t
    | let x=t1 in t2

contexts
G ::= empty
    | G, x:S


Typechecking and type synthesis
(the judgements are
   G, Cs |- t ==m==> T
   G, Cs |- t <==m== T
  where G, Cs, t and m are inputs, T is either output or input)

G,Cs |- t1 ==m==> T1
Cs |- T1 ≤ m (T11 -> m T12)
G,Cs |- t2 <==m== m T11
---------------------------------- app
G,Cs |- t1 t2 ==m==> m T12


G,Cs |- t2 ==m==> T11'
Cs |- T11' ≤ m T11
G,Cs |- t1 <==m== m (T11 -> m T12)
-------------------------------------- app (non-standard rule)
G,Cs |- t1 t2 <==m== m T12

G(x) = forall as. Cs' => T
Cs implies Cs'
-------------------------------- var
G,Cs |- x ==m==> T


Subtyping (the judgement is Cs |- T1 ≤ T2)

C |- T2 ≤ T2'
----------------------------- eta
C |- T1->T2 ≤ T1->T2'

----------------------------- return
C |- T ≤ m T

C |= m1 ≤ m2
----------------------------- lift
G |- m1 T ≤ m2 T

C |- T1 ≤ T2
C |- T2 ≤ T3
--------------------------- trans
C |- T1 ≤ T3


This system is not algorithmic: the subtyping judgement has trans in it,
and the application rule(s) calls the subtyping judgement in a way
where it is not quite clear what is input and output.

We expect all the elaboration be come from the use of the subtyping judgement.

Notes from July 7:

Can we implement the case of the ≤ judgement that we need? Here are two functions which kindof do it:

fun1 : Given T and m, output the best substitution s and best types T1, T2 such that either T ≤ T1->m T2 or T ≤ m (T1 -> m T2).

fun1 ( T1->T2, m) = T1 and mT2 , null substitution
fun1 ( n T, m) = check n≤m and output fun3(T, m)
fun1 ( a , m) =  output substitution a := b (T1 -> m T2) 
fun1 (otherwise) = fail

fun3 : Given T and M, output the best T1, T2 such that T ≤ T1 -> m T2
fun3 ( T1->T2, m) = T1 and m T2, null substitution
fun3 ( a, m) = output substitution a := (T1 -> m T2)
fun3 ( otherwise) = fail

The problem here is the type variable b, which is applied as a type constructor, but ranges over either type constructors or the identity type function. This seems like a very special case of higher-order unification...

Notes from July 10:

Ok, this function was not quite right, we need an extra case for T1->mT2:

fun3 : Given T and m, output the best T1, T2 such that T ≤ T1 -> m T2
fun3 ( T1->nT2, m) when n≤m = T1 and T2, null substitution
fun3 ( T1->T2, m) = T1 and m T2, null substitution
fun3 ( a, m) = output substitution a := (T1 -> m T2)
fun3 ( otherwise) = fail

Note that this does not do anything special for e.g. A->m(m B). That is consistent with
the definition of ≤ we picked. If we also wanted the elaborator to insert monadic joins,
we could add a rule like

-------------------- join
  m (m T) ≤ m T

but it seems fine to not do that.

Now the question is what "best" means. See the whiteboard photo for one attempt (apparently
not quite working yet.


Notes from September 16:

1. We note that the current equational system does not talk about monad morphisms at all. We decided to not worry about this for now,
   let's first get something working without them.

Here are some possible next steps:

2. Figure out how to solve the constraints. This seems to involve both unification and checking for propositional satisfiability.

3. Write up an algorithmic system, and write a typechecker that generates constraints.

We already have a proposed application rule. What about variable and lambda? We think something like:

x:T in Gamma
----------------
Gamma |- x : m_p T

Gamma, x:T1 |- t : T2
--------------------------------------
Gamma |- (\x:T1.t) : m_p (T1->T2) 

Note, this only introduces one level of monads. So it doesn't match, e.g., a declarative system where you can apply a "return" rule anywhere.

4. Think about what declarative system the proposed algorithmic system corresponds to.

