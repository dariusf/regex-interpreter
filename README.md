
Various proofs about regular expression interpreters.

- `Naive`: a naive interpreter which mishandles disjunction, as it cannot backtrack due to not having a representation of the continuation
- `List`: the simplest way to add backtracking: using the list monad to enumerate all matches
- `CPSOption`: a CPS version using an option type; failure to match is represented as the continuation being invoked with `none`
- `DefuncAtWork`: the interpreter from _Defunctionalization at Work_, Danvy & Nielsen, which is in CPS but does not use an option type; failure to match is represented as the continuation _not_ being invoked
- `Defunc`: a defunctionalized version of `CPSOption`
- `SuccFail`: an "double-barrelled CPS" interpreter using success and failure continuations

All but `Naive` are proven correct against a denotational semantics, i.e. `Regex → Set (List Int)`, by defining instances of the `Matcher` typeclass. Properties of correct matchers (e.g. commutativity of disjunction) follow as theorems.

The equivalence of `CPSOption` and `DefuncAtWork` is also proven separately in `Related`.