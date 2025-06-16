# Interpreting Algebraic Effects Through Monads

*This work was presented as my undergraduate thesis for the completion of my Bachelor's degree in Computer Science. It presents a syntax-directed translation from an IR in ANF, with a type and effect system based on Leijen's Koka system.*

**To run:** _cabal run exes -- **fileName**_

**To test:** _change the **fileName** to one of the `test.lc` files to run different predefined tests_

### Packages

- *extensible-effects*

### Entry Syntax

#### If you want to create your own tests, the syntax below will guide you through the process.

```bnf
effects     ::= effect effectName { declaration+ }
declaration ::= funName : ∀ var* . type
type        ::= int | bool | string | var | type → effs type
effs        ::= var | effectName | <effs, effs+>
fun         ::= funName = lambda
lambda      ::= \ var+ -> stmt
stmt        ::= lambda | let | where | app | op | var
let         ::= let var = stmt in stmt
where       ::= stmt where { name var+ = stmt }
app         ::= (stmt stmt)
op          ::= (stmt operator stmt)
operator    ::= + | - | * | / | < | > | ==
```