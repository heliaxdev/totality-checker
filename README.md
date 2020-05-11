# termination-checker

This repository is a work-in-progress implementation of a type checker with
dependent types and totality checks. The totality checks include strict positivity checks, pattern
matching coverage checks, and termination checks. It is inspired by 'Termination
checking for a dependently typed
language'
by Karl Mehltretter (2007) and 'Towards a practical programming
language based on dependent type theory' by Ulf Norell (2007).

## Preliminaries (type checking without totality checks)

This type checker checks *data type* and *function* declarations. These declarations
consist of *expressions*.

### Expressions

An expression is one of the following (as in `Types.hs`):

```haskell
data Expr
  = Star -- universe of small types
  | Var Name -- variable, parameterized by `name`
  | Con Name -- constructor, parameterized by `name`
  | Def Name -- function/data type, parameterized by `name`
  | Lam Name Expr -- abstraction, \x.e
  | Pi Name Expr Expr -- (PI) dependent function, (x:A)->B
  | App Expr [Expr] -- application, e e1...en
```

Because of dependent types, computation is required during type-checking. An
expression is *evaluated* during type-checking to a *value*. (See `Evaluator.hs`.)

Values may contain *closures*. A closure e<sup>ρ</sup> is a pair of an expression ***e*** and an
*environment* ***ρ***.

Environments provide bindings for the free variables occurring in the
corresponding *e*.
```haskell
type Env = [(Name, Value)]
```
A generic value *k* represents the computed value of a variable during type
checking. More on this below.

```haskell
data Value
  = VStar -- universe of small types
  | VApp Value [Value] -- application
  | VCon Name -- constructor
  | VDef Name -- function/data
  | VLam Name Env Expr -- Lam x e^ρ
  | VPi Name Value Env Expr -- Pi x v_A e^ρ where v_A = eval A^ρ
  | VGen Int -- generic value k
```

The closures in *Lam x e<sup>ρ</sup>* and *Pi x e<sup>ρ</sup>* do not have a
binding for *x*. If there is no concrete value, a fresh generic value *k* would be
the binding for *x* so that the closures can be evaluated.
