# category-theory-experiment

A small lab for experimenting with category theory.

The project mixes two styles on purpose:

- **typed experiments** where ordinary Haskell functions behave like morphisms in familiar categories,
- **finite symbolic experiments** where categories, functors, and natural transformations are represented explicitly as data so you can inspect and validate them.

This makes the repo useful as a playground for ideas like:

- building and validating finite categories,
- generating bounded free categories from graphs,
- representing monoids as one-object categories,
- experimenting with functors between finite categories,
- checking naturality conditions directly,
- exploring Kleisli categories for `Maybe`, `[]`, and `Either String`.

---

## Why this repo exists

A lot of category-theory Haskell repos go in one of two directions:

1. they become very abstract and type-heavy very quickly, or
2. they are mostly notes with tiny code snippets.

`categorical-lab` tries to sit in the middle:

- enough structure to feel like a real codebase,
- enough concrete examples to be hackable,
- enough room to grow into your own experiments.

---

## Project layout

```text
category-theory-experiment/
├── app/
│   └── Main.hs
├── src/
│   └── CategoryTheory/
│       ├── Core.hs
│       ├── Small.hs
│       ├── Free.hs
│       ├── Functorial.hs
│       └── Kleisli.hs
├── categorical-lab.cabal
└── README.md
```

### `CategoryTheory.Core`
A tiny category interface and basic constructions.

Highlights:
- a minimal `Cat` class,
- the ordinary category of Haskell functions (`Hask`),
- opposite categories,
- products of categories,
- isomorphisms,
- sample categorical combinators like pairing, currying, and evaluation,
- finite-sample law checks for identity and associativity.

### `CategoryTheory.Small`
An explicit representation of a **finite small category**.

Highlights:
- named objects and morphisms,
- explicit composition table,
- validators for typing, identities, and associativity,
- constructors for:
  - discrete categories,
  - finite ordinals as thin categories,
  - monoids as one-object categories,
  - opposite categories.

### `CategoryTheory.Free`
A bounded free-category playground built from a directed graph.

Highlights:
- graph edges as generators,
- paths as morphisms,
- bounded path enumeration,
- conversion into a `SmallCategory`,
- sample graph and sample path experiments.

### `CategoryTheory.Functorial`
Finite functors and natural transformations represented as explicit maps.

Highlights:
- object and morphism maps,
- validation that a functor preserves identities and composition,
- composition of functors,
- ordinal inclusion functors,
- a shift endofunctor on finite ordinals,
- explicit natural transformations with naturality checks.

### `CategoryTheory.Kleisli`
Category theory through monadic composition.

Highlights:
- a general `KleisliC` construction,
- `Maybe` pipelines for partial computations,
- list-valued nondeterministic transitions,
- `Either String` pipelines for checked computations,
- repeated Kleisli composition.

### `app/Main.hs`
A runnable demo that exercises the main ideas in the repo and prints example results.

---

## Example experiments inside the repo

### 1. Finite ordinals as categories

`finiteOrdinal 4` builds the thin category corresponding to:

```text
0 <= 1 <= 2 <= 3
```

There is a unique morphism `i<=j` whenever `i <= j`, and composition is determined automatically.

This is useful for testing:
- monotone-map-like functors,
- pointwise ordered natural transformations,
- small concrete diagrams.

### 2. Monoids as one-object categories

`monoidCategory` lets you package a monoid operation as a category with one object.

The demo includes a simple Boolean OR example.

### 3. Free categories on graphs

You can define a graph of generating arrows such as:

- `f : A -> B`
- `g : B -> C`
- `h : A -> C`
- `u : C -> A`

Then the repo enumerates paths up to a chosen depth and turns those paths into morphisms of a bounded free category.

### 4. Functors and natural transformations

The repo includes:
- inclusion functors `Ord(3) -> Ord(5)`,
- a shift endofunctor on `Ord(n)`,
- a pointwise natural transformation `Id => Shift` when the underlying order makes those components exist.

### 5. Kleisli composition

The `Kleisli` module explores how category theory shows up in ordinary Haskell programming:

- partial pipelines with `Maybe`,
- branching computations with lists,
- validated computations with `Either String`.

---

## Build and run

With GHC and Cabal installed:

```bash
cabal build
cabal run categorical-lab-demo
```

If you only want to read the code, the modules are written to be reasonably self-contained and approachable.

---


## Notes

This repo is deliberately an **experiment lab**, not a polished categorical framework. Some constructions are represented symbolically using names and tables instead of highly sophisticated type-level encodings. That tradeoff is intentional: it keeps the code easier to inspect, fork, and modify.

