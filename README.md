Disclaimer
===
This has been worked on as part of my masters' thesis, which is now finished. There is ongoing development at https://gitlab.imn.htwk-leipzig.de/waldmann/cyp/-/tree/master


cyp<sup>[1](#footnote1), [2](#footnote2)</sup>
===

cyp (short for "Check Your Proof") verifies proofs about Haskell-like programs. It is designed as an teaching aid for undergraduate courses in functional programming.

The implemented logic is untyped higher-order equational logic, but without lambda expressions. In addition, structural induction over datatypes is supported.

The terms follow standard Haskell-syntax and the background theory can be constructed from datatype declarations, function definitions and arbitrary equations.

The use of this tool to verify Haskell functions is justified by the following considerations:

  * [Fast and Loose Reasoning is Morally Correct](http://www.cse.chalmers.se/~nad/publications/danielsson-et-al-popl2006.html).
  * We convinced ourselves that for a type-correct background-theory and a type-correct proposition a proof exists if and only if a type-correct proof exists. A formal proof is still missing. Here, type-correct is meant in the sense of Haskell's type system, but without type-classes.
  
<a name="footnote1">1</a>: This is a modified version of cyp which requires the user to be explicit about generalization. This version is used in the "Formal Methods and Functional Programming" lecture at ETH Zürich

<a name="footnote2">2</a>: This is a modified version of cyp adding a type system and so-called "blueprint" exercises, where for a given theory/proof with holes these have to be filled out to make the theory and proof valid. This version is used in the "Fortgeschrittene Programmierung" lecture at HTWK Leipzig.

Getting started
===============

To get the repository and build & install the binary (using [stack](https://docs.haskellstack.org/en/stable/README/))

    git clone https://github.com/ehonda/cyp.git
    cd cyp
    stack install

The tests can be run via

    stack test

Usage
=====

There are two usage modes, classic and blueprint, which are explained briefly in the following subsections. In any case, a theory and a proof will be needed, of which the syntaxes are explained in the respective sections. Examples for valid (blueprint-)theories and proofs can be found in [`examples`](https://github.com/ehonda/cyp/tree/master/examples) and in [`test-data/pos`](https://github.com/ehonda/cyp/tree/master/test-data/pos).

Classic
-------

In classic mode, a theory and a proof are provided to cyp

    cyp cthy cprf

The first argument provided is the theory, the second argument the proof. They can be named arbitrarily, the naming scheme from this example is used throughout the repository. The theory and proof will then first be typechecked, where the typechecking of the Haskell part of the theory is modelled after the typechecking of standard-Haskell, albeit without type classes. If the typecheck succeeds, cyp will check if all goals specified in the theory are proven by the Lemmas in the proof.

Blueprint
---------

In blueprint mode, a blueprint theory (and optionally a blueprint proof) are provided alongside a classic theory and proof. In a blueprint theory, the right hand sides of function declarations can be missing

```haskell
f x y = _
```

In a blueprint proof, the term and/or rule of a step of an equational proof can be missing

```
                  S a
(by _)        .=. _
```

The binary can then be executed in the following way

```bash
# Without blueprint-proof
cyp bpthy cthy cprf

# With blueprint-proof
cyp bpthy cthy bpprf cprf
```

The naming convention here is the prefix "bp" for blueprints, "c" for classic cyp-theories/proofs. It will then be checked that the blueprints match the provided classic theories/proofs (i.e. all occurences of holes are replaced by a valid term/rule, the rest of the contents are equal). If that is the case, the classic type- and proofcheck take place.

Syntax of Theories
==================
Theories can be divided into two parts, a Haskell part and a cyp-specific part. The following [example](https://github.com/ehonda/cyp/tree/d85b57ec4258a260ec99d65bb880dd4eb0a84549/examples/btree) highlights these parts (but they don't have to actually be structurally separate blocks, like it is shown here)

```haskell
-- Haskell part
-----------------------------------------------
data Bool = False | True
data Tree a = Leaf | Branch (Tree a) a (Tree a)

-- Abstract function declaration, no definition
-- is given here, but an axiom is declared
-- later
(&&) :: Bool -> Bool -> Bool

-- Concrete function declaration, definition
-- is given
foo :: Tree a -> Bool
foo Leaf = True
foo (Branch l n r) = (foo l) && (foo r)

-- cyp part
-----------------------------------------------
axiom true_and_true: True && True .=. True

goal foo t .=. True
```

In the Haskell part, datatypes and functions can be declared using the common Haskell syntax. Not all valid Haskell declarations are supported by cyp, the above example covers most of what can be done. For simplicity, cyp assumes all type variables introduced by datatype declarations (eg. `a` in `Tree a` above) to be of kind `*`. It is possibly to provide a function type signature without declaring any equations for it, we call this an abstract function. These can then only be used via axioms declared about them.

Line breaks within declarations (continuing one indentation level deeper on the next line, like it is possible in [standard](https://www.haskell.org/onlinereport/haskell2010/haskellch2.html#x7-210002.7) haskell) are not allowed in cyp.

All datatypes and functions to be used in cyp have to be explicity declared, with the exception of the list datatype `[a]`, which is implicitly available in every cyp-theory.

In the cyp part, axioms and goals can be declared. These are simply equations (using the cyp syntax `lhs .=. rhs` for equations). Axioms get a name and can then be referenced via that name in proofs, goals have no name and need to be proved by the proof provided to cyp.

Syntax of Proofs
================

In this section, the syntax of Lemmas and the different types of proofs is presented. Concrete examples are linked to at the beginning of each subsection. Some of the line breaks in the syntax for proofs are optional (e.g. the line break after `Then` in a `Case`), but most aren't. Any time a variable or term (with or without type signature) is read, they are parsed until the end of line (or until a delimiter, if several variables/terms with type signature can be written down in a list, like in `Fix`, or `generalizing`). In these cases, the line breaks are needed for a correct parse and thus not optional. In any case, it is recommended to also insert the optional line breaks as presented here, to improve readability.

Lemmas
------

A proof file can contain an arbitrary number of lemmas. Proofs of later lemmas can use the the previously proven lemmas. The syntax of lemmas looks like this

    Lemma [name]: <lhs> .=. <rhs>
    <Proof ... QED>

`<lhs>` and `<rhs>` are arbitrary Haskell expressions. `[...]` here is meta-syntax and means the content of the brackets is optional, i.e. Lemmas can have an optional name, so they can be referenced by other Lemmas. The Lemma header is followed by the proof, represented here by `<Proof ... QED>`. Different types of proofs are availabe in cyp and will be explained in the following subsections.

Equational Proofs
-----------------

The syntax for this [type of proof](https://github.com/ehonda/cyp/blob/d85b57ec4258a260ec99d65bb880dd4eb0a84549/examples/nat_succ_eq_plus_one/cprf) is as follows

```
Proof
                  <t1>
    (by <r1>) .=. <t2>
    ...
    (by <r(n-1)>) .=. <tn>

    [             
                   <t'1>
    (by <r'1>) .=. <t'2>
    ...
    (by <r'(m-1)>) .=. <t'm>
    ]
QED
```

The proof consists of one or two equations sequences. For each step of an equation sequence, the rule `<r>` to rewrite term `<t>` to term `<s>` is given (which can be a function definition or the name of an axiom or lemma) and each step of a sequence has to be specified on a new line.

Then, to prove `<lhs> .=. <rhs>` via equational proof, all steps in the equation sequences must be valid and:

* If one equation sequence is specified, `<t1>` must be `<lhs>`, `<tn>` must be `<rhs>`.

* If two equation secuences are specified, `<t1>` must be `<lhs>`, `<t'1>` must be `<rhs>` and `<tn>` must be `<t'm>`, i.e. the two sequences "meet in the middle".


Extensionality Proofs
---------------------

The syntax for this [type of proof](https://github.com/ehonda/cyp/blob/d85b57ec4258a260ec99d65bb880dd4eb0a84549/test-data/pos/easy/cprf) is as follows

```
Proof by extensionality with <x> :: <type>
	Show: <lhs_x> .=. <rhs_x>
    <Proof ... QED>
QED
```

This proof technique is used to show equality of functions, for example `not . not .=. id`. The proof header introduces an extensionality variable, annotated with its type, e.g. `x :: Bool`. Then, that variable is appended to the original left- and right-hand-sides of the equation in `Show:`, for our concrete examples we would get `(not . not) x .=. id x`. The proof for that is then given in the subproof `<Proof ... QED>`, which can be any of the proof types presented here.

The proof is valid if it `Show:` typechecks and the subproof is valid.


Case Analysis Proofs
--------------------

The syntax for this [type of proof](https://github.com/ehonda/cyp/blob/d85b57ec4258a260ec99d65bb880dd4eb0a84549/test-data/pos/easy/cprf) is as follows

```
Proof by case analysis on <t> :: <type>
	Case <c1>
        Assume
            AS: <t> .=. <c1>
        Then
        <Proof ... QED>

    ...

    Case <cn>
        ...
QED
```

Using this proof technique, we first specifiy the term `<t>` to do case analysis on, together with it's type `<type>`, e.g. `(p x) :: Bool`. The different cases are then the different dataconstructors of that type, e.g. `<c1> = False`, `<cn> = True`. Inside the case branches, we make the case assumption explicit, e.g. `AS: p x .=. False`, it can then be used in the accompanying subproof.

The proof is valid if `<t>` has the correct type, the assumptions typecheck, the cases are exhaustive and all subproofs are valid.


Induction proofs
----------------

The syntax for this [type of proof](https://github.com/ehonda/cyp/blob/d85b57ec4258a260ec99d65bb880dd4eb0a84549/examples/bp_symdiff/cprf) is as follows (using the placerholder `<gens> = <y1> :: <ty1>, ..., <yn> :: <tyn>`)

```
Proof by induction on <x> :: <tx> [generalizing <gens>]
    Case <cb1>
        [For fixed <gens>]
        Show: <lhs_cb1> .=. <rhs_cb1>

        <Proof ... QED>

    ...

    Case <cr1>
        Fix <arg1> :: <targ1>, ..., <argn> :: <targn>
        Assume
            IH1: [forall <gens>]: <lhs_IH1> .=. <rhs_IH1>
            [IH2, ..., IHn]

        Then [for fixed <gens>]
        Show: <lhs_cr1> .=. <rhs_cr1>

        <Proof ... QED>

    ...
QED
```

Using this proof technique, we first specifiy an induction variable and its type. Optionally, generalization variables are specified (together with their types), over which the induction hypotheses will be all-quantified. Then, first the base cases are proved. Afterwards, the inductive cases are proved, where an induction hypothesis is assumed for each recursive argument of the case constructors. Constructor arguments are explicitly fixed, all variables that are not generalized are implicitly fixed.

To make a little more sense of all of this, we take a look at the following more concrete [example](https://github.com/ehonda/cyp/blob/d85b57ec4258a260ec99d65bb880dd4eb0a84549/examples/bp_symdiff/cprf)

```
Lemma symdiff_sym: symdiff x y .=. symdiff y x

Proof by induction on x :: N generalizing y :: N
  Case Z
    For fixed y :: N
    Show: symdiff Z y .=. symdiff y Z

    <Proof ... QED>

  Case S x
    Fix x :: N
    Assume
      IH: forall y :: N: symdiff x y .=. symdiff y x
    
    Then for fixed y :: N
    Show: symdiff (S x) y .=. symdiff y (S x)

    <Proof ... QED>
QED
```

Here, the induction variable is `x :: N` and we generalize over `y :: N`. The base case is `Z` (since `data N = Z | S N`), while the inductive case is `S x`, where we fix `x :: N`. We assume one induction hypothesis (for the recursive constructor argument `x :: N`), which is all-quantified over our generalization variable. We then have to show the outer goal, where we substitute the induction variable `x` by the term `S x` (note that this is a different, new `x` and not our induction variable).

Known limitations
=================

  * There is no check that the functions defined in the background theory terminate (on finite inputs). This is demonstrated in this [example](https://github.com/ehonda/cyp/tree/d85b57ec4258a260ec99d65bb880dd4eb0a84549/examples/non_terminating_def). The focus of this tool is checking the proofs of students against some known-to-be-good background theory, but in blueprint mode these definitions can be written.

  * cyp supports only equational reasoning, so it is not possible to use propositional or predicate logic.
