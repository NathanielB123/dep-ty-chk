# DepTyChk

The goal of this project is to implement a simple, sound bidirectional typechecker for dependent types, in Agda.

The combination of dependently typed lambda calculus being so high-order, and the goal of producing an instrinsically-typed syntax (to ensure soundness) makes this very non-trivial. My best progress towards a real typechecking algorithm is in [./DepTyChk/Simple.agda](Simple.agda). 

To truly guarantee soundess, I must replace the postulated equations (relating different substitutions in how they commute) with cubical path constructors (see [./DepTyChk/Concrete.agda](Concrete.agda)), and get substitution it to pass the termination checker, somehow...
