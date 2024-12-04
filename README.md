![Coquand](https://img.shields.io/badge/Coq-8.16.1-CC2927)
![](https://img.shields.io/badge/License-BSD--3--Clause-blue)
[![Maintenance](https://img.shields.io/badge/Maintained%3F-yes-green.svg)](https://GitHub.com/Naereen/StrapDown.js/graphs/commit-activity)


# LML - Little Mermaid Logic

This project formalizes a deep embedding of arbitrary normal modal logic systems in the Coq proof assistant.

# Files

- [Sets](coq/Sets.v): some basic definitions for working with sets in Coq.
- [Modal_Library](coq/Modal_Library.v): core of the library. This file defines the syntax of formulas, frames, models, and entailment.
- [Modal_Notations](coq/Modal_Notations.v): notations used throughout the development.
- [Deductive_System](coq/Deductive_System.v): definition of a Hilbert-style deduction system for modal logic, quantified over a set of axioms.
- [Modal_Tactics](coq/Modal_Tactics.v): basic auxiliary lemmas regarding derivation in the system, making it feel more [natural](https://en.wikipedia.org/wiki/Natural_deduction).
- [Completeness](coq/Completeness.v): proof of completeness in regard to the Kripke semantics.
- [Frame_Validation](coq/Frame_Validation.v): characterization of axioms by the kind of frame relation they represent.
- [Logical_Equivalence](coq/Logical_Equivalence.v): minor lemmas about implications on the system (this should eventually be moved).
- [Soundness](coq/Soundness.v): proof of soundness in regard to the Kripke semantics.
- [Fusion](coq/Fusion.v): proof for preservation of soundness through fusion of separate logic systems.
- [Examples](coq/Examples.v): some example derivations, including [Löb's theorem](https://en.wikipedia.org/wiki/L%C3%B6b%27s_theorem).

We are aware that the files do need some cleanup. We are too tired at the moment, but we will eventually do it.

# Publications

This is a research project. You may have found this code from one of our publications. The current publications about this codebase are as follow:

- [A Sound Deep Embedding of Arbitrary Normal Modal Logics in Coq](https://dl.acm.org/doi/10.1145/3561320.3561329)
- [Soundness-Preserving Fusion of Modal Logics in Coq](https://link.springer.com/chapter/10.1007/978-3-031-78116-2_8)

We currently have one more paper under review; this file should be updated to reflect that after the decision is taken.

# License

This is free software. You're free to use it under the [BSD 3-clause](LICENSE) license. Enjoy!

# Authors

This project has been developed by [Santa Catarina State University](https://www.udesc.br/international)'s research group on theoretical computer science, [Função](https://github.com/funcao). All rights reserved.

<center>

[<img src="https://github.com/arielsilveira.png" alt="Ariel Agne da Silveira" style="border-radius:50%;" width="80px" height="80px"/>](https://github.com/arielsilveira)
[<img src="https://github.com/MiguelANunes.png" alt="Miguel Nunes" style="border-radius:50%;" width="80px" height="80px"/>](https://github.com/MiguelANunes)
[<img src="https://github.com/takanuva.png" alt="Paulo Torrens" style="border-radius:50%;" width="80px" height="80px"/>](https://github.com/takanuva)
[<img src="https://github.com/rodrigogribeiro.png" alt="Rodrigo Ribeiro" style="border-radius:50%;" width="80px" height="80px"/>](https://github.com/rodrigogribeiro)
[<img src="https://github.com/kaqui.png" alt="Karina Roggia" style="border-radius:50%;" width="80px" height="80px"/>](https://github.com/kaqui)

</center>
