# Atoms

A formalization in Lean 4, on Mathlib, of higher category theory built on the category of atoms,
in the sense of Hadzihasanovic's *Combinatorics of higher-categorical diagrams* and of the papers
of Chanavat and Hadzihasanovic on diagrammatic sets.

An oriented graded poset is a poset graded by dimension in which every covering relation is
marked as an input or an output; it records the faces of a diagram. Molecules are the oriented
graded posets generated from the point by pasting and rewriting. Atoms are the molecules with a
greatest element, the shapes of single cells, and a diagrammatic set is a presheaf on the
category of atoms. The library develops the combinatorics of these shapes, the homotopy theory of
presheaves it rests on (Cisinski's model structures, Grothendieck's test categories), and the
model structures on diagrammatic sets for homotopy types and for `(∞, n)`-categories.

It is about 228,000 lines of Lean in 951 files, written from September 2026 on with AI agents
under my direction. There is no `sorry`, and no axiom beyond `propext`, `Classical.choice` and
`Quot.sound`. This repository is a release of the Lean sources alone: the project's comments,
documentation and tooling are not included.

## Main definitions

- Oriented graded posets, [`Atoms.Molecule.OGP`](Atoms/Molecule/OrientedGradedPoset.lean);
  molecules, [`OGP.IsMolecule`](Atoms/Molecule/Molecule.lean); atoms,
  [`OGP.IsAtom`](Atoms/Molecule/Submolecule.lean).
- The category of atoms, [`Atoms.Shape.Atom`](Atoms/Shape/Atom.lean), and diagrammatic sets,
  [`Atoms.Diagrammatic.DiagSet`](Atoms/Diagrammatic/DiagrammaticSet.lean).
- Diagrammatic `(∞, n)`-categories,
  [`Atoms.Diagrammatic.IsInftyCategory`](Atoms/Diagrammatic/InftyCategory.lean).
- The adjunction between simplicial sets and diagrammatic sets, left Kan extension and
  restriction along the functor from simplices to atoms:
  [`Atoms.Diagrammatic.sSetDiagSetAdj`](Atoms/Diagrammatic/SimplicialAdjunction.lean).

## Some of what is proved

Homotopical algebra on presheaves:

- Cisinski's generation theorem, as a model structure on presheaves built from an exact cylinder
  and a small class of monomorphisms:
  [`HomotopicalAlgebra.ExactCylinder.modelCategory`](Atoms/Homotopical/Cylinder/ModelStructure.lean).
- The Eilenberg–Zilber lemma for Eilenberg–Zilber categories:
  [`Atoms.Homotopical.EZCategory.exists_isNondegenerate`](Atoms/Homotopical/EilenbergZilber/Lemma.lean)
  and `existsUnique_iso_of_isNondegenerate` in the same file.
- The Kan–Quillen and Joyal model structures on simplicial sets, neither of which Mathlib has at
  this version:
  [`SSet.modelCategoryQuillen.kanQuillenModelCategory`](Atoms/Homotopical/Simplicial/KanQuillen.lean)
  and
  [`SSet.modelCategoryJoyal.joyalModelCategory`](Atoms/Homotopical/Simplicial/Joyal.lean).
  Their cofibrations are the monomorphisms and their fibrant objects are Mathlib's Kan
  complexes, respectively Mathlib's quasicategories, and each is the only model structure on
  simplicial sets with these cofibrations and fibrant objects:
  [`eq_kanQuillenModelCategory` and `eq_joyalModelCategory`](Atoms/Homotopical/Simplicial/ModelStructureUniqueness.lean).

Test categories:

- For a weak test category, presheaves localized at the induced weak equivalences are equivalent
  to small categories localized at the basic localizer:
  [`Atoms.TestCategory.BasicLocalizer.localizationEquivalence`](Atoms/TestCategory/LocalizationEquivalence.lean).
- The minimal basic localizer is the one given by the weak equivalences of the Kan–Quillen model
  structure:
  [`Atoms.TestCategory.minimalBasicLocalizer_eq_kanBasicLocalizer`](Atoms/TestCategory/Simplicial/KanBasicLocalizer.lean).

Combinatorics of atoms:

- `IsMolecule` is defined by decomposing an oriented graded poset into closed subsets. It agrees
  with the class generated from the point, up to isomorphism, by pasting and rewriting:
  [`Atoms.Molecule.OGP.isGeneratedMolecule_iff_isMolecule`](Atoms/Molecule/Gluing/Generated.lean).
- There is at most one isomorphism from a molecule to any oriented graded poset:
  [`Atoms.Molecule.OGP.IsMolecule.subsingleton_iso`](Atoms/Molecule/Rigidity.lean).
- The Gray product of two molecules is a molecule:
  [`Atoms.Molecule.OGP.isMolecule_grayProduct`](Atoms/Molecule/Construction/GrayProductMolecule.lean).

Diagrammatic sets:

- The atoms form an Eilenberg–Zilber category,
  [`Atoms.Diagrammatic.ezCategoryAtom`](Atoms/Diagrammatic/DiagrammaticSet.lean), and a test
  category for every basic localizer:
  [`Atoms.TestCategory.BasicLocalizer.isTest_asSmallAtom`](Atoms/Diagrammatic/AtomTest.lean).
- The model structure for homotopy types,
  [`Atoms.Diagrammatic.DiagSet.modelCategoryCisinski.cisinskiModelCategory`](Atoms/Diagrammatic/InfinityEquivalence.lean),
  and its Quillen equivalence with the Kan–Quillen model structure:
  [`Atoms.Diagrammatic.isQuillenEquivalence_sSetDiagSetAdj_kan`](Atoms/Diagrammatic/KanComparison.lean).
- The model structures for `(∞, n)`-categories, for `0 ≤ n ≤ ∞`,
  [`Atoms.Diagrammatic.inftyModelCategory`](Atoms/Diagrammatic/Localization/ModelStructure.lean),
  whose fibrant objects are the diagrammatic `(∞, n)`-categories:
  [`Atoms.Diagrammatic.isFibrant_infty_iff`](Atoms/Diagrammatic/Marked/FlatEquivalence.lean).
- The Quillen equivalence between the Joyal model structure and the `(∞, 1)` model structure:
  [`Atoms.Diagrammatic.isQuillenEquivalence_sSetDiagSetAdj`](Atoms/Diagrammatic/Joyal/Comparison.lean).
- The nerve of a bicategory, in Mathlib's sense, is a diagrammatic `(∞, 2)`-category,
  [`Atoms.Diagrammatic.isInftyCategory_bicategoryNerve`](Atoms/Diagrammatic/BicategoryNerve/InftyTwo.lean),
  and the bicategory built from its cells, `RoundBicat`, is biequivalent to the one it came from:
  [`nervePseudoInverseUnit` and `nervePseudoInverseCounit`](Atoms/Diagrammatic/BicategoryNerve/Biequivalence.lean).
- A fibrational Yoneda lemma for Cartesian fibrations over a diagrammatic `(∞, 1)`-category:
  [`Atoms.Diagrammatic.DiagSet.trivialFibration_cartesianYoneda`](Atoms/Diagrammatic/Fibration/FibrationalYoneda.lean).

The statements about the Joyal model structure, as they are in the sources (the namespaces are
`SSet.modelCategoryJoyal` and `SSet`):

```lean
theorem isFibrant_iff_quasicategory (X : SSet.{u}) : IsFibrant X ↔ X.Quasicategory

theorem modelCategoryJoyal.eq_joyalModelCategory (M : ModelCategory SSet.{u})
    (hc : @cofibrations SSet.{u} _ M.categoryWithCofibrations =
      MorphismProperty.monomorphisms SSet.{u})
    (hf : ∀ X : SSet.{u}, @IsFibrant SSet.{u} _ M.categoryWithFibrations _ X ↔ X.Quasicategory) :
    M = modelCategoryJoyal.joyalModelCategory
```

`ModelCategory`, `SSet.KanComplex`, `SSet.Quasicategory` and `Bicategory` are Mathlib's. Quillen
equivalences are defined in this library, in
[`Quillen.lean`](Atoms/ForMathlib/AlgebraicTopology/ModelCategory/Quillen.lean).

## Layout

| Directory | Files | Lines | Contents |
|---|---|---|---|
| `Atoms/ForMathlib` | 274 | 39,800 | General results that are not about atoms: model categories, simplicial sets, category theory, orders |
| `Atoms/Homotopical` | 130 | 29,700 | Eilenberg–Zilber categories, Cisinski's theory, simplicial sets |
| `Atoms/TestCategory` | 58 | 7,900 | Basic localizers and test categories |
| `Atoms/Molecule` | 126 | 37,200 | Oriented graded posets and molecules |
| `Atoms/Shape` | 29 | 8,300 | The category of atoms, and constructions in it |
| `Atoms/Diagrammatic` | 314 | 102,600 | Diagrammatic sets: equivalences, the model structures and their comparison with simplicial sets, Gray tensor products, joins and slices, mapping spaces, fibrations, limits, adjunctions, the nerve of a bicategory |
| `Atoms/Doctrine` | 3 | 100 | Definitions only |
| `Atoms/Serialize` | 8 | 2,100 | A text format and a JSON format for shapes; a separate library, not imported by `Atoms` |

The other nine files are lists of imports.

## Building

Install [elan](https://github.com/leanprover/elan), then:

```sh
lake exe cache get
lake build
```

The Lean version is pinned in `lean-toolchain` and Mathlib's revision in `lake-manifest.json`.
The first command downloads Mathlib's compiled files. The second builds the library, which takes
about 17 minutes on six cores.

To see the axioms a result depends on:

```sh
echo 'import Atoms
#print axioms Atoms.Diagrammatic.isQuillenEquivalence_sSetDiagSetAdj' | lake env lean --stdin
```

## References

- A. Hadzihasanovic, *Combinatorics of higher-categorical diagrams*,
  [arXiv:2404.07273](https://arxiv.org/abs/2404.07273).
- C. Chanavat and A. Hadzihasanovic, *Diagrammatic sets as a model of homotopy types*,
  [arXiv:2407.06285](https://arxiv.org/abs/2407.06285).
- C. Chanavat and A. Hadzihasanovic, *Equivalences in diagrammatic sets*,
  [arXiv:2410.00123](https://arxiv.org/abs/2410.00123).
- C. Chanavat and A. Hadzihasanovic, *Model structures for diagrammatic `(∞, n)`-categories*,
  [arXiv:2410.19053](https://arxiv.org/abs/2410.19053).
- D.-C. Cisinski, *Les préfaisceaux comme modèles des types d'homotopie*, Astérisque 308, 2006.
- G. Maltsiniotis, *La théorie de l'homotopie de Grothendieck*, Astérisque 301, 2005.
- C. Berger and I. Moerdijk, *On an extension of the notion of Reedy category*,
  [arXiv:0809.3341](https://arxiv.org/abs/0809.3341).

## License

Apache-2.0; see `LICENSE`.
