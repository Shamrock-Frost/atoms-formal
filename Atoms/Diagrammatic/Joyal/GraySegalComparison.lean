import Atoms.Diagrammatic.MappingSpaceComparison
import Atoms.Diagrammatic.Joyal.GraySegal
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.SimplexFibre
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Product

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Simplicial
open Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

open SSet.modelCategoryJoyal

theorem weakEquivalence_toSSet_relativeMappingSpaceMapOfEq {V A X Y : DiagSet.{u}}
    (i : V ⟶ A) [Mono i] {f : V ⟶ X} {g : V ⟶ Y} (p : X ⟶ Y) (h : f ≫ p = g)
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    [WeakEquivalence ((DiagSet.toInfty 1).map p)] :
    WeakEquivalence (DiagSet.toSSet.map (relativeMappingSpaceMapOfEq i p h)) := by
  have : PreservesLimitsOfSize.{0, 0} DiagSet.toSSet.{u} :=
    sSetDiagSetAdj.rightAdjoint_preservesLimits
  have : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 X).2 hX
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 Y).2 hY
  have := fibration_toInfty_one_grayHomRestrict i hX
  have := fibration_toInfty_one_grayHomRestrict i hY
  have : Fibration (DiagSet.toSSet.map ((grayHomRestrict i).app X)) :=
    isQuillen_sSetDiagSetAdj.fibration_map
      ((DiagSet.toInfty 1).map ((grayHomRestrict i).app X))
  have : Fibration (DiagSet.toSSet.map ((grayHomRestrict i).app Y)) :=
    isQuillen_sSetDiagSetAdj.fibration_map
      ((DiagSet.toInfty 1).map ((grayHomRestrict i).app Y))
  have : IsFibrant ((DiagSet.toInfty 1).obj ((grayHomRight V).obj X)) :=
    (isFibrant_infty_iff 1 _).2 (isInftyCategory_grayHomRight _ hX)
  have : IsFibrant ((DiagSet.toInfty 1).obj ((grayHomRight V).obj Y)) :=
    (isFibrant_infty_iff 1 _).2 (isInftyCategory_grayHomRight _ hY)
  have : IsFibrant (DiagSet.toSSet.obj ((grayHomRight V).obj X)) :=
    isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj ((grayHomRight V).obj X))
  have : IsFibrant (DiagSet.toSSet.obj ((grayHomRight V).obj Y)) :=
    isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj ((grayHomRight V).obj Y))
  have : IsFibrant (DiagSet.toSSet.obj (ball.{u} Atoms.Shape.atomPoint)) :=
    (isFibrant_iff_of_isTerminal (𝟙 _) isTerminalToSSetBallAtomPoint).2 inferInstance
  have : WeakEquivalence (DiagSet.toSSet.map ((grayHomRight A).map p)) :=
    (isQuillen_sSetDiagSetAdj.comp
    (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one A)).weakEquivalence_map_of_isFibrant
      ((DiagSet.toInfty 1).map p)
  have : WeakEquivalence (DiagSet.toSSet.map ((grayHomRight V).map p)) :=
    (isQuillen_sSetDiagSetAdj.comp
    (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one V)).weakEquivalence_map_of_isFibrant
      ((DiagSet.toInfty 1).map p)
  exact (DiagSet.toSSet.map_isPullback (IsPullback.of_hasPullback
      ((grayHomRestrict i).app X) (diagramPoint f))).weakEquivalence_map_of_fibration
    (DiagSet.toSSet.map_isPullback (IsPullback.of_hasPullback
      ((grayHomRestrict i).app Y) (diagramPoint g)))
    (DiagSet.toSSet.map ((grayHomRight A).map p))
    (DiagSet.toSSet.map ((grayHomRight V).map p)) (𝟙 _)
    (DiagSet.toSSet.map (relativeMappingSpaceMapOfEq i p h))
    (by rw [← Functor.map_comp, ← Functor.map_comp, (grayHomRestrict i).naturality])
    (by rw [Category.id_comp, ← Functor.map_comp, diagramPoint_comp, h])
    (by rw [← Functor.map_comp, ← Functor.map_comp, relativeMappingSpaceMapOfEq_fst])
    (by
      rw [Category.comp_id, ← Functor.map_comp]
      exact congrArg DiagSet.toSSet.map
        ((pullback.lift_snd _ _ _).trans (Category.comp_id _)))

private theorem isFibrant_of_kanComplex (K : SSet.{u}) [K.KanComplex] : IsFibrant K :=
  (isFibrant_iff_quasicategory K).2 inferInstance

noncomputable def toSSetGraySpineFibreIso (X : DiagSet.{u}) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) :
    DiagSet.toSSet.obj (graySpineFibre X x) ≅
      ∏ᶜ fun i : Fin p => DiagSet.toSSet.obj
        (X.mappingSpace (x i.castSucc) (x i.succ)).toFunctor :=
  have : PreservesLimitsOfShape (Discrete (Fin p)) DiagSet.toSSet.{u} :=
    sSetDiagSetAdj.rightAdjoint_preservesLimits.preservesLimitsOfShape
  DiagSet.toSSet.mapIso (graySpineFibreIso X x) ≪≫ PreservesProduct.iso _ _

@[reassoc]
theorem toSSetGraySpineFibreIso_hom_π (X : DiagSet.{u}) {p : ℕ}
    (x : Fin (p + 1) → X.Vertex) (i : Fin p) :
    (toSSetGraySpineFibreIso X x).hom ≫ Pi.π _ i =
      DiagSet.toSSet.map ((graySpineFibreIso X x).hom ≫ Pi.π _ i) := by
  rw [toSSetGraySpineFibreIso, Iso.trans_hom, PreservesProduct.iso_hom,
    Category.assoc, piComparison_comp_π, Functor.mapIso_hom, ← Functor.map_comp]

@[reassoc]
theorem toSSet_map_graySpineFibreTwoIso_hom_prodComparison (X : DiagSet.{u})
    (x : Fin 3 → X.Vertex) :
    DiagSet.toSSet.map (graySpineFibreTwoIso X x).hom ≫ prodComparison DiagSet.toSSet
        (X.mappingSpace (x 0) (x 1)).toFunctor (X.mappingSpace (x 1) (x 2)).toFunctor =
      (toSSetGraySpineFibreIso X x).hom ≫ prod.lift (Pi.π _ 0) (Pi.π _ 1) := by
  apply prod.hom_ext
  · rw [Category.assoc, prodComparison_fst, ← Functor.map_comp, graySpineFibreTwoIso_hom]
    simp only [Category.assoc]
    exact (congrArg DiagSet.toSSet.map
      (congrArg ((graySpineFibreIso X x).hom ≫ ·) (prod.lift_fst _ _))).trans
      ((toSSetGraySpineFibreIso_hom_π X x 0).symm.trans
        (congrArg ((toSSetGraySpineFibreIso X x).hom ≫ ·) (prod.lift_fst _ _)).symm)
  · rw [Category.assoc, prodComparison_snd, ← Functor.map_comp, graySpineFibreTwoIso_hom]
    simp only [Category.assoc]
    exact (congrArg DiagSet.toSSet.map
      (congrArg ((graySpineFibreIso X x).hom ≫ ·) (prod.lift_snd _ _))).trans
      ((toSSetGraySpineFibreIso_hom_π X x 1).symm.trans
        (congrArg ((toSSetGraySpineFibreIso X x).hom ≫ ·) (prod.lift_snd _ _)).symm)

private theorem graySpineFibreComparison_positive {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {p : ℕ} (x : Fin (p + 2) → X.Vertex) :
    ∃ (Z : SSet.{u}) (l : Z ⟶ DiagSet.toSSet.obj (graySpineFibre X x))
      (r : Z ⟶ SSet.spineFibre (DiagSet.toSSet.obj X)
        (fun i => X.vertexEquivSSet (x i))),
      WeakEquivalence l ∧ WeakEquivalence r := by
  have : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 X).2 hX
  have : (DiagSet.toSSet.obj X).Quasicategory :=
    (isFibrant_iff_quasicategory _).1
      (isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj X))
  choose Z l r hZ hl hr using fun i : Fin (p + 1) =>
    mappingSpaceComparison_exists_joyal hX (x i.castSucc) (x i.succ)
  have : ∀ i, (Z i).KanComplex := hZ
  have : ∀ i, IsFibrant (Z i) := fun i => isFibrant_of_kanComplex _
  have : ∀ i : Fin (p + 1), IsFibrant
      (DiagSet.toSSet.obj (X.mappingSpace (x i.castSucc) (x i.succ)).toFunctor) := fun i =>
    have := kanComplex_toSSet_mappingSpace hX (x i.castSucc) (x i.succ)
    isFibrant_of_kanComplex _
  have : ∀ i : Fin (p + 1), IsFibrant
      (SSet.mappingSpace (DiagSet.toSSet.obj X)
        (X.vertexEquivSSet (x i.castSucc)) (X.vertexEquivSSet (x i.succ))) := fun i =>
    have := kanComplex_mappingSpace_toSSet_obj hX (x i.castSucc) (x i.succ)
    isFibrant_of_kanComplex _
  have : ∀ i, WeakEquivalence (l i) := hl
  have : ∀ i, WeakEquivalence (r i) := hr
  have := weakEquivalence_piMap l
  have := weakEquivalence_piMap r
  exact ⟨∏ᶜ Z, Limits.Pi.map l ≫ (toSSetGraySpineFibreIso X x).inv,
    Limits.Pi.map r ≫
      (SSet.simplexFibreSpineIso _ (fun i => X.vertexEquivSSet (x i))).inv,
    inferInstance, inferInstance⟩

noncomputable def isTerminalToSSetGraySpineFibreZero (X : DiagSet.{u})
    (x : Fin 1 → X.Vertex) : IsTerminal (DiagSet.toSSet.obj (graySpineFibre X x)) := by
  let e := toSSetGraySpineFibreIso X x
  apply IsTerminal.ofUniqueHom (fun T => Pi.lift (fun i : Fin 0 => Fin.elim0 i) ≫ e.inv)
  intro T f
  apply (cancel_mono e.hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact Pi.hom_ext _ _ fun i => Fin.elim0 i

theorem graySpineFibreComparison_exists {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {p : ℕ} (x : Fin (p + 1) → X.Vertex) :
    ∃ (Z : SSet.{u}) (l : Z ⟶ DiagSet.toSSet.obj (graySpineFibre X x))
      (r : Z ⟶ SSet.spineFibre (DiagSet.toSSet.obj X)
        (fun i => X.vertexEquivSSet (x i))),
      WeakEquivalence l ∧ WeakEquivalence r := by
  cases p with
  | zero =>
    have hK : IsTerminal (SSet.spineSubcomplex.{u} 0 : SSet.{u}) :=
      SSet.stdSimplex.isTerminalObj₀.ofIso (SSet.Subcomplex.topIso _).symm
    let e := (isTerminalToSSetGraySpineFibreZero X x).uniqueUpToIso
      (SSet.isTerminalIhomFibreOfIsTerminal hK (SSet.spineSubcomplex.spineId 0).vertex
        _ (fun i => X.vertexEquivSSet (x i)))
    exact ⟨_, 𝟙 _, e.hom, inferInstance, inferInstance⟩
  | succ p => exact graySpineFibreComparison_positive hX x

theorem trivialFibration_toSSet_map_graySegalMap {X : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) {p : ℕ} (x : Fin (p + 1) → X.Vertex) :
    trivialFibrations SSet.{u} (DiagSet.toSSet.map (graySegalMap X x)) := by
  rw [← cofibrations_rlp]
  change (monomorphisms SSet.{u}).rlp _
  intro A B i hi
  rw [← sSetDiagSetAdj.hasLiftingProperty_iff]
  exact rlp_monomorphisms_graySegalMap hX x _
    (monomorphisms.infer_property (SSet.toDiagSet.map i))

theorem graySegalComparison_exists {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {p : ℕ} (x : Fin (p + 1) → X.Vertex) :
    ∃ (Z : SSet.{u}) (l : Z ⟶ DiagSet.toSSet.obj (graySpineFibre X x))
      (r : Z ⟶ SSet.spineFibre (DiagSet.toSSet.obj X)
        (fun i => X.vertexEquivSSet (x i))),
      WeakEquivalence l ∧ WeakEquivalence r ∧
        Nonempty (ArrowSpanComparison (DiagSet.toSSet.map (graySegalMap X x))
          (SSet.simplexFibreSegalMap _ (fun i => X.vertexEquivSSet (x i))) l r) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 X).2 hX
  have : (DiagSet.toSSet.obj X).Quasicategory :=
    (isFibrant_iff_quasicategory _).1
      (isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj X))
  obtain ⟨Z, l, r, hl, hr⟩ := graySpineFibreComparison_exists hX x
  have : WeakEquivalence l := hl
  have : WeakEquivalence r := hr
  obtain ⟨ha, hw⟩ := (mem_trivialFibrations_iff _).1
    (trivialFibration_toSSet_map_graySegalMap hX x)
  have : Fibration (DiagSet.toSSet.map (graySegalMap X x)) := ha
  have : WeakEquivalence (DiagSet.toSSet.map (graySegalMap X x)) := hw
  have hs : trivialFibrations SSet.{u}
      (SSet.simplexFibreSegalMap _ (fun i => X.vertexEquivSSet (x i))) := by
    rw [← cofibrations_rlp]
    change (monomorphisms SSet.{u}).rlp _
    rw [SSet.rlp_monomorphisms]
    exact SSet.rlp_I_simplexFibreSegalMap _ _
  obtain ⟨hsf, hsw⟩ := (mem_trivialFibrations_iff _).1 hs
  have := hsf
  have := hsw
  exact ⟨Z, l, r, hl, hr, ⟨arrowSpanComparisonOfTrivialFibrations _ _ l r⟩⟩

theorem graySimplexFibreComparison_exists {X : DiagSet.{u}} (hX : IsInftyCategory 1 X)
    {p : ℕ} (x : Fin (p + 1) → X.Vertex) :
    ∃ (Z : SSet.{u}) (l : Z ⟶ DiagSet.toSSet.obj (graySimplexFibre X x))
      (r : Z ⟶ SSet.simplexFibre (DiagSet.toSSet.obj X)
        (fun i => X.vertexEquivSSet (x i))),
      WeakEquivalence l ∧ WeakEquivalence r := by
  obtain ⟨Z, l, r, hl, hr, ⟨e⟩⟩ := graySegalComparison_exists hX x
  exact ⟨e.total, e.left, e.right, e.weakEquivalence_left, e.weakEquivalence_right⟩

end Atoms.Diagrammatic
