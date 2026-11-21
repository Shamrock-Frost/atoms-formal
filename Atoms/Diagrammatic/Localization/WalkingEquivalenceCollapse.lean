import Atoms.Diagrammatic.AtomTest
import Atoms.Diagrammatic.Horn.Localizer
import Atoms.Diagrammatic.Joyal.GrayCylinderModel
import Atoms.Diagrammatic.KanComparison
import Atoms.Diagrammatic.Localization.ModelStructure
import Atoms.Diagrammatic.Localization.WalkingEquivalenceLift
import Atoms.Molecule.MoleculeShape.AtomBoundaryIso
import Atoms.Molecule.MoleculeShape.PartialCylinder
import Atoms.Shape.Join

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

theorem weakEquivalence_walkingEquivalenceLift_toMerger (n : ℕ∞) (U : RoundShape)
    (hU : 0 < U.dimension) {W : Atom} (p : toMergerAtom U hU ⟶ W)
    (hW : W.dimension < (toMergerAtom U hU).dimension)
    (hp : IsIso (toMergerInclusion.{u} U hU ≫ uliftYoneda.{u}.map p)) :
    WeakEquivalence ((DiagSet.toInfty n).map
      (walkingEquivalenceLift.{u} (pos_dimension_toMergerAtom U hU) p hW)) := by
  have hι : WeakEquivalence ((DiagSet.toInfty n).map (toMergerInclusion.{u} U hU ≫
      toWalkingEquivalence (toMergerAtom U hU) (pos_dimension_toMergerAtom U hU))) :=
    weakEquivalence_toInfty_map_of_mem_inftyGenerators n
      (Or.inl ⟨(⟨U, hU⟩ : {U : RoundShape // 0 < U.dimension})⟩)
  have hc : WeakEquivalence ((DiagSet.toInfty n).map ((toMergerInclusion.{u} U hU ≫
      toWalkingEquivalence (toMergerAtom U hU) (pos_dimension_toMergerAtom U hU)) ≫
      walkingEquivalenceLift (pos_dimension_toMergerAtom U hU) p hW)) := by
    rw [Category.assoc, toWalkingEquivalence_walkingEquivalenceLift]
    have : IsIso ((DiagSet.toInfty n).map (toMergerInclusion.{u} U hU ≫ uliftYoneda.{u}.map p)) :=
      hp
    infer_instance
  rw [Functor.map_comp] at hc
  exact weakEquivalence_of_precomp ((DiagSet.toInfty n).map (toMergerInclusion.{u} U hU ≫
    toWalkingEquivalence (toMergerAtom U hU) (pos_dimension_toMergerAtom U hU)))
    ((DiagSet.toInfty n).map (walkingEquivalenceLift (pos_dimension_toMergerAtom U hU) p hW))

theorem exists_weakEquivalence_walkingEquivalence_collapse (n : ℕ∞) (U : Atom)
    (hU : 0 < U.dimension) :
    ∃ (p : toMergerAtom U.toRoundShape hU ⟶ U)
      (hW : U.dimension < (toMergerAtom U.toRoundShape hU).dimension),
      IsIso (toMergerInclusion.{u} U.toRoundShape hU ≫ uliftYoneda.{u}.map p) ∧
      WeakEquivalence ((DiagSet.toInfty n).map
        (walkingEquivalenceLift.{u} (pos_dimension_toMergerAtom U.toRoundShape hU) p hW)) := by
  have hR : 0 < U.toRoundShape.dimension := hU
  let M := toMergerAtom U.toRoundShape hR
  let C := unitShape U.toMoleculeShape
  have hd : U.toRoundShape.dimension = (U.dimension - 1) + 1 := (Nat.sub_add_cancel hU).symm
  have hdC : C.dimension = U.dimension + 1 := dimension_cylShape U.toMoleculeShape _
    (exists_notMem_bdryFull_grade_eq U.isMolecule U.toMoleculeShape.krullDim_eq_dimension)
  have hbC (α : Bool) : C.ogp.boundary ⊤ U.dimension α = C.ogp.bdry ⊤ α :=
    (bdry_eq_boundary (C.krullDim_top_eq hdC) α).symm
  obtain ⟨Θ⟩ := MoleculeShape.nonempty_iso_of_boundary_iso M.toMoleculeShape C
    (fun α => (nonempty_iso_boundary_toMergerAtom U hR α).some ≪≫
      (C.bdryIso hdC α ≪≫ (isoRestrictOfFintype
        (cylEndpoint U.toMoleculeShape (U.ogp.bdryFull ⊤) α)
        ((map_cylEndpoint_bdryFull_top U.toMoleculeShape α).trans (hbC α))).symm).symm)
    M.isAtom (isAtom_unitShape U) (dimension_toMergerAtom U.toRoundShape hR) hdC
  let p : M ⟶ U := InducedCategory.homMk ((RDCpx.isoOfIso (P := M.rdc) (Q := C.rdc) Θ).hom ≫
    cylProj U.toMoleculeShape (U.ogp.bdryFull ⊤))
  have hW : U.dimension < M.dimension := by
    rw [dimension_toMergerAtom U.toRoundShape hR]
    exact Nat.lt_succ_self _
  have hI : IsInclusion (P := U.ogp) (Q := M.ogp) (toMergerInputIncl U.toRoundShape hR) :=
    inferInstanceAs (IsInclusion (toMergerInputIncl U.toRoundShape hR))
  have hΘ : IsInclusion (P := U.ogp) (toMergerInputIncl U.toRoundShape hR ≫ Θ.hom) :=
    IsInclusion.comp _ _
  have himg₀ : map (toMergerInputIncl U.toRoundShape hR) ⊤ = M.ogp.bdry ⊤ false :=
    U.toRoundShape.map_inputIncl hd
  have himg : map (P := U.ogp) (toMergerInputIncl U.toRoundShape hR ≫ Θ.hom) ⊤ =
      map (cylEndpoint U.toMoleculeShape (U.ogp.bdryFull ⊤) false) ⊤ := by
    refine (map_comp (toMergerInputIncl U.toRoundShape hR) Θ.hom ⊤).trans ?_
    rw [himg₀, map_bdry, map_top_of_isIso, map_cylEndpoint_bdryFull_top]
    exact (hbC false).symm
  have hpe : RDCpx.ofInclusion (P := atomToRDCpx.obj U) (Q := atomToRDCpx.obj M)
      (toMergerInputIncl U.toRoundShape hR) ≫ atomToRDCpx.map p = 𝟙 (atomToRDCpx.obj U) := by
    ext x
    exact (congrArg (ConcreteCategory.hom (cylProj U.toMoleculeShape (U.ogp.bdryFull ⊤)).hom)
      (IsMoleculeIn.eqOn_of_map_eq (P := U.ogp) (toMergerInputIncl U.toRoundShape hR ≫ Θ.hom)
        (cylEndpoint U.toMoleculeShape (U.ogp.bdryFull ⊤) false) U.isMolecule himg
        (LowerSet.mem_top (a := x)))).trans (cylProj_cylEndpoint U.toMoleculeShape _ false x)
  have hnat : (realizeAtomIso.{u} M).hom ≫ uliftYoneda.{u}.map p =
      realize.{u}.map (atomToRDCpx.map p) ≫ (realizeAtomIso U).hom := by
    ext T c
    rfl
  have e : (toMergerInclusion.{u} U.toRoundShape hR ≫ uliftYoneda.{u}.map p :
      realize.{u}.obj (atomToRDCpx.obj U) ⟶ ball.{u} U) = (realizeAtomIso U).hom := by
    change (realize.map (RDCpx.ofInclusion (P := atomToRDCpx.obj U) (Q := atomToRDCpx.obj M)
      (toMergerInputIncl U.toRoundShape hR)) ≫ (realizeAtomIso M).hom) ≫ uliftYoneda.map p = _
    rw [Category.assoc, hnat, ← realize.map_comp_assoc, hpe, realize.map_id, Category.id_comp]
  have hp : IsIso (toMergerInclusion.{u} U.toRoundShape hR ≫ uliftYoneda.{u}.map p) :=
    Eq.mpr (congrArg (fun f => IsIso f) e) (Iso.isIso_hom (realizeAtomIso.{u} U))
  exact ⟨p, hW, hp, weakEquivalence_walkingEquivalenceLift_toMerger n U.toRoundShape hR p hW hp⟩

theorem weakEquivalence_walkingEquivalence_arrow_toTerminal (n : ℕ∞) (A : Atom)
    (hA : A.dimension = 1) :
    WeakEquivalence ((DiagSet.toInfty n).map
      (terminal.from (walkingEquivalence.{u} A (by omega)))) := by
  obtain ⟨e⟩ := nonempty_iso_atomGlobe_of_dimension_eq_one hA
  have hA' : 0 < A.dimension := by omega
  have hG : 0 < (atomGlobe 1).dimension := (dimension_atomGlobe 1).symm ▸ Nat.one_pos
  have hφ : IsIso (walkingEquivalenceMap.{u} hG hA' e.symm) :=
    (walkingEquivalenceIso hG hA' e.symm).isIso_hom
  have h : WeakEquivalence ((DiagSet.toInfty n).map
      (isTerminalBallAtomPoint.from (walkingEquivalence.{u} (atomGlobe 1) hG))) :=
    DiagSet.Infty.weakEquivalence_toInfty_reversibleArrow_from n
  have : IsIso (terminal.from (ball.{u} atomPoint)) :=
    isIso_of_isTerminal isTerminalBallAtomPoint terminalIsTerminal _
  rw [← terminal.comp_from (walkingEquivalenceMap.{u} hG hA' e.symm ≫
    isTerminalBallAtomPoint.from (walkingEquivalence.{u} (atomGlobe 1) hG)), Functor.map_comp,
    Functor.map_comp]
  infer_instance

theorem weakEquivalence_walkingEquivalence_toTerminal (U : Atom) (hU : 0 < U.dimension) :
    WeakEquivalence ((DiagSet.toInfty 0).map (terminal.from (walkingEquivalence.{u} U hU))) := by
  have h₁ : WeakEquivalence ((DiagSet.toInfty 0).map (toWalkingEquivalence.{u} U hU)) :=
    weakEquivalence_toInfty_map_of_mem_inftyGenerators 0
      (Or.inr ⟨(⟨U, by exact_mod_cast hU⟩ : {U : Atom // (0 : ℕ∞) < U.dimension})⟩)
  have h₂ : WeakEquivalence ((DiagSet.toInfty 0).map (terminal.from (ball.{u} U))) := by
    have : IsIso (terminal.from (ball.{u} atomPoint)) :=
      isIso_of_isTerminal isTerminalBallAtomPoint terminalIsTerminal _
    have h : reversibleCylinder.{u}.weakEquivalences (inftyGenerators 0)
        (uliftYoneda.{u}.map (toAtomPoint U)) := by
      rw [weakEquivalences_infty_zero_eq_hornWeak]
      exact hornWeak_uliftYoneda_map _
    have : WeakEquivalence ((DiagSet.toInfty 0).map (uliftYoneda.{u}.map (toAtomPoint U))) :=
      (weakEquivalence_iff _).2 h
    rw [← terminal.comp_from (uliftYoneda.{u}.map (toAtomPoint U)), Functor.map_comp]
    infer_instance
  rw [← terminal.comp_from (toWalkingEquivalence.{u} U hU), Functor.map_comp] at h₂
  exact weakEquivalence_of_precomp ((DiagSet.toInfty 0).map (toWalkingEquivalence.{u} U hU))
    ((DiagSet.toInfty 0).map (terminal.from (walkingEquivalence.{u} U hU)))

end Atoms.Diagrammatic
