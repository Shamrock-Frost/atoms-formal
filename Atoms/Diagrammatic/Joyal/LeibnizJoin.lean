import Atoms.Diagrammatic.JoinClosedSubpresheaf
import Atoms.Diagrammatic.Joyal.JoinBox

open CategoryTheory CategoryTheory.WithInitial Limits MorphismProperty HomotopicalAlgebra
  Atoms.Shape Atoms.Molecule Atoms.Molecule.OGP

universe u

namespace Atoms.Diagrammatic

open scoped DiagSet.Join

section Realized

variable (U V : Atom)

private theorem mem_closedJoin_ofOGPIso_hom {A : LowerSet U.ogp} {B : LowerSet V.ogp}
    (p : join U.ogp V.ogp) :
    (FiniteOGP.ofOGPIso (join U.ogp V.ogp)).hom p ∈ closedJoin A B ↔
      p ∈ MoleculeShape.joinPair U.toMoleculeShape V.isMolecule A B := by
  have h := Iso.hom_inv_id_apply (FiniteOGP.ofOGPIso (join U.ogp V.ogp)) p
  change (∀ a : U.ogp, joinBotFst (WithBot.some ((FiniteOGP.ofOGPIso (join U.ogp V.ogp)).inv
      ((FiniteOGP.ofOGPIso (join U.ogp V.ogp)).hom p))) = a → a ∈ A) ∧
    (∀ b : V.ogp, joinBotSnd (WithBot.some ((FiniteOGP.ofOGPIso (join U.ogp V.ogp)).inv
      ((FiniteOGP.ofOGPIso (join U.ogp V.ogp)).hom p))) = b → b ∈ B) ↔ _
  rw [h]
  exact Iff.rfl

private noncomputable def leibnizJoinBoxArrowIso {A : LowerSet U.ogp} {B B' : LowerSet V.ogp}
    (hB : B ≤ B') :
    Arrow.mk (leibnizJoinBox.{u} U.toMoleculeShape V.isMolecule A ⊤ B B') ≅
      Arrow.mk (Subfunctor.homOfLe (closedSubpresheaf_mono.{u} (atomJoin U V)
        (sup_le (closedJoin_mono le_rfl hB) (closedJoin_mono le_top le_rfl) :
          closedJoin ⊤ B ⊔ closedJoin A B' ≤ closedJoin ⊤ B'))) :=
  Arrow.isoMk
    (realizeRestrictIsoOfIso _ (atomJoin U V) (FiniteOGP.ofOGPIso (join U.ogp V.ogp)) _ _
      fun p => LowerSet.mem_sup_iff.trans <| (or_congr (mem_closedJoin_ofOGPIso_hom U V p)
        (mem_closedJoin_ofOGPIso_hom (A := A) U V p)).trans (SetLike.ext_iff.1 (inf_eq_right.2
          (sup_le (MoleculeShape.joinPair_mono _ _ le_rfl hB)
            (MoleculeShape.joinPair_mono _ _ le_top le_rfl))).symm p))
    (realizeRestrictIsoOfIso _ (atomJoin U V) (FiniteOGP.ofOGPIso (join U.ogp V.ogp)) _ _
      fun p => mem_closedJoin_ofOGPIso_hom U V p) (by
    ext T g
    rfl)

private noncomputable def sphereInclusionArrowIsoHomOfLe (V : Atom) :
    Arrow.mk (sphereInclusion.{u} V) ≅
      Arrow.mk (Subfunctor.homOfLe (closedSubpresheaf_mono.{u} V
        (le_top : V.ogp.bdryFull ⊤ ≤ ⊤))) :=
  have h : Arrow.mk (closedSubpresheaf.{u} V (V.ogp.bdryFull ⊤)).ι =
      Arrow.mk (sphereInclusion.{u} V) := by
    rw [closedSubpresheaf_univ_erase_top]
    rfl
  eqToIso h.symm ≪≫ (homOfLeUnivArrowIso V _).symm

end Realized

private theorem markedAbove_pushoutObjObj_ι_of_leibnizJoinBox (n : ℕ∞) (U V : Atom)
    (A : LowerSet U.ogp) {B B' : LowerSet V.ogp} (hB : B ≤ B')
    (h : WeakEquivalence ((MarkedDiagSet.toCoinductive n).map
      ((MarkedDiagSet.markedAboveFunctor 1).map
        (leibnizJoinBox.{u} U.toMoleculeShape V.isMolecule A ⊤ B B')))) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map ((MarkedDiagSet.markedAboveFunctor 1).map
      (Functor.PushoutObjObj.ofHasPushout 𝒥 (closedSubpresheaf.{u} U A).ι
        (Subfunctor.homOfLe (closedSubpresheaf_mono.{u} V hB))).ι)) := by
  refine (weakEquivalence_coinductive_iff n _).2 ?_
  have := MorphismProperty.respectsIso_of_isStableUnderComposition
    (markedExactCylinder.isomorphisms_le_weakEquivalences (coinductiveGenerators n))
  let E := leibnizJoinBoxArrowIso.{u} U V (A := A) hB ≪≫
    (pushoutObjObjClosedSubpresheafArrowIso le_top hB).symm ≪≫
    Functor.PushoutObjObj.ι_iso_of_iso_left (f₂ := Arrow.mk (Subfunctor.homOfLe
      (closedSubpresheaf_mono.{u} V hB))) _ (Functor.PushoutObjObj.ofHasPushout 𝒥 _ _)
      (homOfLeUnivArrowIso U _)
  exact ((markedExactCylinder.{u}.weakEquivalences _).arrow_mk_iso_iff
    ((MarkedDiagSet.markedAboveFunctor 1).mapArrow.mapIso E)).1
    ((weakEquivalence_coinductive_iff n _).1 h)

private theorem markedAbove_pushoutObjObj_ι_sphereInclusion_of_homOfLe
    (n : ℕ∞) (U V : Atom) (A : LowerSet U.ogp)
    (h : WeakEquivalence ((MarkedDiagSet.toCoinductive n).map
      ((MarkedDiagSet.markedAboveFunctor 1).map
        (Functor.PushoutObjObj.ofHasPushout 𝒥 (closedSubpresheaf.{u} U A).ι
          (Subfunctor.homOfLe (closedSubpresheaf_mono.{u} V
            (le_top : V.ogp.bdryFull ⊤ ≤ ⊤)))).ι))) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map ((MarkedDiagSet.markedAboveFunctor 1).map
      (Functor.PushoutObjObj.ofHasPushout 𝒥 (closedSubpresheaf.{u} U A).ι
        (sphereInclusion.{u} V)).ι)) := by
  refine (weakEquivalence_coinductive_iff n _).2 ?_
  have := MorphismProperty.respectsIso_of_isStableUnderComposition
    (markedExactCylinder.isomorphisms_le_weakEquivalences (coinductiveGenerators n))
  exact ((markedExactCylinder.{u}.weakEquivalences _).arrow_mk_iso_iff
    ((MarkedDiagSet.markedAboveFunctor 1).mapArrow.mapIso
      (Functor.PushoutObjObj.ι_iso_of_iso_right
        (f₁ := Arrow.mk (closedSubpresheaf.{u} U A).ι)
        (Functor.PushoutObjObj.ofHasPushout 𝒥 _ (sphereInclusion.{u} V))
        (Functor.PushoutObjObj.ofHasPushout 𝒥 _ _) (sphereInclusionArrowIsoHomOfLe V)))).2
    ((weakEquivalence_coinductive_iff n _).1 h)

theorem weakEquivalence_markedAboveFunctor_map_pushoutObjObj_ι_boundary (n : ℕ∞) (U V : Atom)
    {B B' : LowerSet V.ogp} (hB : B ≤ B') (k : ℕ) (α : Bool) (hα : α = true ∨ 1 ≤ k) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map ((MarkedDiagSet.markedAboveFunctor 1).map
      (Functor.PushoutObjObj.ofHasPushout 𝒥 (closedSubpresheaf.{u} U (U.ogp.boundary ⊤ k α)).ι
        (Subfunctor.homOfLe (closedSubpresheaf_mono.{u} V hB))).ι)) :=
  markedAbove_pushoutObjObj_ι_of_leibnizJoinBox n U V _ hB
    (weakEquivalence_markedAboveFunctor_map_leibnizJoinBox_boundary n U.toMoleculeShape
      V.isMolecule hB k α hα)

theorem weakEquivalence_markedAboveFunctor_map_pushoutObjObj_ι_sphereInclusion (n : ℕ∞)
    (U V : Atom) (k : ℕ) (α : Bool) (hα : α = true ∨ 1 ≤ k) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map ((MarkedDiagSet.markedAboveFunctor 1).map
      (Functor.PushoutObjObj.ofHasPushout 𝒥 (closedSubpresheaf.{u} U (U.ogp.boundary ⊤ k α)).ι
        (sphereInclusion.{u} V)).ι)) :=
  markedAbove_pushoutObjObj_ι_sphereInclusion_of_homOfLe n U V _
    (weakEquivalence_markedAboveFunctor_map_pushoutObjObj_ι_boundary n U V le_top k α hα)

private theorem erase_erase_Iic_top_eq_hornSubset (U : Atom) (x : U.ogp) (hx : x ⋖ U.top) :
    ((LowerSet.Iic U.top).erase U.top).erase x =
      hornSubset (atomicHornDataOfCovBy U x hx).toHornData := by
  have h (y : U.ogp) : y ∈ ((LowerSet.Iic U.top).erase U.top).erase x ↔ y ≠ U.top ∧ y ≠ x := by
    simp only [← SetLike.mem_coe, LowerSet.coe_erase, LowerSet.coe_Iic, UpperSet.coe_Ici,
      Set.mem_sdiff, Set.mem_Iic, Set.mem_Ici]
    refine ⟨fun ⟨⟨_, hty⟩, hxy⟩ => ⟨fun h => hty h.ge, fun h => hxy h.ge⟩,
      fun ⟨hyt, hyx⟩ => ⟨⟨U.le_top y, fun h => hyt (le_antisymm (U.le_top y) h)⟩, fun h => ?_⟩⟩
    exact hyx ((hx.eq_or_eq h (U.le_top y)).resolve_right hyt)
  exact SetLike.ext fun y => (h y).trans (mem_hornSet_closure_singleton_iff
    (atomicHornDataOfCovBy U x hx).toHornData (x := x) (z := y) rfl).symm

theorem weakEquivalence_markedAboveFunctor_map_pushoutObjObj_ι_atomicHorn (n : ℕ∞) (U : Atom)
    (x : U.ogp) (hx : x ⋖ U.top)
    (hs : U.ogp.boundary (LowerSet.Iic x) 0 false = U.ogp.boundary ⊤ 0 false) (V : Atom) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map ((MarkedDiagSet.markedAboveFunctor 1).map
      (Functor.PushoutObjObj.ofHasPushout 𝒥
        (hornInclusion.{u} (atomicHornDataOfCovBy U x hx).toHornData)
        (sphereInclusion.{u} V)).ι)) := by
  have h := weakEquivalence_markedAboveFunctor_map_leibnizJoinBox_horn.{u} n U.toMoleculeShape hx
    (by rw [U.Iic_top]; exact hs) V.isMolecule (le_top : V.ogp.bdryFull ⊤ ≤ ⊤)
  rw [erase_erase_Iic_top_eq_hornSubset U x hx, U.Iic_top] at h
  exact markedAbove_pushoutObjObj_ι_sphereInclusion_of_homOfLe n U V _
    (markedAbove_pushoutObjObj_ι_of_leibnizJoinBox n U V _ le_top h)

end Atoms.Diagrammatic
