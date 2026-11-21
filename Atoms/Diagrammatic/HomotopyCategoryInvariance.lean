import Atoms.Diagrammatic.FullyFaithful
import Atoms.Diagrammatic.Localization.InftyWeakEquivalence

open CategoryTheory Limits Simplicial HomotopicalAlgebra
open Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

theorem DiagSet.faithful_homotopyFunctor (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (F : X ⟶ Y) [WeakEquivalence ((DiagSet.toInfty 1).map F)] :
    (homotopyFunctor hX.1 hY.1 F).Faithful := by
  have : Fibration ((DiagSet.toInfty 1).map (reversibleMappingPathSpaceProj F)) :=
    fibration_reversibleMappingPathSpaceProj F 1 hX hY
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 Y).2 hY
  have : IsFibrant ((DiagSet.toInfty 1).obj (reversibleMappingPathSpace F)) :=
    isFibrant_of_fibration ((DiagSet.toInfty 1).map (reversibleMappingPathSpaceProj F))
  have hP : IsInftyCategory 1 (reversibleMappingPathSpace F) := (isFibrant_infty_iff 1 _).1 this
  have : (homotopyFunctor hX.1 hP.1 (reversibleMappingPathSpaceIncl F)).Faithful :=
    Functor.Faithful.of_comp_eq (G := homotopyFunctor hP.1 hX.1 (pullback.fst _ _))
      (H := 𝟭 _) (by rw [← homotopyFunctor_comp, reversibleMappingPathSpaceIncl_fst,
        homotopyFunctor_id])
  have : (homotopyFunctor hP.1 hY.1 (reversibleMappingPathSpaceProj F)).Faithful := by
    refine ⟨fun {a b} φ ψ hφψ => ?_⟩
    obtain ⟨a⟩ := a
    obtain ⟨b⟩ := b
    obtain ⟨f, rfl⟩ := HomotopyCategory.homMk_surjective hP.1 φ
    obtain ⟨g, rfl⟩ := HomotopyCategory.homMk_surjective hP.1 ψ
    rw [homotopyFunctor_map_homMk, homotopyFunctor_map_homMk] at hφψ
    replace hφψ := (HomotopyCategory.homMk_eq_homMk_iff hY.1 _ _).1 hφψ
    rw [HomotopyCategory.homMk_eq_homMk_iff]
    have hmap (e : DiagSet.Edge _ a b) :
        cellRound (e.map (reversibleMappingPathSpaceProj F)).cell =
          (cellRound e.cell).mapTo (reversibleMappingPathSpaceProj F) :=
      RoundPastingDiagram.ext (PastingDiagram.ofCell_app (reversibleMappingPathSpaceProj F) e.cell)
    rw [hmap, hmap] at hφψ
    exact equivalent_of_rlp_monomorphisms
      (rlp_monomorphisms_reversibleMappingPathSpaceProj F 1 hX hY) hY.1
      ((hasBdry_ofCell_edge f).parallel (hasBdry_ofCell_edge g) (.refl _) (.refl _) _ _) hφψ
  have hfac : homotopyFunctor hX.1 hY.1 F = homotopyFunctor hX.1 hP.1
      (reversibleMappingPathSpaceIncl F) ⋙ homotopyFunctor hP.1 hY.1
        (reversibleMappingPathSpaceProj F) := by
    rw [← homotopyFunctor_comp, reversibleMappingPathSpaceIncl_proj]
  rw [hfac]
  infer_instance

theorem DiagSet.exists_isEquivalence_edge_map (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (F : X ⟶ Y) [WeakEquivalence ((DiagSet.toInfty 1).map F)]
    (y : Y.Vertex) :
    ∃ (x : X.Vertex) (e : Y.Edge (x.map F) y), IsEquivalence Y e.cell := by
  have hω := (weakEquivalence_iff_isOmegaEquivalence F 1 hX hY).1 inferInstance
  obtain ⟨x, hx⟩ := hω.exists_equivalent_of_dimension_eq_zero atomPoint dimension_atomPoint y
  obtain ⟨U, c, hc, hU, hs, ht⟩ := exists_equivalence_cell_side hY.1 true _ _ hx
  have hd : (cellRound y).dim = 0 := dimension_atomPoint
  rw [hd] at hU hs ht
  obtain ⟨e, he⟩ := exists_edge_equivalent_of_hasBdry hY.1 (cellRound c)
    (x := DiagSet.Vertex.map F x) (z := y)
    ⟨hU, dimension_atomPoint, dimension_atomPoint, ht, hs⟩
  refine ⟨x, e, ?_⟩
  exact (mem_equivalences_iff_of_equivalent he).1 hc

theorem DiagSet.essSurj_homotopyFunctor (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (F : X ⟶ Y) [WeakEquivalence ((DiagSet.toInfty 1).map F)] :
    (homotopyFunctor hX.1 hY.1 F).EssSurj :=
  (DiagSet.isEssentiallySurjective_iff_essSurj hX hY F).1
    (DiagSet.exists_isEquivalence_edge_map hX hY F)

theorem DiagSet.isEquivalence_homotopyFunctor_of_weakEquivalence (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (F : X ⟶ Y) [WeakEquivalence ((DiagSet.toInfty 1).map F)] :
    (homotopyFunctor hX.1 hY.1 F).IsEquivalence :=
  DiagSet.isEquivalence_homotopyFunctor hX hY (DiagSet.isFullyFaithful_of_weakEquivalence hX hY F)
    (DiagSet.exists_isEquivalence_edge_map hX hY F)

noncomputable def DiagSet.homotopyCategoryEquivalenceOfWeakEquivalence
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) (F : X ⟶ Y)
    [WeakEquivalence ((DiagSet.toInfty 1).map F)] :
    HomotopyCategory X hX.1 ≌ HomotopyCategory Y hY.1 :=
  @Functor.asEquivalence _ _ _ _ (homotopyFunctor hX.1 hY.1 F)
    (DiagSet.isEquivalence_homotopyFunctor_of_weakEquivalence hX hY F)

theorem DiagSet.homotopyCategoryEquivalenceOfWeakEquivalence_functor
    (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y) (F : X ⟶ Y)
    [WeakEquivalence ((DiagSet.toInfty 1).map F)] :
    (DiagSet.homotopyCategoryEquivalenceOfWeakEquivalence hX hY F).functor =
      homotopyFunctor hX.1 hY.1 F :=
  rfl

theorem homotopyCategoryEquivalence_inverse_comp_homotopyFunctor (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (F : X ⟶ Y) :
    (homotopyCategoryEquivalence hX).inverse ⋙ homotopyFunctor hX.1 hY.1 F =
      (SSet.hoFunctor.map (DiagSet.toSSet.map F)).toFunctor ⋙
        (homotopyCategoryEquivalence hY).inverse :=
  SSet.Truncated.HomotopyCategory.functor_ext (fun _ => rfl) fun _ _ e => by
    refine ((congrArg (homotopyFunctor hX.1 hY.1 F).map
      (homotopyCategoryEquivalence_inverse_map_homMk hX (SSet.Edge.ofTruncated e))).trans
        ?_).trans (Category.id_comp _).symm
    refine (homotopyFunctor_map_homMk hX.1 hY.1 F _).trans ?_
    refine (congrArg (HomotopyCategory.homMk hY.1)
      (DiagSet.edgeEquivSSet_symm_map (SSet.Edge.ofTruncated e) F).symm).trans ?_
    exact (homotopyCategoryEquivalence_inverse_map_homMk hY
      ((SSet.Edge.ofTruncated e).map (DiagSet.toSSet.map F))).symm.trans
        (Category.comp_id _).symm

theorem DiagSet.isEquivalence_hoFunctor_map (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (F : X ⟶ Y) [WeakEquivalence ((DiagSet.toInfty 1).map F)] :
    (SSet.hoFunctor.map (DiagSet.toSSet.map F)).toFunctor.IsEquivalence := by
  have := DiagSet.isEquivalence_homotopyFunctor_of_weakEquivalence hX hY F
  have : ((SSet.hoFunctor.map (DiagSet.toSSet.map F)).toFunctor ⋙
      (homotopyCategoryEquivalence hY).inverse).IsEquivalence := by
    rw [← homotopyCategoryEquivalence_inverse_comp_homotopyFunctor hX hY F]
    infer_instance
  exact Functor.isEquivalence_of_comp_right _ (homotopyCategoryEquivalence hY).inverse

end Atoms.Diagrammatic
