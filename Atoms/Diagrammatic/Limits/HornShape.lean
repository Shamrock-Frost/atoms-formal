import Atoms.Diagrammatic.Limits.ProductPullback

open CategoryTheory Limits Opposite Simplicial Atoms.Shape SSet

universe u

namespace Atoms.Diagrammatic

@[reassoc]
theorem toDiagSet_map_stdSimplex_δ_zero :
    SSet.toDiagSet.{u}.map (stdSimplex.δ (0 : Fin 2)) ≫ (toDiagSetObjStdSimplexIso 1).hom =
      (toDiagSetObjStdSimplexIso 0).hom ≫ intervalTarget.{u} :=
  stdSimplexCompToDiagSetIso.hom.naturality (SimplexCategory.δ 0)

@[reassoc]
theorem toDiagSet_map_stdSimplex_δ_one :
    SSet.toDiagSet.{u}.map (stdSimplex.δ (1 : Fin 2)) ≫ (toDiagSetObjStdSimplexIso 1).hom =
      (toDiagSetObjStdSimplexIso 0).hom ≫ intervalSource.{u} :=
  stdSimplexCompToDiagSetIso.hom.naturality (SimplexCategory.δ 1)

private theorem isPushout_toDiagSet_map {P : SSet.{u}} {a b : Δ[1] ⟶ P} {i : Fin 2}
    {f : ball.{u} atomPoint ⟶ ball (atomSimplex 1)}
    (h : IsPushout (stdSimplex.δ i) (stdSimplex.δ i) a b)
    (hf : SSet.toDiagSet.{u}.map (stdSimplex.δ i) ≫ (toDiagSetObjStdSimplexIso 1).hom =
      (toDiagSetObjStdSimplexIso 0).hom ≫ f) :
    IsPushout f f ((toDiagSetObjStdSimplexIso 1).inv ≫ SSet.toDiagSet.map a)
      ((toDiagSetObjStdSimplexIso 1).inv ≫ SSet.toDiagSet.map b) :=
  have : PreservesColimitsOfSize.{0, 0} SSet.toDiagSet.{u} :=
    sSetDiagSetAdj.leftAdjoint_preservesColimits
  (h.map SSet.toDiagSet).of_iso (toDiagSetObjStdSimplexIso 0) (toDiagSetObjStdSimplexIso 1)
    (toDiagSetObjStdSimplexIso 1) (Iso.refl _) hf hf (by simp) (by simp)

noncomputable def toDiagSetHornTwoTwoIso :
    SSet.toDiagSet.{u}.obj Λ[2, 2] ≅ cornerShape.{u} true :=
  (isPushout_toDiagSet_map.{u} horn₂₂.isPushout toDiagSet_map_stdSimplex_δ_zero).isoIsPushout _ _
    (IsPushout.of_hasPushout _ _)

noncomputable def toDiagSetHornTwoZeroIso :
    SSet.toDiagSet.{u}.obj Λ[2, 0] ≅ cornerShape.{u} false :=
  (isPushout_toDiagSet_map.{u} horn₂₀.isPushout toDiagSet_map_stdSimplex_δ_one).isoIsPushout _ _
    (IsPushout.of_hasPushout _ _)

@[reassoc]
theorem toDiagSet_map_horn₂₂_ι₀₂_comp_toDiagSetHornTwoTwoIso_hom :
    SSet.toDiagSet.{u}.map horn₂₂.ι₀₂ ≫ toDiagSetHornTwoTwoIso.hom =
      (toDiagSetObjStdSimplexIso 1).hom ≫ pushout.inl _ _ :=
  (Iso.inv_comp_eq _).1 ((Category.assoc _ _ _).symm.trans (IsPushout.inl_isoIsPushout_hom _ _
    (isPushout_toDiagSet_map.{u} horn₂₂.isPushout toDiagSet_map_stdSimplex_δ_zero)
    (IsPushout.of_hasPushout _ _)))

@[reassoc]
theorem toDiagSet_map_horn₂₂_ι₁₂_comp_toDiagSetHornTwoTwoIso_hom :
    SSet.toDiagSet.{u}.map horn₂₂.ι₁₂ ≫ toDiagSetHornTwoTwoIso.hom =
      (toDiagSetObjStdSimplexIso 1).hom ≫ pushout.inr _ _ :=
  (Iso.inv_comp_eq _).1 ((Category.assoc _ _ _).symm.trans (IsPushout.inr_isoIsPushout_hom _ _
    (isPushout_toDiagSet_map.{u} horn₂₂.isPushout toDiagSet_map_stdSimplex_δ_zero)
    (IsPushout.of_hasPushout _ _)))

@[reassoc]
theorem toDiagSet_map_horn₂₀_ι₀₁_comp_toDiagSetHornTwoZeroIso_hom :
    SSet.toDiagSet.{u}.map horn₂₀.ι₀₁ ≫ toDiagSetHornTwoZeroIso.hom =
      (toDiagSetObjStdSimplexIso 1).hom ≫ pushout.inl _ _ :=
  (Iso.inv_comp_eq _).1 ((Category.assoc _ _ _).symm.trans (IsPushout.inl_isoIsPushout_hom _ _
    (isPushout_toDiagSet_map.{u} horn₂₀.isPushout toDiagSet_map_stdSimplex_δ_one)
    (IsPushout.of_hasPushout _ _)))

@[reassoc]
theorem toDiagSet_map_horn₂₀_ι₀₂_comp_toDiagSetHornTwoZeroIso_hom :
    SSet.toDiagSet.{u}.map horn₂₀.ι₀₂ ≫ toDiagSetHornTwoZeroIso.hom =
      (toDiagSetObjStdSimplexIso 1).hom ≫ pushout.inr _ _ :=
  (Iso.inv_comp_eq _).1 ((Category.assoc _ _ _).symm.trans (IsPushout.inr_isoIsPushout_hom _ _
    (isPushout_toDiagSet_map.{u} horn₂₀.isPushout toDiagSet_map_stdSimplex_δ_one)
    (IsPushout.of_hasPushout _ _)))

noncomputable def toDiagSetCoprodStdSimplexZeroIso :
    SSet.toDiagSet.{u}.obj (Δ[0] ⨿ Δ[0]) ≅ intervalBoundary.{u} :=
  haveI : PreservesColimitsOfSize.{0, 0} SSet.toDiagSet.{u} :=
    sSetDiagSetAdj.leftAdjoint_preservesColimits
  (PreservesColimitPair.iso SSet.toDiagSet.{u} Δ[0] Δ[0]).symm ≪≫
    coprod.mapIso (toDiagSetObjStdSimplexIso 0) (toDiagSetObjStdSimplexIso 0)

@[reassoc]
theorem toDiagSet_map_coprod_inl_comp_toDiagSetCoprodStdSimplexZeroIso_hom :
    SSet.toDiagSet.{u}.map coprod.inl ≫ toDiagSetCoprodStdSimplexZeroIso.hom =
      (toDiagSetObjStdSimplexIso 0).hom ≫
        coprod.inl (X := ball.{u} atomPoint) (Y := ball atomPoint) := by
  have : PreservesColimitsOfSize.{0, 0} SSet.toDiagSet.{u} :=
    sSetDiagSetAdj.leftAdjoint_preservesColimits
  rw [toDiagSetCoprodStdSimplexZeroIso, Iso.trans_hom, Iso.symm_hom, ← coprodComparison_inl,
    ← PreservesColimitPair.iso_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact coprod.inl_map _ _

@[reassoc]
theorem toDiagSet_map_coprod_inr_comp_toDiagSetCoprodStdSimplexZeroIso_hom :
    SSet.toDiagSet.{u}.map coprod.inr ≫ toDiagSetCoprodStdSimplexZeroIso.hom =
      (toDiagSetObjStdSimplexIso 0).hom ≫
        coprod.inr (X := ball.{u} atomPoint) (Y := ball atomPoint) := by
  have : PreservesColimitsOfSize.{0, 0} SSet.toDiagSet.{u} :=
    sSetDiagSetAdj.leftAdjoint_preservesColimits
  rw [toDiagSetCoprodStdSimplexZeroIso, Iso.trans_hom, Iso.symm_hom, ← coprodComparison_inr,
    ← PreservesColimitPair.iso_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact coprod.inr_map _ _

end Atoms.Diagrammatic
