import Atoms.Diagrammatic.Joyal.FaceNerve
import Atoms.Diagrammatic.SimplicialAdjunction
import Atoms.Homotopical.Simplicial.Subdivision

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial Opposite
open Atoms.Homotopical Atoms.Shape PartialOrder

universe u

namespace Atoms.Diagrammatic

noncomputable def DiagSet.sd : DiagSet.{u} ⥤ SSet.{u} := faceNerve ⋙ MarkedPresheaf.forget

noncomputable def DiagSet.ex : SSet.{u} ⥤ DiagSet.{u} :=
  MarkedPresheaf.sharp edgeMarking ⋙
    MarkedPresheaf.nerve markedFaceNerveSite (fun x => epi_markedFaceNerveSite_map_toSelf x) ⋙
      MarkedPresheaf.forget

noncomputable def DiagSet.sdExAdjunction : DiagSet.sd.{u} ⊣ DiagSet.ex.{u} :=
  (MarkedPresheaf.flatForgetAdjunction atomMarking).comp
    (markedFaceNerveAdjunction.comp (MarkedPresheaf.forgetSharpAdjunction edgeMarking))

noncomputable def DiagSet.yonedaCompSdIso :
    uliftYoneda.{u} ⋙ DiagSet.sd ≅ atomToRDCpx ⋙ rdcFaceNerve ⋙ MarkedPresheaf.forget :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight yonedaCompFaceNerveIso _ ≪≫
    Functor.associator _ _ _

noncomputable def DiagSet.exObjEquiv (K : SSet.{u}) (U : Atom) :
    (DiagSet.ex.obj K).obj (op U) ≃ (nerve (ULift.{u} U.ogp) ⟶ K) :=
  uliftYonedaEquiv.symm.trans
    (((DiagSet.sdExAdjunction.homEquiv (uliftYoneda.{u}.obj U) K).symm).trans
      ((DiagSet.yonedaCompSdIso.app U).homCongr (Iso.refl K)))

instance DiagSet.preservesMonomorphisms_sd : DiagSet.sd.{u}.PreservesMonomorphisms :=
  ⟨fun f _ => (MarkedPresheaf.mono_iff _).1 (faceNerve.map_mono f)⟩

private noncomputable def atomSimplexVerticesOrderIso (n : ℕ) :
    (atomSimplex n).ogp ≃o {S : Finset (Fin (n + 1)) // S.Nonempty} where
  toEquiv := Equiv.ofBijective
    (fun x => ⟨atomSimplexVertices n x,
      Finset.card_pos.1 (by rw [card_atomSimplexVertices]; omega)⟩)
    ⟨fun _ _ h => atomSimplexVertices_injective n (congrArg Subtype.val h),
      fun S => let ⟨x, hx⟩ := exists_atomSimplexVertices_eq n S.2; ⟨x, Subtype.ext hx⟩⟩
  map_rel_iff' := atomSimplexVertices_subset_iff

private noncomputable def faceChainOrderIso (n : SimplexCategory) :
    ULift.{u} (atomSimplex n.len).ogp ≃o NonemptyFiniteChains (ULift.{u} (Fin (n.len + 1))) :=
  ULift.orderIso.trans ((atomSimplexVerticesOrderIso n.len).trans (chainOrderIso n.len).symm)

private theorem mem_faceChainOrderIso {n : SimplexCategory}
    (x : ULift.{u} (atomSimplex n.len).ogp) (b : ULift.{u} (Fin (n.len + 1))) :
    b ∈ (faceChainOrderIso n x).finset ↔ b.down ∈ atomSimplexVertices n.len x.down := by
  change b ∈ (atomSimplexVertices n.len x.down).map Equiv.ulift.symm.toEmbedding ↔ _
  rw [Finset.mem_map]
  exact ⟨fun ⟨a, ha, hab⟩ => hab ▸ ha, fun h => ⟨b.down, h, rfl⟩⟩

private theorem faceChainOrderIso_map {n m : SimplexCategory} (θ : n ⟶ m)
    (x : ULift.{u} (atomSimplex n.len).ogp) :
    faceChainOrderIso m (ULift.map (simplexHom θ.toOrderHom) x) =
      NonemptyFiniteChains.map (faceChainOrderIso n x) (SimplexCategory.toPartOrd.map θ).hom := by
  apply (chainOrderIso m.len).injective
  apply Subtype.ext
  rw [faceChainOrderIso, OrderIso.trans_apply, OrderIso.trans_apply, OrderIso.apply_symm_apply]
  change atomSimplexVertices m.len (simplexHom θ.toOrderHom x.down) = _
  rw [atomSimplexVertices_simplexHom]
  ext v
  simp only [chainOrderIso, RelIso.coe_fn_mk, Equiv.coe_fn_mk, Finset.mem_map, Finset.mem_image,
    Equiv.toEmbedding_apply, Equiv.ulift_apply]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨ULift.up (θ.toOrderHom j), (NonemptyFiniteChains.mem_map_iff _ _ _).2
      ⟨ULift.up j, (mem_faceChainOrderIso x _).2 hj, rfl⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨b, hb, rfl⟩ := (NonemptyFiniteChains.mem_map_iff _ _ _).1 ha
    exact ⟨b.down, (mem_faceChainOrderIso x b).1 hb, rfl⟩

private noncomputable def stdSimplexCompSdIso :
    SSet.stdSimplex ⋙ SSet.toDiagSet ⋙ DiagSet.sd ≅ SimplexCategory.sd.{u} :=
  Functor.isoWhiskerRight stdSimplexCompToDiagSetIso DiagSet.sd ≪≫
    Functor.isoWhiskerLeft simplexFunctor DiagSet.yonedaCompSdIso ≪≫
    NatIso.ofComponents (fun n => @asIso _ _ _ _
      (nerveMap (faceChainOrderIso n).monotone.functor) (isIso_nerveMap_orderIso _))
      (fun {n m} θ => by
        induction n using SimplexCategory.rec with | _ n
        induction m using SimplexCategory.rec with | _ m
        ext d x
        exact nerve.ext_of_isThin (funext fun i ↦ faceChainOrderIso_map θ (x.obj i)))

noncomputable def DiagSet.toDiagSetCompSdIso : SSet.toDiagSet.{u} ⋙ DiagSet.sd ≅ SSet.sd :=
  have : PreservesColimitsOfSize.{0, u} SSet.toDiagSet.{u} :=
    sSetDiagSetAdj.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0, u} DiagSet.sd.{u} :=
    DiagSet.sdExAdjunction.leftAdjoint_preservesColimits
  have : (SSet.toDiagSet.{u} ⋙ DiagSet.sd).IsLeftKanExtension stdSimplexCompSdIso.inv :=
    Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} _
      stdSimplexCompSdIso.symm
  Functor.leftKanExtensionUnique _ stdSimplexCompSdIso.inv SSet.sd SSet.stdSimplex.sdIso.inv

noncomputable def DiagSet.exCompToSSetIso : DiagSet.ex.{u} ⋙ DiagSet.toSSet ≅ SSet.ex :=
  conjugateIsoEquiv (sSetDiagSetAdj.comp DiagSet.sdExAdjunction) SSet.sdExAdjunction
    DiagSet.toDiagSetCompSdIso.symm

end Atoms.Diagrammatic
