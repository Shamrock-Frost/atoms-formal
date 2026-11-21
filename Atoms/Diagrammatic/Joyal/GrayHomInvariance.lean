import Atoms.Diagrammatic.Joyal.GrayHomComparison
import Atoms.Diagrammatic.Joyal.RelativeCylinder

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open Atoms.Shape

universe u

namespace Atoms.Diagrammatic

private theorem conjugateEquiv_grayTensorLeft_map {A B : DiagSet.{u}} (i : A ⟶ B) :
    conjugateEquiv (grayTensorLeftAdjunction B) (grayTensorLeftAdjunction A)
      ((Functor.curry.obj grayTensorBifunctor).map i) = grayHomLeftRestrict i :=
  conjugateEquiv_eq_of_homEquiv _ _ _ _ fun _ _ g =>
    grayTensorLeftParametrizedAdjunction.homEquiv_naturality_one i g

theorem DiagSet.Infty.weakEquivalence_toInfty_one_grayHomLeftRestrict_app {A B : DiagSet.{u}}
    (f : A ⟶ B) [WeakEquivalence ((DiagSet.toInfty 1).map f)] {Y : DiagSet.{u}}
    (hY : IsInftyCategory 1 Y) :
    WeakEquivalence ((DiagSet.toInfty 1).map ((grayHomLeftRestrict f).app Y)) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2 hY
  have h := Adjunction.IsQuillen.weakEquivalence_conjugateEquiv_app
    (DiagSet.Infty.isQuillen_grayTensorLeftAdjunction_one B)
    (DiagSet.Infty.isQuillen_grayTensorLeftAdjunction_one A)
    ((Functor.curry.obj grayTensorBifunctor).map f)
    (fun T _ => (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one T).weakEquivalence_map
      ((DiagSet.toInfty 1).map f)) ((DiagSet.toInfty 1).obj Y)
  have e : (conjugateEquiv (DiagSet.Infty.grayTensorLeftAdjunction 1 B)
      (DiagSet.Infty.grayTensorLeftAdjunction 1 A)
        ((Functor.curry.obj grayTensorBifunctor).map f)).app ((DiagSet.toInfty 1).obj Y) =
      (DiagSet.toInfty 1).map ((grayHomLeftRestrict f).app Y) :=
    NatTrans.congr_app (conjugateEquiv_grayTensorLeft_map f) Y
  rw [e] at h
  exact h

theorem DiagSet.Infty.weakEquivalence_toInfty_one_functorCategory_restrict {A B : DiagSet.{u}}
    (f : A ⟶ B) [WeakEquivalence ((DiagSet.toInfty 1).map f)] {Y : DiagSet.{u}}
    (hY : IsInftyCategory 1 Y) :
    WeakEquivalence ((DiagSet.toInfty 1).map ((functorCategoryGrayIso B Y).hom ≫
      (grayHomRestrict f).app Y ≫ (functorCategoryGrayIso A Y).inv)) := by
  have := weakEquivalence_grayHomRestrict_app f hY
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

theorem DiagSet.Infty.weakEquivalence_toInfty_one_functorCategory_pseudo_restrict
    {A B : DiagSet.{u}} (f : A ⟶ B) [WeakEquivalence ((DiagSet.toInfty 1).map f)]
    {Y : DiagSet.{u}} (hY : IsInftyCategory 1 Y) :
    haveI := isIso_functorCategoryPseudoToGray A hY
    WeakEquivalence ((DiagSet.toInfty 1).map (functorCategoryPseudoToGray B Y ≫
      (functorCategoryGrayIso B Y).hom ≫ (grayHomRestrict f).app Y ≫
      (functorCategoryGrayIso A Y).inv ≫
      inv (functorCategoryPseudoToGray A Y))) := by
  have := isIso_functorCategoryPseudoToGray A hY
  have := isIso_functorCategoryPseudoToGray B hY
  have := weakEquivalence_grayHomRestrict_app f hY
  simp only [Functor.map_comp]
  infer_instance

theorem weakEquivalence_toInfty_one_of_isPullback_grayHomRestrict {V A' A X T M M' : DiagSet.{u}}
    {j : V ⟶ A'} {k : A' ⟶ A} {i : V ⟶ A} (hi : j ≫ k = i) [Mono i]
    [WeakEquivalence ((DiagSet.toInfty 1).map k)] (hX : IsInftyCategory 1 X)
    {b : T ⟶ (grayHomRight V).obj X} {fst : M ⟶ (grayHomRight A).obj X} {snd : M ⟶ T}
    {fst' : M' ⟶ (grayHomRight A').obj X} {snd' : M' ⟶ T}
    (h : IsPullback fst snd ((grayHomRestrict i).app X) b)
    (h' : IsPullback fst' snd' ((grayHomRestrict j).app X) b) (m : M ⟶ M')
    (hfst : m ≫ fst' = fst ≫ (grayHomRestrict k).app X) (hsnd : m ≫ snd' = snd) :
    WeakEquivalence ((DiagSet.toInfty 1).map m) := by
  have : Mono j := mono_of_mono_fac hi
  have := fibration_toInfty_one_grayHomRestrict i hX
  have := fibration_toInfty_one_grayHomRestrict j hX
  have := weakEquivalence_grayHomRestrict_app k hX
  have : PreservesLimits (DiagSet.toInfty 1) :=
    inferInstanceAs (PreservesLimits (𝟭 DiagSet.{u}))
  have hk : (DiagSet.toInfty 1).map ((grayHomRestrict k).app X) ≫
      (DiagSet.toInfty 1).map ((grayHomRestrict j).app X) =
        (DiagSet.toInfty 1).map ((grayHomRestrict i).app X) := by
    rw [← Functor.map_comp, ← NatTrans.comp_app, ← grayHomRestrict_comp, hi]
  have := weakEquivalence_pullback_map_of_fibration ((DiagSet.toInfty 1).map b) _ _ _ hk
  have H := (DiagSet.toInfty 1).map_isPullback h
  have H' := (DiagSet.toInfty 1).map_isPullback h'
  have e : (DiagSet.toInfty 1).map m = H.isoPullback.hom ≫
      pullback.map _ _ _ _ ((DiagSet.toInfty 1).map ((grayHomRestrict k).app X)) (𝟙 _) (𝟙 _)
        ((Category.comp_id _).trans hk.symm)
        ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ H'.isoPullback.inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    apply pullback.hom_ext
    · rw [Category.assoc, H'.isoPullback_hom_fst, Category.assoc, pullback.lift_fst,
        H.isoPullback_hom_fst_assoc, ← Functor.map_comp, ← Functor.map_comp, hfst]
    · rw [Category.assoc, H'.isoPullback_hom_snd, Category.assoc, pullback.lift_snd,
        Category.comp_id, H.isoPullback_hom_snd, ← Functor.map_comp, hsnd]
  rw [e]
  infer_instance

theorem weakEquivalence_toInfty_one_relativeMappingSpaceRestrict {V A' A X : DiagSet.{u}}
    (j : V ⟶ A') (k : A' ⟶ A) [Mono (j ≫ k)] [WeakEquivalence ((DiagSet.toInfty 1).map k)]
    (f : V ⟶ X) (hX : IsInftyCategory 1 X) :
    WeakEquivalence ((DiagSet.toInfty 1).map (relativeMappingSpaceRestrict j k f)) :=
  weakEquivalence_toInfty_one_of_isPullback_grayHomRestrict rfl hX
    (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _) _
    (pullback.lift_fst _ _ _) ((pullback.lift_snd _ _ _).trans (Category.comp_id _))

theorem DiagSet.weakEquivalence_toInfty_one_mappingSpace_restrict {I' X : DiagSet.{u}}
    {j : intervalBoundary ⟶ I'} {e : I' ⟶ ball (atomSimplex 1)} (he : j ≫ e = intervalBoundaryι)
    [WeakEquivalence ((DiagSet.toInfty 1).map e)] (hX : IsInftyCategory 1 X) (x y : X.Vertex)
    (m : (X.mappingSpace x y).toFunctor ⟶
      relativeMappingSpace j (coprod.desc (vertexHom x) (vertexHom y)))
    (hm : m ≫ pullback.fst _ _ = (X.mappingSpace x y).ι ≫ (grayHomRestrict e).app X) :
    WeakEquivalence ((DiagSet.toInfty 1).map m) := by
  have h := X.isPullback_mappingSpace x y
  rw [X.endpointsPoint_eq_homEquiv] at h
  exact weakEquivalence_toInfty_one_of_isPullback_grayHomRestrict he hX h
    (IsPullback.of_hasPullback _ (diagramPoint _)) m hm (isTerminalBallAtomPoint.hom_ext _ _)

end Atoms.Diagrammatic
