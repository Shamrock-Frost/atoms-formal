import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.Op
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.JoinOp
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.StdSimplex

open CategoryTheory Limits Opposite Simplicial

universe u

namespace SSet

variable {T : SSet.{u}}

noncomputable def cosliceπ (t : Under T) : (coslice T).obj t ⟶ t.right :=
  joinInclRight T _ ≫ ((joinLeftUnderAdjunction T).counit.app t).right

theorem comp_cosliceπ {K : SSet.{u}} {t : Under T} (ψ : K ⟶ (coslice T).obj t) :
    ψ ≫ cosliceπ t =
      joinInclRight T K ≫ (((joinLeftUnderAdjunction T).homEquiv _ _).symm ψ).right := by
  rw [Adjunction.homEquiv_counit, Under.comp_right, cosliceπ]
  exact (joinInclRight_comp_joinMap_assoc (𝟙 T) ψ _).symm

theorem yonedaEquiv_symm_comp_cosliceπ {t : Under T} {n : ℕ} (σ : ((coslice T).obj t) _⦋n⦌) :
    yonedaEquiv.symm σ ≫ cosliceπ t = joinInclRight T Δ[n] ≫ (cosliceObjEquiv T t n σ).1 := by
  have : PreservesColimitsOfSize.{0, u} (joinLeftUnder T) := preservesColimitsOfSize_shrink _
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} (joinLeftUnder T)
    (Iso.refl _)
  let g : (joinLeftUnder T).obj Δ[n] ⟶ t :=
    Under.homMk (cosliceObjEquiv T t n σ).1 (cosliceObjEquiv T t n σ).2
  have h : (uliftYonedaEquiv.symm (ULift.up (𝟙 ⦋n⦌)) : Δ[n] ⟶ Δ[n]) = 𝟙 _ :=
    uliftYonedaEquiv.symm_apply_eq.2 rfl
  have h' : yonedaEquiv ((joinLeftUnderAdjunction T).homEquiv _ _ g) = σ := by
    refine (Presheaf.uliftYonedaAdjunction_homEquiv_app _ _ g (ULift.up (𝟙 ⦋n⦌))).trans ?_
    rw [h]
    exact congrArg ULift.up ((Category.id_comp _).trans ((congrArg (· ≫ g)
      ((joinLeftUnder T).map_id _)).trans (Category.id_comp g)))
  rw [comp_cosliceπ, ← (Equiv.eq_symm_apply _).2 h', Equiv.symm_apply_apply]
  rfl

@[reassoc]
theorem cosliceOpIso_hom_app_comp_sliceπ (t : Under T) :
    (cosliceOpIso T).hom.app t ≫ sliceπ ((Under.post opFunctor).obj t) =
      opFunctor.map (cosliceπ t) := by
  refine hom_ext_yonedaEquiv_symm fun n σ' ↦ ?_
  obtain ⟨σ, rfl⟩ := (opObjEquiv (X := (coslice T).obj t)).symm.surjective σ'
  have h₁ : yonedaEquiv.symm (opObjEquiv.symm σ) ≫ (cosliceOpIso T).hom.app t =
      yonedaEquiv.symm (((cosliceOpIso T).hom.app t).app _ (opObjEquiv.symm σ)) :=
    yonedaEquiv_symm_comp _ _
  rw [← Category.assoc, h₁, yonedaEquiv_symm_comp_sliceπ,
    sliceObjEquiv_cosliceOpIso_hom_app_app_coe, yonedaEquiv_symm_opObjEquiv_symm]
  refine (joinInclLeft_comp_joinMap_assoc _ _ _).trans ?_
  refine Eq.trans (congrArg (_ ≫ ·) ?_) (Category.assoc _ _ _).symm
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) ((Iso.comp_inv_eq _).2
    (opFunctor_map_joinInclRight_comp_joinOpIso_hom T Δ[n]).symm))).trans ?_
  exact ((opFunctor.map_comp _ _).symm.trans (congrArg opFunctor.map
    (yonedaEquiv_symm_comp_cosliceπ σ).symm)).trans (opFunctor.map_comp _ _)

end SSet
