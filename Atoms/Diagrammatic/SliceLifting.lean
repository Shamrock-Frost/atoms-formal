import Atoms.Diagrammatic.JoinMonomorphism
import Atoms.Diagrammatic.Localization.ModelStructure
import Atoms.Diagrammatic.Slice
import Atoms.ForMathlib.CategoryTheory.Monoidal.DayConvolution.JoinLifting

open CategoryTheory CategoryTheory.WithInitial Limits MorphismProperty HomotopicalAlgebra
  Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open scoped DiagSet.Join

theorem sliceRestrict_eq {A' A : DiagSet.{u}} (i : A' ⟶ A) :
    sliceRestrict i = WithInitial.sliceRes i := by
  ext t U x
  refine (sliceObjEquiv A' ((Under.map i).obj t) U.unop).injective (Subtype.ext ?_)
  exact (congrArg Subtype.val (Equiv.apply_symm_apply _ _)).trans
    (sliceObjEquiv_sliceRes_app_app_coe i t U.unop x).symm

theorem rlp_monomorphisms_leibnizSlice {S T X Y : DiagSet.{u}} (j : S ⟶ T) [Mono j]
    {p : X ⟶ Y} (hp : (monomorphisms DiagSet.{u}).rlp p) (t : T ⟶ X) :
    (monomorphisms DiagSet.{u}).rlp (WithInitial.leibnizSlice j p t) := by
  intro K L i hi
  have : Mono i := hi
  exact (hasLiftingProperty_pushoutObjObj_ι_iff (Functor.PushoutObjObj.ofHasPushout 𝒥 i j) p).1
    (hp _ (mono_pushoutObjObj_ι_join i j)) t

theorem rlp_anodyne_leibnizSlice
    (h : ∀ ⦃A B : DiagSet.{u}⦄ (g : A ⟶ B),
      reversibleCylinder.{u}.anodyneGenerators (inftyGenerators 1) g →
      ∀ V : Atom, trivialCofibrations (DiagSet.Infty.{u} 1)
        ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout
          (Functor.curry.obj (WithInitial.joinFunctor (C := Atom) : DiagSet × DiagSet ⥤ DiagSet))
          g (sphereInclusion.{u} V)).ι))
    {S T X Y : DiagSet.{u}} (j : S ⟶ T) [Mono j] {p : X ⟶ Y}
    (hp : Fibration ((DiagSet.toInfty 1).map p)) (t : T ⟶ X) :
    (reversibleCylinder.{u}.anodyne (inftyGenerators 1)).rlp (WithInitial.leibnizSlice j p t) := by
  have hS := inftyGenerators_le_monomorphisms.{u} 1
  have := reversibleCylinder.{u}.isSaturated_trivialCofibrations (inftyGenerators.{u} 1) hS
  have hj : saturation.{u} sphereInclusions j := by
    rw [← monomorphisms_eq_saturation_sphereInclusions]
    exact ‹Mono j›
  refine (reversibleCylinder.{u}.naiveFibrations_eq_rlp_anodyneGenerators _ hS).symm.le _ ?_
  intro A B g hg
  have hι := pushoutObjObj_ι_join_mem_of_saturation
    (reversibleCylinder.{u}.trivialCofibrations (inftyGenerators 1))
    (reversibleCylinder.{u}.anodyneGenerators (inftyGenerators 1)) sphereInclusions
    (by
      rintro _ _ _ _ g _ hg ⟨V⟩
      exact h g hg V)
    (le_saturation _ _ hg) hj
  exact (hasLiftingProperty_pushoutObjObj_ι_iff _ p).1
    ((hp.mem : reversibleCylinder.{u}.fibrations (inftyGenerators 1) p) _ hι) t

theorem isFibrant_slice
    (h : ∀ ⦃A B : DiagSet.{u}⦄ (g : A ⟶ B),
      reversibleCylinder.{u}.anodyneGenerators (inftyGenerators 1) g →
      ∀ V : Atom, trivialCofibrations (DiagSet.Infty.{u} 1)
        ((DiagSet.toInfty 1).map (Functor.PushoutObjObj.ofHasPushout
          (Functor.curry.obj (WithInitial.joinFunctor (C := Atom) : DiagSet × DiagSet ⥤ DiagSet))
          g (sphereInclusion.{u} V)).ι))
    {T X : DiagSet.{u}} (hX : IsFibrant ((DiagSet.toInfty 1).obj X)) (t : T ⟶ X) :
    IsFibrant ((DiagSet.toInfty 1).obj ((WithInitial.slice T).obj (Under.mk t))) := by
  have hS := inftyGenerators_le_monomorphisms.{u} 1
  refine (ExactCylinder.modelCategory.isFibrant_iff reversibleCylinder (inftyGenerators 1) hS
    _).2 ?_
  have hp : Fibration ((DiagSet.toInfty 1).map (terminal.from X)) :=
    (isFibrant_iff_of_isTerminal _ terminalIsTerminal).1 hX
  have hl := rlp_anodyne_leibnizSlice h (initial.to T) hp t
  have hg : (reversibleCylinder.{u}.anodyne (inftyGenerators 1)).rlp
      ((sliceRes (initial.to T)).app (Under.mk (t ≫ terminal.from X))) := by
    have := isIso_of_isTerminal (isTerminalSliceObj _ terminalIsTerminal)
      (isTerminalSliceObj _ terminalIsTerminal)
      ((sliceRes (initial.to T)).app (Under.mk (t ≫ terminal.from X)))
    exact rlp_of_isIso _ _
  have hfst := MorphismProperty.pullback_fst ((slice (⊥_ DiagSet.{u})).map
    (Under.homMk (terminal.from X) (by simp) :
      Under.mk (initial.to T ≫ t) ⟶ Under.mk (initial.to T ≫ t ≫ terminal.from X))) _ hg
  have hiso := rlp_of_isIso (reversibleCylinder.{u}.anodyne (inftyGenerators 1))
    (sliceEmptyIso initialIsInitial ((Under.map (initial.to T)).obj (Under.mk t))).hom
  exact reversibleCylinder.{u}.isFibrant_of_rlp_anodyne (inftyGenerators 1) _
    (comp_mem _ _ _ hl (comp_mem _ _ _ hfst hiso))
    ((ExactCylinder.modelCategory.isFibrant_iff reversibleCylinder (inftyGenerators 1) hS
      X).1 hX)

end Atoms.Diagrammatic
