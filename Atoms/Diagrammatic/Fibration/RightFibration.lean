import Atoms.Diagrammatic.Fibration.SliceFibration

open CategoryTheory Limits Opposite HomotopicalAlgebra Simplicial Atoms.Shape
open CategoryTheory.WithInitial (join joinMap joinMapIso joinInclRight slice coslice sliceRes
  cosliceRes leibnizSlice leibnizCoslice joinRightUnder joinRightUnderAdjunction
  joinLeftUnderAdjunction hasLiftingProperty_pushoutObjObj_ι_iff
  hasLiftingProperty_leibnizCoslice_iff)
open CategoryTheory.MorphismProperty (comp_mem of_isIso monomorphisms)
open scoped Atoms.Diagrammatic.DiagSet.Join

universe u

namespace Atoms.Diagrammatic

variable {E S : DiagSet.{u}}

structure DiagSet.IsRightFibration (p : E ⟶ S) : Prop where
  fibration : Fibration ((DiagSet.toInfty 1).map p)
  hasLiftingProperty_joinMap : ∀ ⦃K L : DiagSet.{u}⦄ (i : K ⟶ L) [Mono i],
    HasLiftingProperty (joinMap i (𝟙 (ball.{u} atomPoint))) p

theorem DiagSet.hasLiftingProperty_joinMap_id_iff {K L Z : DiagSet.{u}} (i : K ⟶ L)
    (p : E ⟶ S) :
    HasLiftingProperty (joinMap i (𝟙 Z)) p ↔ ∀ z : Z ⟶ E,
      HasLiftingProperty i ((slice Z).map (Under.homMk p : Under.mk z ⟶ Under.mk (z ≫ p))) := by
  refine ⟨fun h z ↦ ?_, fun h ↦ ⟨fun {a b} sq ↦ ?_⟩⟩
  · rw [← (joinRightUnderAdjunction Z).hasLiftingProperty_iff]
    refine ⟨fun {u v} sq ↦ ?_⟩
    obtain ⟨l⟩ := (h.sq_hasLift (sq.map (Under.forget Z))).exists_lift
    have hl : ((joinRightUnder Z).obj L).hom ≫ l.l = (Under.mk z).hom := by
      rw [← Under.w ((joinRightUnder Z).map i)]
      exact (Category.assoc _ _ _).trans ((congrArg _ l.fac_left).trans (Under.w u))
    exact ⟨⟨⟨Under.homMk l.l hl, Under.UnderMorphism.ext l.fac_left,
      Under.UnderMorphism.ext l.fac_right⟩⟩⟩
  · have hb : joinInclRight L Z ≫ b = (joinInclRight K Z ≫ a) ≫ p := by
      rw [Category.assoc, sq.w, ← Category.assoc, WithInitial.joinInclRight_comp_joinMap,
        Category.id_comp]
    have sq' : CommSq (Under.homMk a rfl :
        (joinRightUnder Z).obj K ⟶ Under.mk (joinInclRight K Z ≫ a)) ((joinRightUnder Z).map i)
        (Under.homMk p : Under.mk (joinInclRight K Z ≫ a) ⟶
          Under.mk ((joinInclRight K Z ≫ a) ≫ p)) (Under.homMk b hb) :=
      ⟨Under.UnderMorphism.ext sq.w⟩
    have := ((joinRightUnderAdjunction Z).hasLiftingProperty_iff i _).2
      (h (joinInclRight K Z ≫ a))
    obtain ⟨l⟩ := (this.sq_hasLift sq').exists_lift
    exact ⟨⟨⟨l.l.right, congrArg CommaMorphism.right l.fac_left,
      congrArg CommaMorphism.right l.fac_right⟩⟩⟩

private noncomputable def toDiagSetJoinMapIdArrowIso {K L : SSet.{u}} (i : K ⟶ L) :
    Arrow.mk (SSet.toDiagSet.map (SSet.joinMap i (𝟙 Δ[0]))) ≅
      Arrow.mk (joinMap (SSet.toDiagSet.map i) (𝟙 (ball.{u} atomPoint))) :=
  Arrow.isoMk (toDiagSetJoinIso K Δ[0] ≪≫ joinMapIso (Iso.refl _) (toDiagSetObjStdSimplexIso 0))
    (toDiagSetJoinIso L Δ[0] ≪≫ joinMapIso (Iso.refl _) (toDiagSetObjStdSimplexIso 0)) (by
      simp only [Arrow.mk_hom, Iso.trans_hom, joinMapIso, Iso.refl_hom, Category.assoc,
        toDiagSet_map_joinMap_comp_toDiagSetJoinIso_hom_assoc, WithInitial.joinMap_comp_joinMap,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id])

theorem DiagSet.isRightFibration_of_hasLiftingProperty_of_sliceFibrancy
    (hslice : ∀ ⦃A B E S : DiagSet.{u}⦄ (j : A ⟶ B) [Mono j] (p : E ⟶ S)
      [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
      (t : B ⟶ E), Fibration ((DiagSet.toInfty 1).map (WithInitial.leibnizSlice j p t)))
    {X Y : DiagSet.{u}} (q : X ⟶ Y) [Fibration ((DiagSet.toInfty 1).map q)]
    [IsFibrant ((DiagSet.toInfty 1).obj Y)]
    (h : ∀ n : ℕ, HasLiftingProperty (SSet.toDiagSet.map (SSet.joinMap ∂Δ[n].ι (𝟙 Δ[0]))) q) :
    DiagSet.IsRightFibration q := by
  refine ⟨inferInstance, fun K L i _ ↦ (DiagSet.hasLiftingProperty_joinMap_id_iff i q).2
    fun y ↦ ?_⟩
  have := fibration_slice_map_of_sliceFibrancy hslice q y
  have := isFibrant_slice_of_sliceFibrancy hslice (y ≫ q)
  refine rlp_monomorphisms_of_rlp_I_toSSet_map _ ?_ i
    (MorphismProperty.monomorphisms.infer_property i)
  rintro _ _ _ ⟨n⟩
  have := mono_toDiagSet_map_boundary_ι.{u} n
  refine (sSetDiagSetAdj.hasLiftingProperty_iff _ _).1 ?_
  exact (DiagSet.hasLiftingProperty_joinMap_id_iff _ q).1
    ((HasLiftingProperty.iff_of_arrow_iso_left (toDiagSetJoinMapIdArrowIso ∂Δ[n].ι) q).1 (h n)) y

theorem DiagSet.isRightFibration_iff_rightFibrations_toSSet_of_sliceFibrancy
    (hslice : ∀ ⦃A B E S : DiagSet.{u}⦄ (j : A ⟶ B) [Mono j] (p : E ⟶ S)
      [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
      (t : B ⟶ E), Fibration ((DiagSet.toInfty 1).map (WithInitial.leibnizSlice j p t)))
    (p : E ⟶ S) [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)] :
    DiagSet.IsRightFibration p ↔ SSet.rightFibrations (DiagSet.toSSet.map p) := by
  refine ⟨fun hp ↦ ?_, fun hp ↦ DiagSet.isRightFibration_of_hasLiftingProperty_of_sliceFibrancy
    hslice p fun n ↦ (sSetDiagSetAdj.hasLiftingProperty_iff _ _).2
      (SSet.rightAnodyneExtensions_joinMap_id ∂Δ[n].ι _ hp)⟩
  have : SSet.InnerFibration (DiagSet.toSSet.map p) :=
    innerFibration_toSSet_map ((DiagSet.toInfty 1).map p) inferInstance
  rintro _ _ _ ⟨i, h0⟩
  rcases (Fin.le_last i).lt_or_eq with hi | rfl
  · exact SSet.mem_innerFibrations _ _ (SSet.horn_ι_mem_innerHornInclusions h0 hi)
  · rename_i n
    have := mono_toDiagSet_map_boundary_ι.{u} n
    have h : HasLiftingProperty (SSet.joinMap ∂Δ[n].ι (𝟙 Δ[0])) (DiagSet.toSSet.map p) :=
      (sSetDiagSetAdj.hasLiftingProperty_iff _ _).1
        ((HasLiftingProperty.iff_of_arrow_iso_left (toDiagSetJoinMapIdArrowIso ∂Δ[n].ι) p).2
          (hp.hasLiftingProperty_joinMap _))
    rw [← SSet.range_joinMap_boundary_comp]
    let f := SSet.joinMap ∂Δ[n].ι (𝟙 Δ[0]) ≫ (SSet.stdSimplexJoinIso.{u} n 0).hom
    have : Mono f := mono_comp _ _
    refine (HasLiftingProperty.iff_of_arrow_iso_left (Arrow.isoMk
      (asIso (SSet.Subcomplex.toRange f)).symm (SSet.stdSimplexJoinIso n 0).symm
      ((Iso.inv_comp_eq _).2 ((Category.assoc _ _ _).symm.trans
        ((SSet.Subcomplex.toRange_ι f =≫ _).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id _))))).symm)) _).2 h

private noncomputable def isTerminalCosliceObj {T : DiagSet.{u}} (t : Under T)
    (ht : IsTerminal t.right) : IsTerminal ((coslice T).obj t) :=
  have := (joinLeftUnderAdjunction T).rightAdjoint_preservesLimits
  IsTerminal.isTerminalObj (coslice T) t (IsTerminal.ofUniqueHom
    (fun Y ↦ Under.homMk (ht.from Y.right) (ht.hom_ext _ _))
    (fun _ _ ↦ Under.UnderMorphism.ext (ht.hom_ext _ _)))

theorem isFibrant_leibnizCoslice_target_of_sliceFibrancy
    (hcoslice : ∀ ⦃A B E S : DiagSet.{u}⦄ (j : A ⟶ B) [Mono j] (p : E ⟶ S)
      [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
      (t : B ⟶ E), Fibration ((DiagSet.toInfty 1).map (WithInitial.leibnizCoslice j p t)))
    (hcofib : ∀ ⦃B X : DiagSet.{u}⦄ [IsFibrant ((DiagSet.toInfty 1).obj X)] (t : B ⟶ X),
      IsFibrant ((DiagSet.toInfty 1).obj ((WithInitial.coslice B).obj (Under.mk t))))
    {A B E S : DiagSet.{u}} (j : A ⟶ B) [Mono j] (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [hS : IsFibrant ((DiagSet.toInfty 1).obj S)]
    (t : B ⟶ E) :
    IsFibrant ((DiagSet.toInfty 1).obj (pullback ((coslice A).map (Under.homMk p :
      Under.mk (j ≫ t) ⟶ Under.mk (j ≫ t ≫ p))) ((cosliceRes j).app (Under.mk (t ≫ p))))) := by
  have : Fibration ((DiagSet.toInfty 1).map (terminal.from S)) :=
    (isFibrant_iff_of_isTerminal _ terminalIsTerminal).1 hS
  have : IsFibrant ((DiagSet.toInfty 1).obj E) :=
    isFibrant_of_fibration ((DiagSet.toInfty 1).map p)
  have := hcofib (j ≫ t)
  have hiso : IsIso (pullback.fst ((coslice A).map (Under.homMk (terminal.from S) :
      Under.mk (j ≫ t ≫ p) ⟶ Under.mk (j ≫ (t ≫ p) ≫ terminal.from S)))
      ((cosliceRes j).app (Under.mk ((t ≫ p) ≫ terminal.from S)))) := by
    have := isIso_of_isTerminal (isTerminalCosliceObj _ terminalIsTerminal)
      (isTerminalCosliceObj _ terminalIsTerminal)
      ((cosliceRes j).app (Under.mk ((t ≫ p) ≫ terminal.from S)))
    exact MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms DiagSet.{u})
      (IsPullback.of_hasPullback _ _).flip this
  have e : (cosliceRes j).app (Under.mk (t ≫ p)) =
      leibnizCoslice j (terminal.from S) (t ≫ p) ≫ pullback.fst _ _ :=
    (pullback.lift_fst _ _ _).symm
  have hres : (reversibleCylinder.{u}.trivialCofibrations (inftyGenerators 1)).rlp
      ((cosliceRes j).app (Under.mk (t ≫ p))) := by
    rw [e]
    exact comp_mem _ _ _ ((fibration_toInfty_one_map_iff _).1 (hcoslice j _ (t ≫ p)))
      (of_isIso _ _)
  have : Fibration ((DiagSet.toInfty 1).map (pullback.fst ((coslice A).map (Under.homMk p :
      Under.mk (j ≫ t) ⟶ Under.mk (j ≫ t ≫ p))) ((cosliceRes j).app (Under.mk (t ≫ p))))) :=
    (fibration_toInfty_one_map_iff _).2
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip hres)
  exact isFibrant_of_fibration ((DiagSet.toInfty 1).map (pullback.fst _ _))

theorem rlp_monomorphisms_leibnizCoslice_toDiagSet_map_of_sliceFibrancy
    (hcoslice : ∀ ⦃A B E S : DiagSet.{u}⦄ (j : A ⟶ B) [Mono j] (p : E ⟶ S)
      [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
      (t : B ⟶ E), Fibration ((DiagSet.toInfty 1).map (WithInitial.leibnizCoslice j p t)))
    (hcofib : ∀ ⦃B X : DiagSet.{u}⦄ [IsFibrant ((DiagSet.toInfty 1).obj X)] (t : B ⟶ X),
      IsFibrant ((DiagSet.toInfty 1).obj ((WithInitial.coslice B).obj (Under.mk t))))
    {K L : SSet.{u}} {h : K ⟶ L} [Mono h] (hh : SSet.rightAnodyneExtensions h) (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (t : SSet.toDiagSet.obj L ⟶ E) :
    (monomorphisms DiagSet.{u}).rlp (leibnizCoslice (SSet.toDiagSet.map h) p t) := by
  have := hcoslice (SSet.toDiagSet.map h) p t
  have := isFibrant_leibnizCoslice_target_of_sliceFibrancy hcoslice hcofib
    (SSet.toDiagSet.map h) p t
  refine rlp_monomorphisms_of_rlp_I_toSSet_map _ ?_
  rintro _ _ _ ⟨m⟩
  refine (sSetDiagSetAdj.hasLiftingProperty_iff _ _).1 ?_
  have : PreservesColimitsOfSize.{0, 0} SSet.toDiagSet.{u} :=
    sSetDiagSetAdj.leftAdjoint_preservesColimits
  let sq₀ := Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj SSet.joinFunctor) h ∂Δ[m].ι
  let sq := sq₀.map toDiagSetJoinFunctorIso
  have : SSet.InnerFibration (DiagSet.toSSet.map p) :=
    innerFibration_toSSet_map ((DiagSet.toInfty 1).map p) inferInstance
  have h₀ : HasLiftingProperty (SSet.toDiagSet.map sq₀.ι) p :=
    (sSetDiagSetAdj.hasLiftingProperty_iff _ _).2
      (SSet.innerAnodyneExtensions_pushoutObjObjι_join sq₀ hh _
        (SSet.mem_innerFibrations (DiagSet.toSSet.map p)))
  have h₁ : HasLiftingProperty sq.ι p :=
    (HasLiftingProperty.iff_of_arrow_iso_left (Arrow.isoMk
      (f := Arrow.mk (SSet.toDiagSet.map sq₀.ι)) (g := Arrow.mk sq.ι) (Iso.refl _)
      ((toDiagSetJoinFunctorIso.app L).app Δ[m])
      ((Category.id_comp _).trans (sq₀.map_ι toDiagSetJoinFunctorIso))) p).1 h₀
  exact (hasLiftingProperty_leibnizCoslice_iff sq p t).2 fun hsq _ ↦ h₁.sq_hasLift hsq

theorem DiagSet.isRightFibration_leibnizSlice_of_sliceFibrancy
    (hslice : ∀ ⦃A B E S : DiagSet.{u}⦄ (j : A ⟶ B) [Mono j] (p : E ⟶ S)
      [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
      (t : B ⟶ E), Fibration ((DiagSet.toInfty 1).map (WithInitial.leibnizSlice j p t)))
    (hcoslice : ∀ ⦃A B E S : DiagSet.{u}⦄ (j : A ⟶ B) [Mono j] (p : E ⟶ S)
      [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
      (t : B ⟶ E), Fibration ((DiagSet.toInfty 1).map (WithInitial.leibnizCoslice j p t)))
    (hcofib : ∀ ⦃B X : DiagSet.{u}⦄ [IsFibrant ((DiagSet.toInfty 1).obj X)] (t : B ⟶ X),
      IsFibrant ((DiagSet.toInfty 1).obj ((WithInitial.coslice B).obj (Under.mk t))))
    {A B : DiagSet.{u}} (j : A ⟶ B) [Mono j] (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (t : B ⟶ E) :
    DiagSet.IsRightFibration (WithInitial.leibnizSlice j p t) := by
  have := hslice j p t
  have := isFibrant_leibnizSlice_target_of_sliceFibrancy hslice j p t
  refine DiagSet.isRightFibration_of_hasLiftingProperty_of_sliceFibrancy hslice _ fun n ↦ ?_
  let sq := Functor.PushoutObjObj.ofHasPushout 𝒥
    (SSet.toDiagSet.map (SSet.joinMap ∂Δ[n].ι (𝟙 Δ[0]))) j
  refine (hasLiftingProperty_pushoutObjObj_ι_iff sq p).1 ⟨fun {a b} hsq ↦ ?_⟩ t
  exact (hasLiftingProperty_leibnizCoslice_iff sq p _).1
    (rlp_monomorphisms_leibnizCoslice_toDiagSet_map_of_sliceFibrancy hcoslice hcofib
      (SSet.rightAnodyneExtensions_joinMap_id ∂Δ[n].ι) p _ j
      (MorphismProperty.monomorphisms.infer_property j))
    hsq rfl

theorem DiagSet.isRightFibration_sliceProj_of_sliceFibrancy
    (hslice : ∀ ⦃A B E S : DiagSet.{u}⦄ (j : A ⟶ B) [Mono j] (p : E ⟶ S)
      [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
      (t : B ⟶ E), Fibration ((DiagSet.toInfty 1).map (WithInitial.leibnizSlice j p t)))
    (hcoslice : ∀ ⦃A B E S : DiagSet.{u}⦄ (j : A ⟶ B) [Mono j] (p : E ⟶ S)
      [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
      (t : B ⟶ E), Fibration ((DiagSet.toInfty 1).map (WithInitial.leibnizCoslice j p t)))
    (hcofib : ∀ ⦃B X : DiagSet.{u}⦄ [IsFibrant ((DiagSet.toInfty 1).obj X)] (t : B ⟶ X),
      IsFibrant ((DiagSet.toInfty 1).obj ((WithInitial.coslice B).obj (Under.mk t))))
    {B X : DiagSet.{u}} [hX : IsFibrant ((DiagSet.toInfty 1).obj X)] (t : B ⟶ X) :
    DiagSet.IsRightFibration ((sliceProj B).app (Under.mk t)) := by
  have : Fibration ((DiagSet.toInfty 1).map (terminal.from X)) :=
    (isFibrant_iff_of_isTerminal _ terminalIsTerminal).1 hX
  have h := DiagSet.isRightFibration_leibnizSlice_of_sliceFibrancy hslice hcoslice hcofib
    (initial.to B) (terminal.from X) t
  refine ⟨fibration_sliceProj_of_sliceFibrancy hslice t, fun K L i _ ↦ ?_⟩
  let W := (MorphismProperty.ofHoms fun _ : Unit ↦ joinMap i (𝟙 (ball.{u} atomPoint))).rlp
  have hW : W ((sliceProj B).app (Under.mk t)) := by
    rw [sliceProj_app_eq_leibnizSlice]
    exact comp_mem _ _ _ (fun _ _ _ ⟨_⟩ ↦ h.hasLiftingProperty_joinMap i)
      (comp_mem _ _ _ (of_isIso _ _) (of_isIso _ _))
  exact hW _ (MorphismProperty.ofHoms.mk ())

theorem DiagSet.isRightFibration_iff_rightFibrations_toSSet (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)] :
    DiagSet.IsRightFibration p ↔ SSet.rightFibrations (DiagSet.toSSet.map p) :=
  DiagSet.isRightFibration_iff_rightFibrations_toSSet_of_sliceFibrancy
    (fun _ _ _ _ j _ _ hp _ t ↦ Atoms.Diagrammatic.fibration_leibnizSlice j (hp := hp) t) p

theorem DiagSet.isRightFibration_leibnizSlice {A B : DiagSet.{u}} (j : A ⟶ B) [Mono j]
    (p : E ⟶ S) [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (t : B ⟶ E) :
    DiagSet.IsRightFibration (WithInitial.leibnizSlice j p t) :=
  DiagSet.isRightFibration_leibnizSlice_of_sliceFibrancy
    (fun _ _ _ _ j _ _ hp _ t ↦ Atoms.Diagrammatic.fibration_leibnizSlice j (hp := hp) t)
    (fun _ _ _ _ j _ _ hp _ t ↦ Atoms.Diagrammatic.fibration_leibnizCoslice j (hp := hp) t)
    (fun _ _ hX t ↦ Atoms.Diagrammatic.isFibrant_coslice_of_isFibrant (hX := hX) t) j p t

theorem DiagSet.isRightFibration_sliceProj {B X : DiagSet.{u}}
    [IsFibrant ((DiagSet.toInfty 1).obj X)] (t : B ⟶ X) :
    DiagSet.IsRightFibration ((sliceProj B).app (Under.mk t)) :=
  DiagSet.isRightFibration_sliceProj_of_sliceFibrancy
    (fun _ _ _ _ j _ _ hp _ t ↦ Atoms.Diagrammatic.fibration_leibnizSlice j (hp := hp) t)
    (fun _ _ _ _ j _ _ hp _ t ↦ Atoms.Diagrammatic.fibration_leibnizCoslice j (hp := hp) t)
    (fun _ _ hX t ↦ Atoms.Diagrammatic.isFibrant_coslice_of_isFibrant (hX := hX) t) t

end Atoms.Diagrammatic
