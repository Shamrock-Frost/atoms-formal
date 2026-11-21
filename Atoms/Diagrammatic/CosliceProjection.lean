import Atoms.Diagrammatic.Joyal.GrayHomComparison
import Atoms.Diagrammatic.Joyal.JoinDualQuillen
import Atoms.Diagrammatic.SimplicialJoin
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.CosliceProjection

open CategoryTheory CategoryTheory.WithInitial Limits Opposite Simplicial MorphismProperty
  HomotopicalAlgebra Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open scoped DiagSet.Join

noncomputable def cosliceProj {A : DiagSet.{u}} (t : Under A) : (coslice A).obj t ⟶ t.right :=
  joinInclRight A _ ≫ ((joinLeftUnderAdjunction A).counit.app t).right

theorem comp_cosliceProj {A K : DiagSet.{u}} {t : Under A} (ψ : K ⟶ (coslice A).obj t) :
    ψ ≫ cosliceProj t =
      joinInclRight A K ≫ (((joinLeftUnderAdjunction A).homEquiv _ _).symm ψ).right := by
  rw [Adjunction.homEquiv_counit, Under.comp_right, cosliceProj]
  exact (joinInclRight_comp_joinMap_assoc (𝟙 A) ψ _).symm

@[reassoc]
theorem cosliceRes_app_comp_cosliceProj {A' A : DiagSet.{u}} (g : A' ⟶ A) (t : Under A) :
    (cosliceRes g).app t ≫ cosliceProj ((Under.map g).obj t) = cosliceProj t := by
  have h := homEquiv_symm_comp_cosliceRes_app_right g (𝟙 ((coslice A).obj t))
  rw [Category.id_comp] at h
  rw [comp_cosliceProj, h]
  refine (joinInclRight_comp_joinMap_assoc g (𝟙 _) _).trans ?_
  exact (Category.id_comp _).trans ((comp_cosliceProj (𝟙 _)).symm.trans (Category.id_comp _))

private theorem hasLiftingProperty_cosliceProj {A X K L : DiagSet.{u}} (t : A ⟶ X) (i : K ⟶ L)
    (hι : HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout 𝒥 (initial.to A) i).ι
      (terminal.from X)) :
    HasLiftingProperty i (cosliceProj (Under.mk t)) := by
  let sq := Functor.PushoutObjObj.ofHasPushout 𝒥 (initial.to A) i
  have hE : ∀ c : Atomᵒᵖ, IsEmpty ((⊥_ DiagSet.{u}).obj c) := fun c ↦
    ⟨fun e ↦ PEmpty.elim ((initialIsInitial.to ((Functor.const Atomᵒᵖ).obj PEmpty)).app c e)⟩
  have hK : IsIso (joinInclRight (⊥_ DiagSet.{u}) K) := isIso_joinInclRight_of_isEmpty _ _
  have hL : IsIso (joinInclRight (⊥_ DiagSet.{u}) L) := isIso_joinInclRight_of_isEmpty _ _
  refine ⟨fun {a b} hsq ↦ ?_⟩
  let a' := ((joinLeftUnderAdjunction A).homEquiv K (Under.mk t)).symm a
  have ha' : joinInclRight A K ≫ a'.right = i ≫ b := (comp_cosliceProj a).symm.trans hsq.w
  let b' : join (⊥_ DiagSet.{u}) L ⟶ X := inv (joinInclRight (⊥_ DiagSet.{u}) L) ≫ b
  have hb' : joinInclRight (⊥_ DiagSet.{u}) L ≫ b' = b := IsIso.hom_inv_id_assoc _ b
  have hc : joinMap (initial.to A) (𝟙 K) ≫ a'.right = joinMap (𝟙 (⊥_ DiagSet.{u})) i ≫ b' := by
    refine (cancel_epi (joinInclRight (⊥_ DiagSet.{u}) K)).1 ?_
    refine ((joinInclRight_comp_joinMap_assoc (initial.to A) (𝟙 K) _).trans
      ((Category.id_comp _).trans ha')).trans ?_
    exact ((joinInclRight_comp_joinMap_assoc (𝟙 _) i _).trans (congrArg (i ≫ ·) hb')).symm
  let c : sq.pt ⟶ X := sq.isPushout.desc a'.right b' hc
  have sqc : CommSq c sq.ι (terminal.from X) (terminal.from _) := ⟨terminal.hom_ext _ _⟩
  have h₁ : joinMap (𝟙 A) i ≫ sqc.lift = a'.right :=
    (congrArg (· ≫ sqc.lift) sq.inl_ι.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (sq.inl ≫ ·) sqc.fac_left).trans (sq.isPushout.inl_desc _ _ _)))
  have h₂ : joinInclRight A L ≫ sqc.lift = b := by
    have e : joinInclRight (⊥_ DiagSet.{u}) L ≫ sq.inr ≫ sq.ι = joinInclRight A L :=
      (congrArg (_ ≫ ·) sq.inr_ι).trans ((joinInclRight_comp_joinMap (initial.to A) (𝟙 L)).trans
        (Category.id_comp _))
    refine (congrArg (· ≫ sqc.lift) e.symm).trans ((Category.assoc _ _ _).trans ?_)
    exact (congrArg (joinInclRight (⊥_ DiagSet.{u}) L ≫ ·) ((Category.assoc _ _ _).trans
      ((congrArg (sq.inr ≫ ·) sqc.fac_left).trans (sq.isPushout.inr_desc _ _ _)))).trans hb'
  have h₀ : joinInclLeft A L ≫ sqc.lift = t := by
    have e : joinInclLeft A K ≫ joinMap (𝟙 A) i = joinInclLeft A L :=
      (joinInclLeft_comp_joinMap (𝟙 A) i).trans (Category.id_comp _)
    exact (congrArg (· ≫ sqc.lift) e.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (joinInclLeft A K ≫ ·) h₁).trans (Under.w a')))
  refine ⟨⟨{ l := (joinLeftUnderAdjunction A).homEquiv L (Under.mk t) (Under.homMk sqc.lift h₀)
             fac_left := ?_
             fac_right := ?_ }⟩⟩
  · refine ((joinLeftUnderAdjunction A).homEquiv_naturality_left i _).symm.trans ?_
    exact (Equiv.eq_symm_apply _).1 (Under.UnderMorphism.ext h₁)
  · rw [comp_cosliceProj, Equiv.symm_apply_apply]
    exact h₂

theorem fibration_cosliceProj {A X : DiagSet.{u}} [hX : IsFibrant ((DiagSet.toInfty 1).obj X)]
    (t : A ⟶ X) : Fibration ((DiagSet.toInfty 1).map (cosliceProj (Under.mk t))) := by
  have hp : Fibration ((DiagSet.toInfty 1).map (terminal.from X)) :=
    (isFibrant_iff_of_isTerminal _ terminalIsTerminal).1 hX
  rw [fibration_iff, ← trivialCofibrations_rlp]
  intro K L i hi
  exact hasLiftingProperty_cosliceProj t i
    ((hp.mem : reversibleCylinder.{u}.fibrations (inftyGenerators 1) (terminal.from X)) _
      (trivialCofibration_toInfty_pushoutObjObj_ι_of_trivialCofibration_right (initial.to A)
        (g := i) hi))

private noncomputable abbrev cosliceAdjunctionDiagSet (K : SSet.{u}) :
    SSet.toDiagSet ⋙ joinLeftUnder (SSet.toDiagSet.obj K) ⊣
      coslice (SSet.toDiagSet.obj K) ⋙ DiagSet.toSSet :=
  sSetDiagSetAdj.comp (joinLeftUnderAdjunction (SSet.toDiagSet.obj K))

private noncomputable abbrev cosliceAdjunctionSSet (K : SSet.{u}) :
    SSet.toDiagSet ⋙ joinLeftUnder (SSet.toDiagSet.obj K) ⊣
      Under.post DiagSet.toSSet ⋙ Under.map (sSetDiagSetAdj.unit.app K) ⋙ SSet.coslice K :=
  ((SSet.joinLeftUnderAdjunction K).comp (Under.postAdjunctionLeft sSetDiagSetAdj)).ofNatIsoLeft
    (toDiagSetJoinLeftUnderIso K)

private theorem joinInclRight_comp_cosliceAdjunctionDiagSet_counit_app_right (K : SSet.{u})
    (p : Under (SSet.toDiagSet.obj K)) :
    joinInclRight _ _ ≫ ((cosliceAdjunctionDiagSet K).counit.app p).right =
      (sSetDiagSetAdj.homEquiv _ _).symm (DiagSet.toSSet.map (cosliceProj p)) := by
  refine (joinInclRight_comp_joinMap_assoc (𝟙 _) (sSetDiagSetAdj.counit.app _)
    ((joinLeftUnderAdjunction (SSet.toDiagSet.obj K)).counit.app p).right).trans ?_
  exact (sSetDiagSetAdj.counit.naturality _).symm.trans (sSetDiagSetAdj.homEquiv_counit _ _ _).symm

private theorem joinInclRight_comp_cosliceAdjunctionSSet_counit_app_right (K : SSet.{u})
    (p : Under (SSet.toDiagSet.obj K)) :
    joinInclRight _ _ ≫ ((cosliceAdjunctionSSet K).counit.app p).right =
      (sSetDiagSetAdj.homEquiv _ _).symm (SSet.cosliceπ _) :=
  (Category.assoc _ _ _).symm.trans ((((Iso.comp_inv_eq _).mpr
    (toDiagSet_map_joinInclRight_comp_toDiagSetJoinIso_hom K _).symm) =≫ _).trans
      ((Functor.map_comp_assoc _ _ _ _).symm.trans (sSetDiagSetAdj.homEquiv_counit _ _ _).symm))

@[reassoc]
theorem toSSetCosliceIso_hom_app_comp_cosliceπ (K : SSet.{u})
    (p : Under (SSet.toDiagSet.obj K)) :
    (toSSetCosliceIso K).hom.app p ≫ SSet.cosliceπ _ = DiagSet.toSSet.map (cosliceProj p) := by
  have e := ((cosliceAdjunctionSSet K).homEquiv_counit _ _ _).symm.trans
    (Adjunction.homEquiv_symm_rightAdjointUniq_hom_app (cosliceAdjunctionDiagSet K)
      (cosliceAdjunctionSSet K) p)
  refine (sSetDiagSetAdj.homEquiv _ _).symm.injective ?_
  refine (sSetDiagSetAdj.homEquiv_naturality_left_symm _ _).trans ?_
  refine (congrArg (_ ≫ ·)
    (joinInclRight_comp_cosliceAdjunctionSSet_counit_app_right K p).symm).trans ?_
  refine (joinInclRight_comp_joinMap_assoc (𝟙 _) _ _).symm.trans ?_
  exact (congrArg (fun f ↦ joinInclRight _ _ ≫ f.right) e).trans
    (joinInclRight_comp_cosliceAdjunctionDiagSet_counit_app_right K p)

theorem rlp_I_toSSet_map_cosliceProj_vertexHom_iff {X : DiagSet.{u}} (x : X.Vertex) :
    SSet.modelCategoryQuillen.I.rlp
        (DiagSet.toSSet.map (cosliceProj (Under.mk (vertexHom x)))) ↔
      SSet.modelCategoryQuillen.I.rlp
        (SSet.cosliceπ (Under.mk (SSet.yonedaEquiv.symm (X.vertexEquivSSet x)))) := by
  let e := pointIsoToDiagSetStdSimplex.{u}
  let t : Under (ball.{u} atomPoint) := Under.mk (vertexHom x)
  have : IsIso ((cosliceRes e.inv).app t) := isIso_cosliceRes_app e.inv t
  have h₁ : SSet.modelCategoryQuillen.I.rlp (DiagSet.toSSet.map (cosliceProj t)) ↔
      SSet.modelCategoryQuillen.I.rlp
        (DiagSet.toSSet.map (cosliceProj ((Under.map e.inv).obj t))) := by
    have e₁ : DiagSet.toSSet.map (cosliceProj t) = DiagSet.toSSet.map ((cosliceRes e.inv).app t) ≫
        DiagSet.toSSet.map (cosliceProj ((Under.map e.inv).obj t)) :=
      (congrArg DiagSet.toSSet.map (cosliceRes_app_comp_cosliceProj e.inv t).symm).trans
        (DiagSet.toSSet.map_comp _ _)
    exact (iff_of_eq (congrArg _ e₁)).trans
      ((SSet.modelCategoryQuillen.I.rlp).cancel_left_of_respectsIso _ _)
  have h₂ : SSet.modelCategoryQuillen.I.rlp
        (DiagSet.toSSet.map (cosliceProj ((Under.map e.inv).obj t))) ↔
      SSet.modelCategoryQuillen.I.rlp (SSet.cosliceπ
        ((Under.post DiagSet.toSSet ⋙ Under.map (sSetDiagSetAdj.unit.app Δ[0])).obj
          ((Under.map e.inv).obj t))) := by
    rw [← toSSetCosliceIso_hom_app_comp_cosliceπ]
    exact (SSet.modelCategoryQuillen.I.rlp).cancel_left_of_respectsIso
      ((toSSetCosliceIso Δ[0]).app ((Under.map e.inv).obj t)).hom _
  have h₃ : sSetDiagSetAdj.unit.app Δ[0] ≫ DiagSet.toSSet.map (e.inv ≫ vertexHom x) =
      SSet.yonedaEquiv.symm (X.vertexEquivSSet x) := by
    rw [Functor.map_comp, ← Category.assoc, ← toSSetPoint_comp_toSSet_map_vertexHom]
    congr 1
    exact (isTerminalBallAtomPoint.isTerminalObj DiagSet.toSSet _).hom_ext _ _
  have hcongr : ∀ {f f' : Δ[0] ⟶ DiagSet.toSSet.obj X}, f = f' →
      (SSet.modelCategoryQuillen.I.rlp (SSet.cosliceπ (Under.mk f)) ↔
        SSet.modelCategoryQuillen.I.rlp (SSet.cosliceπ (Under.mk f'))) := by
    rintro f _ rfl
    exact Iff.rfl
  exact h₁.trans (h₂.trans (hcongr h₃))

end Atoms.Diagrammatic
