import Atoms.Homotopical.Cylinder.ModelStructure
import Atoms.Homotopical.Cylinder.Segment
import Atoms.Homotopical.Simplicial.KanDatum
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Quillen
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.FunctionSpace
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Spine
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.CoherentIso

open CategoryTheory Limits MorphismProperty Simplicial HomotopicalAlgebra

universe u

namespace Atoms.Homotopical

noncomputable def joyalPoint (b : Bool) : ⊤_ SSet.{u} ⟶ SSet.coherentIso.{u} :=
  (terminalIsoIsTerminal SSet.stdSimplex.isTerminalObj₀).hom ≫
    SSet.yonedaEquiv.symm (cond b SSet.coherentIso.x₁ SSet.coherentIso.x₀)

theorem joyalPoint_app_obj (b : Bool) (d : SimplexCategoryᵒᵖ) (t : (⊤_ SSet.{u}).obj d)
    (j : Fin (d.unop.len + 1)) :
    ((joyalPoint b).app d t).obj j = cond b WalkingIso.one WalkingIso.zero := by
  cases b <;> rfl

theorem isPullback_joyalPoint :
    IsPullback (initial.to (⊤_ SSet.{u})) (initial.to (⊤_ SSet.{u}))
      (joyalPoint false) (joyalPoint true) := by
  refine isPullback_of_app_ne joyalPoint fun a t₀ t₁ h ↦ ?_
  have := congrArg (fun s ↦ s.obj 0) h
  rw [joyalPoint_app_obj, joyalPoint_app_obj] at this
  exact Bool.false_ne_true (congrArg WalkingIso.equivBool this)

noncomputable def joyalInterval : SeparatingInterval SimplexCategory :=
  ⟨SSet.coherentIso.{u}, joyalPoint, isPullback_joyalPoint⟩

private noncomputable def vertexArrowIso (ε : Bool) :
    Arrow.mk (SSet.yonedaEquiv.symm (cond ε SSet.coherentIso.x₁ SSet.coherentIso.x₀) :
      Δ[0] ⟶ SSet.coherentIso.{u}) ≅ Arrow.mk (joyalPoint ε) :=
  Arrow.isoMk (terminalIsoIsTerminal SSet.stdSimplex.isTerminalObj₀).symm (Iso.refl _)
    (by simp [joyalPoint])

end Atoms.Homotopical

namespace SSet.modelCategoryJoyal

open Atoms.Homotopical

noncomputable scoped instance joyalModelCategory : ModelCategory SSet.{u} :=
  joyalInterval.cylinder.modelCategory innerHornInclusions innerHornInclusions_le_monomorphisms

scoped instance isCofibrant (A : SSet.{u}) : IsCofibrant A := by
  rw [isCofibrant_iff, cofibration_iff]
  exact MorphismProperty.monomorphisms.infer_property _

private def isofibrationsOfQuasicategories : MorphismProperty SSet.{u} :=
  fun X Y p ↦ X.Quasicategory ∧ Y.Quasicategory ∧ SSet.Isofibration p

private lemma quasicategory_terminal : (⊤_ SSet.{u}).Quasicategory := by
  have : IsIso (terminal.from (⊤_ SSet.{u})) :=
    isIso_of_isTerminal terminalIsTerminal terminalIsTerminal _
  rw [SSet.quasicategory_iff_innerFibration]
  exact ⟨rlp_of_isIso _ _⟩

private lemma isAnodyneClass_llp_isofibrationsOfQuasicategories :
    IsAnodyneClass joyalInterval.{u}.cylinder SSet.innerHornInclusions
      isofibrationsOfQuasicategories.llp where
  isSaturated := inferInstance
  generators_le := by
    rintro _ _ f hf _ _ p ⟨_, _, _⟩
    exact SSet.mem_innerFibrations p f hf
  endpointBox_mem := by
    rintro ε _ _ i _ _ _ p ⟨_, _, _⟩
    let sq := joyalInterval.{u}.endpointBoxPushoutObjObj ε i
    refine (HasLiftingProperty.iff_of_arrow_iso_left
      (show Arrow.mk sq.ι ≅ Arrow.mk sq.flipTensor.ι from Arrow.isoMk (Iso.refl _) (β_ _ _))
        p).2 ?_
    rw [MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff _
      (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p)]
    exact (HasLiftingProperty.iff_of_arrow_iso_left (vertexArrowIso ε) _).1
      (SSet.hasLiftingProperty_coherentIso_vertex_pullbackObjObjπ ε p i _)
  bothBox_mem := by
    rintro _ _ i _ hi E _ p ⟨_, _, _⟩
    let sq₁₃ :=
      Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom joyalInterval.{u}.boundary p
    refine (MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff
      (joyalInterval.{u}.bothBoxPushoutObjObj i) sq₁₃).2
        (hi _ ⟨?_, SSet.quasicategory_pullbackObjObj_pt p _ sq₁₃,
          SSet.isofibration_pullbackObjObjπ p _ sq₁₃⟩)
    exact (inferInstance : ((ihom SSet.coherentIso.{u}).obj E).Quasicategory)

private lemma anodyne_le_llp :
    joyalInterval.{u}.cylinder.anodyne SSet.innerHornInclusions ≤
      isofibrationsOfQuasicategories.llp :=
  joyalInterval.{u}.cylinder.anodyne_le _ _ isAnodyneClass_llp_isofibrationsOfQuasicategories

theorem isFibrant_iff_quasicategory (X : SSet.{u}) : IsFibrant X ↔ X.Quasicategory := by
  refine (ExactCylinder.modelCategory.isFibrant_iff _ _ _ X).trans ⟨fun h ↦ ?_,
    fun h _ _ f hf ↦ anodyne_le_llp f hf _ ⟨h, quasicategory_terminal, inferInstance⟩⟩
  rw [SSet.quasicategory_iff_innerFibration]
  exact ⟨fun _ _ f hf ↦ h f (joyalInterval.{u}.cylinder.le_anodyne _ f hf)⟩

theorem fibration_iff_isofibration {X Y : SSet.{u}} [X.Quasicategory] [Y.Quasicategory]
    (p : X ⟶ Y) : Fibration p ↔ SSet.Isofibration p := by
  rw [HomotopicalAlgebra.fibration_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hp : joyalInterval.{u}.cylinder.naiveFibrations SSet.innerHornInclusions p :=
      antitone_rlp (fun _ _ f hf ↦ ⟨joyalInterval.{u}.cylinder.anodyne_le_monomorphisms _
        SSet.innerHornInclusions_le_monomorphisms f hf,
        joyalInterval.{u}.cylinder.anodyne_le_weakEquivalences _
          SSet.innerHornInclusions_le_monomorphisms f hf⟩) p h
    have : SSet.InnerFibration p :=
      ⟨fun _ _ f hf ↦ hp f (joyalInterval.{u}.cylinder.le_anodyne _ f hf)⟩
    refine SSet.Isofibration.of_hasLiftingProperty_vertex p
      ((HasLiftingProperty.iff_of_arrow_iso_left (vertexArrowIso false) p).2 ?_)
    refine (HasLiftingProperty.iff_of_arrow_iso_left (Arrow.isoMk
      (f := Arrow.mk ((joyalInterval.{u}.cylinder.endpoint false).app (⊤_ SSet.{u})))
      (g := Arrow.mk (joyalPoint false)) (Iso.refl _)
      (@asIso _ _ _ _ (CartesianMonoidalCategory.fst _ (⊤_ SSet.{u}))
        (isIso_fst_terminal _)) ?_) p).1
        (hp _ (joyalInterval.{u}.cylinder.anodyne_endpoint _ false _))
    exact (congrArg (· ≫ joyalPoint false) (terminal.hom_ext (𝟙 _) (terminal.from _))).trans
      (CartesianMonoidalCategory.lift_fst _ _).symm
  · exact joyalInterval.{u}.cylinder.rlp_trivialCofibrations_of_rlp_anodyne _
      SSet.innerHornInclusions_le_monomorphisms p
      (fun _ _ f hf ↦ anodyne_le_llp f hf p ⟨inferInstance, inferInstance, h⟩)
      (fun _ _ f hf ↦ anodyne_le_llp f hf _ ⟨inferInstance, quasicategory_terminal, inferInstance⟩)

theorem innerAnodyneExtensions_le_trivialCofibrations :
    SSet.innerAnodyneExtensions.{u} ≤ trivialCofibrations SSet.{u} := by
  rw [SSet.innerAnodyneExtensions_eq_llp_rlp, ← fibrations_llp]
  refine antitone_llp ?_
  rw [← trivialCofibrations_rlp]
  refine antitone_rlp fun _ _ f hf ↦ ?_
  have hf' := joyalInterval.{u}.cylinder.le_anodyne _ f hf
  exact ⟨joyalInterval.{u}.cylinder.anodyne_le_monomorphisms _
    SSet.innerHornInclusions_le_monomorphisms f hf',
    joyalInterval.{u}.cylinder.anodyne_le_weakEquivalences _
      SSet.innerHornInclusions_le_monomorphisms f hf'⟩

theorem weakEquivalence_of_innerAnodyneExtensions {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : SSet.innerAnodyneExtensions f) : WeakEquivalence f :=
  ⟨(innerAnodyneExtensions_le_trivialCofibrations f hf).2⟩

theorem trivialCofibration_map_spineSubcomplex_ι {D : Type*} [Category D] [ModelCategory D]
    {F : SSet.{u} ⥤ D} {G : D ⥤ SSet.{u}} (adj : F ⊣ G) (h : adj.IsQuillen) (n : ℕ) :
    trivialCofibrations D (F.map (SSet.spineSubcomplex.{u} n).ι) :=
  h.trivialCofibrations_le _ (innerAnodyneExtensions_le_trivialCofibrations _
    (SSet.innerAnodyneExtensions_spineSubcomplex_ι n))

end SSet.modelCategoryJoyal
