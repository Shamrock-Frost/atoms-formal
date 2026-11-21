import Atoms.Diagrammatic.Joyal.RelativeCylinder
import Atoms.Diagrammatic.MappingSpaceComparison
import Atoms.Diagrammatic.MappingFrames
import Atoms.Diagrammatic.Suspension.Quillen
import Atoms.Homotopical.Simplicial.FrameComparison

open CategoryTheory Limits Simplicial HomotopicalAlgebra
open Atoms.Homotopical Atoms.Shape SSet.modelCategoryQuillen

universe u

namespace Atoms.Diagrammatic

local instance (n : ℕ∞) : HasLimits (DiagSet.Infty.{u} n) :=
  inferInstanceAs (HasLimits DiagSet.{u})
local instance (n : ℕ∞) : HasColimits (DiagSet.Infty.{u} n) :=
  inferInstanceAs (HasColimits DiagSet.{u})

noncomputable def relativeCylinderPointIso {V A : DiagSet.{u}} (i : V ⟶ A) :
    (relativeCylinder i).obj (ball.{u} atomPoint) ≅ Under.mk i := by
  let l := pushout.inl ((grayTensorLeft (ball.{u} atomPoint)).map i)
    (grayTensorSnd (ball.{u} atomPoint) V)
  have : IsIso (grayTensorSnd (ball.{u} atomPoint) A) :=
    isIso_grayTensorSnd_ballAtomSimplexZero A
  have : IsIso (grayTensorSnd (ball.{u} atomPoint) V) :=
    isIso_grayTensorSnd_ballAtomSimplexZero V
  refine CategoryTheory.Under.isoMk
    ((asIso l).symm ≪≫ asIso (grayTensorSnd (ball.{u} atomPoint) A)) ?_
  change pushout.inr _ _ ≫ inv l ≫ grayTensorSnd (ball.{u} atomPoint) A = i
  apply (cancel_epi (grayTensorSnd (ball.{u} atomPoint) V)).1
  rw [← pushout.condition_assoc, IsIso.hom_inv_id_assoc, grayTensorLeft_map_grayTensorSnd]

noncomputable def suspensionRelativeCylinderPointIso :
    (SSet.toDiagSetInftyZero ⋙ bipointedSuspensionInfty 0).obj Δ[0] ≅
      (SSet.toDiagSetInftyZero ⋙ relativeCylinderInfty intervalBoundaryι).obj Δ[0] :=
  bipointedSuspension.mapIso (toDiagSetObjStdSimplexIso 0) ≪≫
    bipointedSuspensionPointIso ≪≫ (relativeCylinderPointIso intervalBoundaryι).symm ≪≫
      (relativeCylinder intervalBoundaryι).mapIso (toDiagSetObjStdSimplexIso 0).symm

theorem bipointedHomRelativeMappingSpaceComparison_of_frame
    (X : Under ((DiagSet.toInfty 1).obj pointPair.{u})) (Y : SimplicialFrame X) :
    ∃ f : DiagSet.toSSet.obj (bipointedHom.obj X) ⟶
      DiagSet.toSSet.obj (relativeMappingSpace intervalBoundaryι X.hom), WeakEquivalence f :=
  isQuillen_sSetDiagSetAdjZero_comp_bipointedSuspensionAdjunctionInfty.{u}
    |>.exists_weakEquivalence_of_point_iso
      (isQuillenEquivalence_sSetDiagSetAdjZero.{u}.toIsQuillen.comp
        (isQuillen_relativeCylinderAdjunctionInfty.{u} intervalBoundaryι
          exists_intervalBoundaryι_app_eq)) Y suspensionRelativeCylinderPointIso.{u}

theorem bipointedHomRelativeMappingSpaceComparison
    (X : Under ((DiagSet.toInfty 1).obj pointPair.{u})) [hX : IsFibrant X] :
    ∃ f : DiagSet.toSSet.obj (bipointedHom.obj X) ⟶
      DiagSet.toSSet.obj (relativeMappingSpace intervalBoundaryι X.hom), WeakEquivalence f := by
  let adj₁ := DiagSet.Infty.sSetDiagSetAdjZero.{u}.comp (bipointedSuspensionAdjunctionInfty 0)
  let adj₂ := DiagSet.Infty.sSetDiagSetAdjZero.{u}.comp
    (relativeCylinderAdjunctionInfty intervalBoundaryι.{u})
  have h₁ : adj₁.IsQuillen :=
    isQuillen_sSetDiagSetAdjZero_comp_bipointedSuspensionAdjunctionInfty.{u}
  have h₂ : adj₂.IsQuillen := isQuillenEquivalence_sSetDiagSetAdjZero.{u}.toIsQuillen.comp
    (isQuillen_relativeCylinderAdjunctionInfty.{u} intervalBoundaryι
      exists_intervalBoundaryι_app_eq)
  let G₁ := bipointedHomInfty 0 ⋙ DiagSet.Infty.toSSetZero.{u}
  let G₂ := relativeMappingSpaceInfty intervalBoundaryι ⋙ DiagSet.Infty.toSSetZero.{u}
  let φ := MorphismProperty.factorizationData
    (cofibrations (Under ((DiagSet.toInfty 1).obj pointPair.{u}))) (trivialFibrations _)
    (initial.to X)
  have hp : WeakEquivalence φ.p := (weakEquivalence_iff _).2 φ.hp.2
  have hpf : Fibration φ.p := (HomotopicalAlgebra.fibration_iff _).2 φ.hp.1
  have hQf : IsFibrant φ.Z := isFibrant_of_fibration φ.p
  have hQi : Cofibration φ.i := (HomotopicalAlgebra.cofibration_iff _).2 φ.hi
  have hQc : IsCofibrant φ.Z := by
    rw [isCofibrant_iff, Subsingleton.elim (initial.to φ.Z) φ.i]
    exact hQi
  have hSc : IsCofibrant ((DiagSet.toInfty 1).obj pointPair.{u}) := by
    rw [HomotopicalAlgebra.isCofibrant_iff, HomotopicalAlgebra.cofibration_iff]
    exact MorphismProperty.monomorphisms.infer_property
      (initial.to (pointPair.{u} : DiagSet.{u}))
  obtain ⟨Z, Y, η, hη⟩ :=
    @exists_framed_replacement_under _ hSc φ.Z hQc
  have hX₁ : IsFibrant (C := Under (pointPairInfty.{u} (0 + 1))) X := hX
  have hX₂ : IsFibrant (C := Under ((DiagSet.toInfty 1).obj intervalBoundary.{u})) X := hX
  have hQf₁ : IsFibrant (C := Under (pointPairInfty.{u} (0 + 1))) φ.Z := hQf
  have hQf₂ : IsFibrant
      (C := Under ((DiagSet.toInfty 1).obj intervalBoundary.{u})) φ.Z := hQf
  have hη₁ : WeakEquivalence (C := Under (pointPairInfty.{u} (0 + 1))) η := hη
  have hp₁₀ : WeakEquivalence (C := Under (pointPairInfty.{u} (0 + 1))) φ.p := hp
  have hp₂₀ : WeakEquivalence
      (C := Under ((DiagSet.toInfty 1).obj intervalBoundary.{u})) φ.p := hp
  obtain ⟨g, hg⟩ := h₁.exists_weakEquivalence_of_point_iso_of_replacement h₂ Y η
    suspensionRelativeCylinderPointIso.{u}
  have hp₁ : WeakEquivalence (G₁.map φ.p) := h₁.weakEquivalence_map_of_isFibrant φ.p
  have hp₂ : WeakEquivalence (G₂.map φ.p) := h₂.weakEquivalence_map_of_isFibrant φ.p
  have hGX : IsFibrant (G₁.obj X) := h₁.isFibrant_obj X
  have hGQ : IsFibrant (G₁.obj φ.Z) := h₁.isFibrant_obj φ.Z
  have (K : SSet.{u}) : IsCofibrant K := cofibration_of_mono _
  obtain ⟨r, h₁, h₂⟩ := RightHomotopyClass.whitehead (G₁.map φ.p)
  have hr : WeakEquivalence r := weakEquivalence_of_rightHomotopyRel r (G₁.map φ.p) h₂ h₁
  exact ⟨r ≫ g ≫ G₂.map φ.p, (HomotopicalAlgebra.weakEquivalence_iff _).2
    ((weakEquivalences SSet.{u}).comp_mem _ _ hr.mem
      ((weakEquivalences SSet.{u}).comp_mem _ _ hg.mem hp₂.mem))⟩

theorem bipointedHomGrayMappingSpaceComparison {X : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (x y : X.Vertex) :
    ∃ f : DiagSet.toSSet.obj (bipointedHom.obj (X.bipoint x y)) ⟶
      DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor, WeakEquivalence f := by
  let B : Under ((DiagSet.toInfty 1).obj pointPair.{u}) := X.bipoint x y
  have hB : IsFibrant B := (isFibrant_under_iff _ B).2
    ((isFibrant_infty_iff 1 X).2 hX)
  obtain ⟨f, hf⟩ := bipointedHomRelativeMappingSpaceComparison B
  let e : DiagSet.toSSet.obj (relativeMappingSpace intervalBoundaryι B.hom) ≅
      DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor :=
    (DiagSet.toSSet.mapIso (X.mappingSpaceIsoRelativeMappingSpace x y)).symm
  have hi : WeakEquivalence e.hom := inferInstance
  exact ⟨f ≫ e.hom, inferInstance⟩

theorem bipointedHomMappingSpaceComparison_exists {X : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (x y : X.Vertex) :
    ∃ (Z : SSet.{u}) (l : Z ⟶ DiagSet.toSSet.obj (bipointedHom.obj (X.bipoint x y)))
      (r : Z ⟶ SSet.mappingSpace (DiagSet.toSSet.obj X)
        (X.vertexEquivSSet x) (X.vertexEquivSSet y)),
      WeakEquivalence l ∧ WeakEquivalence r := by
  obtain ⟨f, hf⟩ := bipointedHomGrayMappingSpaceComparison hX x y
  have hK : (DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor).KanComplex :=
    kanComplex_toSSet_mappingSpace hX x y
  have hH : (DiagSet.toSSet.obj (bipointedHom.obj (X.bipoint x y))).KanComplex :=
    kanComplex_toSSet_obj
      ((isFibrant_infty_iff 0 _).1 (isFibrant_bipointedHom hX))
  have (K : SSet.{u}) : IsCofibrant K := cofibration_of_mono _
  obtain ⟨g, h₁, h₂⟩ := RightHomotopyClass.whitehead f
  have hg : WeakEquivalence g := weakEquivalence_of_rightHomotopyRel g f h₂ h₁
  obtain ⟨Z, l, r, hl, hr⟩ := mappingSpaceComparison_exists hX x y
  exact ⟨Z, l ≫ g, r, inferInstance, hr⟩

theorem bipointedHomGrayMappingSpaceComparison_exists {X : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (x y : X.Vertex) :
    ∃ (Z : DiagSet.{u}) (l : Z ⟶ bipointedHom.obj (X.bipoint x y))
      (r : Z ⟶ (X.mappingSpace x y).toFunctor),
      WeakEquivalence ((DiagSet.toInfty 0).map l) ∧
        WeakEquivalence ((DiagSet.toInfty 0).map r) := by
  let A : DiagSet.Infty.{u} 0 := bipointedHom.obj (X.bipoint x y)
  let B : DiagSet.Infty.{u} 0 := (X.mappingSpace x y).toFunctor
  let adj := DiagSet.Infty.sSetDiagSetAdjZero.{u}
  have hA : IsFibrant A := isFibrant_bipointedHom hX
  have hB : IsFibrant B := (isFibrant_infty_iff 0 _).2
    (X.isInftyCategory_zero_mappingSpace hX x y)
  have (K : SSet.{u}) : IsCofibrant K := cofibration_of_mono _
  have hc (T : DiagSet.Infty.{u} 0) [IsFibrant T] :
      WeakEquivalence (C := DiagSet.Infty.{u} 0) (adj.counit.app T) := by
    have hQ : adj.IsQuillenEquivalence := isQuillenEquivalence_sSetDiagSetAdjZero.{u}
    apply (hQ.weakEquivalence_iff (X := T) (adj.counit.app T)).2
    rw [← adj.homEquiv_symm_id, Equiv.apply_symm_apply]
    infer_instance
  obtain ⟨f, hf⟩ := bipointedHomGrayMappingSpaceComparison hX x y
  have hLf : WeakEquivalence (C := DiagSet.Infty.{u} 0)
      (SSet.toDiagSetInftyZero.map f) :=
    isQuillenEquivalence_sSetDiagSetAdjZero.{u}.toIsQuillen.weakEquivalence_map f
  have hcB : WeakEquivalence (C := DiagSet.Infty.{u} 0) (adj.counit.app B) := hc B
  exact ⟨SSet.toDiagSet.obj (DiagSet.toSSet.obj A), adj.counit.app A,
    SSet.toDiagSet.map f ≫ adj.counit.app B, hc A,
    (HomotopicalAlgebra.weakEquivalence_iff _).2
      ((weakEquivalences (DiagSet.Infty.{u} 0)).comp_mem _ _ hLf.mem hcB.mem)⟩

theorem bipointedHomGraySimplicialSpan_exists {X : DiagSet.{u}}
    (hX : IsInftyCategory 1 X) (x y : X.Vertex) :
    ∃ (Z : SSet.{u}) (l : Z ⟶ DiagSet.toSSet.obj (bipointedHom.obj (X.bipoint x y)))
      (r : Z ⟶ DiagSet.toSSet.obj (X.mappingSpace x y).toFunctor),
      WeakEquivalence l ∧ WeakEquivalence r := by
  obtain ⟨f, hf⟩ := bipointedHomGrayMappingSpaceComparison hX x y
  exact ⟨_, 𝟙 _, f, inferInstance, hf⟩

theorem weakEquivalence_bipointedHom_map_iff_relativeMappingSpace_map
    {P P' : Under ((DiagSet.toInfty 1).obj pointPair.{u})} [hP : IsFibrant P]
    [hP' : IsFibrant P'] (φ : P ⟶ P') :
    WeakEquivalence (DiagSet.toSSet.map (bipointedHom.map φ)) ↔
      WeakEquivalence (DiagSet.toSSet.map
        ((relativeMappingSpaceFunctor intervalBoundaryι).map φ)) := by
  let adj₁ := DiagSet.Infty.sSetDiagSetAdjZero.{u}.comp (bipointedSuspensionAdjunctionInfty 0)
  let adj₂ := DiagSet.Infty.sSetDiagSetAdjZero.{u}.comp
    (relativeCylinderAdjunctionInfty intervalBoundaryι.{u})
  have h₁ : adj₁.IsQuillen :=
    isQuillen_sSetDiagSetAdjZero_comp_bipointedSuspensionAdjunctionInfty.{u}
  have h₂ : adj₂.IsQuillen := isQuillenEquivalence_sSetDiagSetAdjZero.{u}.toIsQuillen.comp
    (isQuillen_relativeCylinderAdjunctionInfty.{u} intervalBoundaryι
      exists_intervalBoundaryι_app_eq)
  let G₁ := bipointedHomInfty 0 ⋙ DiagSet.Infty.toSSetZero.{u}
  let G₂ := relativeMappingSpaceInfty intervalBoundaryι ⋙ DiagSet.Infty.toSSetZero.{u}
  let ρ := MorphismProperty.factorizationData
    (cofibrations (Under ((DiagSet.toInfty 1).obj pointPair.{u}))) (trivialFibrations _)
    (initial.to P)
  let ρ' := MorphismProperty.factorizationData
    (cofibrations (Under ((DiagSet.toInfty 1).obj pointPair.{u}))) (trivialFibrations _)
    (initial.to P')
  have hp : WeakEquivalence ρ.p := (weakEquivalence_iff _).2 ρ.hp.2
  have hp' : WeakEquivalence ρ'.p := (weakEquivalence_iff _).2 ρ'.hp.2
  have hpf : Fibration ρ.p := (HomotopicalAlgebra.fibration_iff _).2 ρ.hp.1
  have hpf' : Fibration ρ'.p := (HomotopicalAlgebra.fibration_iff _).2 ρ'.hp.1
  have hQf : IsFibrant ρ.Z := isFibrant_of_fibration ρ.p
  have hQf' : IsFibrant ρ'.Z := isFibrant_of_fibration ρ'.p
  have hQi : Cofibration ρ.i := (HomotopicalAlgebra.cofibration_iff _).2 ρ.hi
  have hQi' : Cofibration ρ'.i := (HomotopicalAlgebra.cofibration_iff _).2 ρ'.hi
  have hQc : IsCofibrant ρ.Z := by
    rw [isCofibrant_iff, Subsingleton.elim (initial.to ρ.Z) ρ.i]
    exact hQi
  have hQc' : IsCofibrant ρ'.Z := by
    rw [isCofibrant_iff, Subsingleton.elim (initial.to ρ'.Z) ρ'.i]
    exact hQi'
  have hSc : IsCofibrant ((DiagSet.toInfty 1).obj pointPair.{u}) := by
    rw [HomotopicalAlgebra.isCofibrant_iff, HomotopicalAlgebra.cofibration_iff]
    exact MorphismProperty.monomorphisms.infer_property
      (initial.to (pointPair.{u} : DiagSet.{u}))
  have sq : CommSq ρ'.i ρ.i ρ'.p (ρ.p ≫ φ) := ⟨initialIsInitial.hom_ext _ _⟩
  let q := sq.lift
  have hq : ρ.p ≫ φ = q ≫ ρ'.p := sq.fac_right.symm
  obtain ⟨Z, Z', Y, Y', η, η', ζ, ψ, hη, hη', hζ, hψ⟩ :=
    @exists_framed_replacement_under_map _ hSc ρ.Z ρ'.Z hQc hQc' q
  have hZ : IsFibrant Z := Y.isFibrant
  have hZ' : IsFibrant Z' := Y'.isFibrant
  have e₁ := (h₁.weakEquivalence_map_iff_of_comp_eq (hX := hQf) (hX' := hQf') (hZ := hP)
    (hZ' := hP') (hη := hp) (hη' := hp') ρ.p ρ'.p q φ hq).symm.trans
    (h₁.weakEquivalence_map_iff_of_comp_eq (hX := hQf) (hX' := hQf') (hZ := hZ) (hZ' := hZ')
      (hη := hη) (hη' := hη') η η' q ζ hζ)
  have e₂ := (h₂.weakEquivalence_map_iff_of_comp_eq (hX := hQf) (hX' := hQf') (hZ := hP)
    (hZ' := hP') (hη := hp) (hη' := hp') ρ.p ρ'.p q φ hq).symm.trans
    (h₂.weakEquivalence_map_iff_of_comp_eq (hX := hQf) (hX' := hQf') (hZ := hZ) (hZ' := hZ')
      (hη := hη) (hη' := hη') η η' q ζ hζ)
  exact e₁.trans ((h₁.weakEquivalence_map_iff_of_point_iso h₂ Y Y' ζ ψ hψ
    suspensionRelativeCylinderPointIso.{u}).trans e₂.symm)

end Atoms.Diagrammatic
