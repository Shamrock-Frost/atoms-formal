import Atoms.Diagrammatic.Fibration.CartesianEdgeComparison
import Atoms.Diagrammatic.Joyal.JoinDualQuillen
import Atoms.Diagrammatic.SliceLifting

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra Simplicial Atoms.Shape
open CategoryTheory.WithInitial (slice sliceRes leibnizSlice leibnizSlice_fst_assoc
  leibnizSlice_snd isTerminalSliceObj)

universe u

namespace Atoms.Diagrammatic

theorem fibration_toInfty_one_map_iff {X Y : DiagSet.{u}} (p : X ⟶ Y) :
    Fibration ((DiagSet.toInfty 1).map p) ↔
      (reversibleCylinder.{u}.trivialCofibrations (inftyGenerators 1)).rlp p :=
  ⟨fun h ↦ h.mem, fun h ↦ ⟨h⟩⟩

instance isFibrant_toInfty_obj_terminal :
    IsFibrant ((DiagSet.toInfty 1).obj (⊤_ DiagSet.{u})) := by
  have : IsIso (terminal.from (⊤_ DiagSet.{u})) :=
    isIso_of_isTerminal terminalIsTerminal terminalIsTerminal _
  have h : Fibration ((DiagSet.toInfty 1).map (terminal.from (⊤_ DiagSet.{u}))) :=
    (fibration_toInfty_one_map_iff _).2 (of_isIso _ _)
  exact (isFibrant_iff_of_isTerminal _ terminalIsTerminal).2 h

private theorem slice_initial_map_eq {t s : Under (⊥_ DiagSet.{u})} (φ : t ⟶ s) :
    (slice (⊥_ DiagSet.{u})).map φ = (sliceEmptyIso initialIsInitial t).hom ≫ φ.right ≫
      (sliceEmptyIso initialIsInitial s).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv, sliceEmptyIso_hom, sliceEmptyIso_hom]
  exact (sliceProj (⊥_ DiagSet.{u})).naturality φ

theorem fibration_slice_map_of_sliceFibrancy
    (hslice : ∀ ⦃A B E S : DiagSet.{u}⦄ (j : A ⟶ B) [Mono j] (p : E ⟶ S)
      [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
      (t : B ⟶ E), Fibration ((DiagSet.toInfty 1).map (WithInitial.leibnizSlice j p t)))
    {B E S : DiagSet.{u}} (p : E ⟶ S) [Fibration ((DiagSet.toInfty 1).map p)]
    [IsFibrant ((DiagSet.toInfty 1).obj S)] (t : B ⟶ E) :
    Fibration ((DiagSet.toInfty 1).map
      ((slice B).map (Under.homMk p : Under.mk t ⟶ Under.mk (t ≫ p)))) := by
  rw [fibration_toInfty_one_map_iff, ← leibnizSlice_snd (initial.to B) p t]
  refine comp_mem _ _ _ ((fibration_toInfty_one_map_iff _).1 (hslice (initial.to B) p t))
    (MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ?_)
  rw [slice_initial_map_eq]
  exact comp_mem _ _ _ (of_isIso _ _) (comp_mem _ _ _ ((fibration_toInfty_one_map_iff p).1
    inferInstance) (of_isIso _ _))

theorem sliceProj_app_eq_leibnizSlice {B X : DiagSet.{u}} (t : B ⟶ X) :
    (sliceProj B).app (Under.mk t) = leibnizSlice (initial.to B) (terminal.from X) t ≫
      pullback.fst _ _ ≫ (sliceEmptyIso initialIsInitial
        ((Under.map (initial.to B)).obj (Under.mk t))).hom :=
  (sliceRestrict_app_comp_sliceProj_app (initial.to B) (Under.mk t)).symm.trans
    ((NatTrans.congr_app (sliceRestrict_eq (initial.to B)) (Under.mk t) =≫ _).trans
      (leibnizSlice_fst_assoc _ _ _ _).symm)

instance isIso_pullback_fst_leibnizSlice_initial {B X : DiagSet.{u}} (t : B ⟶ X) :
    IsIso (pullback.fst ((slice (⊥_ DiagSet.{u})).map (Under.homMk (terminal.from X) :
      Under.mk (initial.to B ≫ t) ⟶ Under.mk (initial.to B ≫ t ≫ terminal.from X)))
      ((sliceRes (initial.to B)).app (Under.mk (t ≫ terminal.from X)))) := by
  have := isIso_of_isTerminal (isTerminalSliceObj _ terminalIsTerminal)
    (isTerminalSliceObj _ terminalIsTerminal)
    ((sliceRes (initial.to B)).app (Under.mk (t ≫ terminal.from X)))
  exact MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms DiagSet.{u})
    (IsPullback.of_hasPullback _ _).flip this

theorem fibration_sliceProj_of_sliceFibrancy
    (hslice : ∀ ⦃A B E S : DiagSet.{u}⦄ (j : A ⟶ B) [Mono j] (p : E ⟶ S)
      [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
      (t : B ⟶ E), Fibration ((DiagSet.toInfty 1).map (WithInitial.leibnizSlice j p t)))
    {B X : DiagSet.{u}} [hX : IsFibrant ((DiagSet.toInfty 1).obj X)] (t : B ⟶ X) :
    Fibration ((DiagSet.toInfty 1).map ((sliceProj B).app (Under.mk t))) := by
  have : Fibration ((DiagSet.toInfty 1).map (terminal.from X)) :=
    (isFibrant_iff_of_isTerminal _ terminalIsTerminal).1 hX
  refine (fibration_toInfty_one_map_iff _).2 ?_
  rw [sliceProj_app_eq_leibnizSlice]
  exact comp_mem _ _ _ ((fibration_toInfty_one_map_iff _).1 (hslice (initial.to B) _ t))
    (comp_mem _ _ _ (of_isIso _ _) (of_isIso _ _))

theorem isFibrant_slice_of_sliceFibrancy
    (hslice : ∀ ⦃A B E S : DiagSet.{u}⦄ (j : A ⟶ B) [Mono j] (p : E ⟶ S)
      [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
      (t : B ⟶ E), Fibration ((DiagSet.toInfty 1).map (WithInitial.leibnizSlice j p t)))
    {B X : DiagSet.{u}} [hX : IsFibrant ((DiagSet.toInfty 1).obj X)] (t : B ⟶ X) :
    IsFibrant ((DiagSet.toInfty 1).obj ((slice B).obj (Under.mk t))) := by
  have := fibration_sliceProj_of_sliceFibrancy hslice t
  have : IsFibrant ((DiagSet.toInfty 1).obj ((Under.forget B).obj (Under.mk t))) := hX
  exact isFibrant_of_fibration ((DiagSet.toInfty 1).map ((sliceProj B).app (Under.mk t)))

theorem isFibrant_leibnizSlice_target_of_sliceFibrancy
    (hslice : ∀ ⦃A B E S : DiagSet.{u}⦄ (j : A ⟶ B) [Mono j] (p : E ⟶ S)
      [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
      (t : B ⟶ E), Fibration ((DiagSet.toInfty 1).map (WithInitial.leibnizSlice j p t)))
    {A B E S : DiagSet.{u}} (j : A ⟶ B) (p : E ⟶ S) [Fibration ((DiagSet.toInfty 1).map p)]
    [IsFibrant ((DiagSet.toInfty 1).obj S)] (t : B ⟶ E) :
    IsFibrant ((DiagSet.toInfty 1).obj (pullback ((slice A).map (Under.homMk p :
      Under.mk (j ≫ t) ⟶ Under.mk (j ≫ t ≫ p))) ((sliceRes j).app (Under.mk (t ≫ p))))) := by
  have := isFibrant_slice_of_sliceFibrancy hslice (t ≫ p)
  have : Fibration ((DiagSet.toInfty 1).map (pullback.snd ((slice A).map (Under.homMk p :
      Under.mk (j ≫ t) ⟶ Under.mk (j ≫ t ≫ p))) ((sliceRes j).app (Under.mk (t ≫ p))))) :=
    (fibration_toInfty_one_map_iff _).2 (MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback _ _)
      ((fibration_toInfty_one_map_iff _).1 (fibration_slice_map_of_sliceFibrancy hslice p _)))
  exact isFibrant_of_fibration ((DiagSet.toInfty 1).map (pullback.snd _ _))

instance mono_arrowOutput : Mono arrowOutput.{u} :=
  isTerminalBallAtomPoint.mono_from _

variable {E S : DiagSet.{u}} {x y : E.Vertex}

instance DiagSet.Edge.fibration_leibnizSlice (p : E ⟶ S) [Fibration ((DiagSet.toInfty 1).map p)]
    (e : E.Edge x y) :
    Fibration ((DiagSet.toInfty 1).map (e.leibnizSlice p)) :=
  Atoms.Diagrammatic.fibration_leibnizSlice arrowOutput _

instance DiagSet.Edge.isFibrant_sliceTarget (p : E ⟶ S) [Fibration ((DiagSet.toInfty 1).map p)]
    [IsFibrant ((DiagSet.toInfty 1).obj S)] (e : E.Edge x y) :
    IsFibrant ((DiagSet.toInfty 1).obj (e.sliceTarget p)) :=
  isFibrant_leibnizSlice_target_of_sliceFibrancy
    (fun _ _ _ _ j _ _ hp _ t ↦ Atoms.Diagrammatic.fibration_leibnizSlice j (hp := hp) t)
    arrowOutput p _

theorem DiagSet.isCartesianEdge_iff_isCartesianEdge_toSSet_of_fibration (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (e : E.Edge x y) :
    DiagSet.IsCartesianEdge p e ↔
      SSet.IsCartesianEdge (DiagSet.toSSet.map p)
        (SSet.yonedaEquiv.symm (E.edgeEquivSSet e).edge) :=
  DiagSet.isCartesianEdge_iff_isCartesianEdge_toSSet p e

private theorem map_simplexHom_δ_eq_cell (σ : diagram E (atomSimplex 2)) (i : Fin 3)
    {a b : E.Vertex} (f : SSet.Edge (E.vertexEquivSSet a) (E.vertexEquivSSet b))
    (hf : (DiagSet.toSSet.obj E).δ i σ = f.edge) :
    E.map (atomSimplexOneIsoGlobe.inv ≫ simplexHom (SimplexCategory.δ i).toOrderHom).op σ =
      (E.edgeEquivSSet.symm f).cell := by
  rw [op_comp, Functor.map_comp_apply]
  exact congrArg (E.map atomSimplexOneIsoGlobe.inv.op) hf

theorem DiagSet.IsCartesianEdge.exists_comp {p : E ⟶ S} {z : E.Vertex}
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    {e₀₁ : E.Edge x y} {e₁₂ : E.Edge y z}
    (he₀₁ : DiagSet.IsCartesianEdge p e₀₁) (he₁₂ : DiagSet.IsCartesianEdge p e₁₂) :
    ∃ (σ : diagram E (atomSimplex 2)) (e₀₂ : E.Edge x z),
      E.map (atomSimplexOneIsoGlobe.inv ≫
        simplexHom (SimplexCategory.δ (2 : Fin 3)).toOrderHom).op σ = e₀₁.cell ∧
      E.map (atomSimplexOneIsoGlobe.inv ≫
        simplexHom (SimplexCategory.δ (0 : Fin 3)).toOrderHom).op σ = e₁₂.cell ∧
      E.map (atomSimplexOneIsoGlobe.inv ≫
        simplexHom (SimplexCategory.δ (1 : Fin 3)).toOrderHom).op σ = e₀₂.cell ∧
      DiagSet.IsCartesianEdge p e₀₂ := by
  have : (DiagSet.toSSet.obj E).Quasicategory := quasicategory_toSSet_obj
    ((DiagSet.toInfty 1).obj E) (isFibrant_of_fibration ((DiagSet.toInfty 1).map p))
  let f := E.edgeEquivSSet e₀₁
  let g := E.edgeEquivSSet e₁₂
  let s : ∀ j : Fin 3, j ≠ 1 → (DiagSet.toSSet.obj E) _⦋1⦌ := fun j _ ↦ ![g.edge, g.edge, f.edge] j
  have hc : SSet.horn.IsCompatible (fun j hj ↦ SSet.yonedaEquiv.symm (s j hj)) := by
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k
    all_goals try exact absurd hjk (by decide)
    all_goals try exact (hk rfl).elim
    all_goals try exact (hj rfl).elim
    simp only [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg _ (g.src_eq.trans f.tgt_eq.symm)
  obtain ⟨τ, hτ⟩ := SSet.Quasicategory.hornFilling (n := 2) (i := 1) (by decide) (by decide)
    hc.desc
  let σ : diagram E (atomSimplex 2) := SSet.yonedaEquiv τ
  have hσ (j : Fin 3) (hj : j ≠ 1) : (DiagSet.toSSet.obj E).δ j σ = s j hj := by
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, ← SSet.horn.ι_ι 1 j hj, Category.assoc, ← hτ,
      hc.ι_desc, Equiv.apply_symm_apply]
  have h₀ : (DiagSet.toSSet.obj E).δ 0 σ = g.edge := hσ 0 (by decide)
  have h₂ : (DiagSet.toSSet.obj E).δ 2 σ = f.edge := hσ 2 (by decide)
  let h : SSet.Edge (E.vertexEquivSSet x) (E.vertexEquivSSet z) :=
    SSet.Edge.mk ((DiagSet.toSSet.obj E).δ 1 σ)
      ((SSet.δ_comp_δ_self_apply (S := DiagSet.toSSet.obj E) (n := 0) (i := 1) σ).trans
        ((congrArg _ h₂).trans f.src_eq))
      ((SSet.δ_comp_δ_self_apply (S := DiagSet.toSSet.obj E) (n := 0) (i := 0) σ).symm.trans
        ((congrArg _ h₀).trans g.tgt_eq))
  have h₀₁ := map_simplexHom_δ_eq_cell σ 2 f h₂
  have h₁₂ := map_simplexHom_δ_eq_cell σ 0 g h₀
  rw [Equiv.symm_apply_apply] at h₀₁ h₁₂
  have h₀₂ := map_simplexHom_δ_eq_cell σ 1 h rfl
  exact ⟨σ, _, h₀₁, h₁₂, h₀₂, DiagSet.IsCartesianEdge.of_simplex_two σ h₀₁ h₁₂ h₀₂ he₀₁ he₁₂⟩

theorem DiagSet.isCartesianEdge_id {p : E ⟶ S} (x : E.Vertex)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)] :
    DiagSet.IsCartesianEdge p (DiagSet.Edge.id x) :=
  have : (DiagSet.toSSet.obj E).Quasicategory :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj E)
      (isFibrant_of_fibration ((DiagSet.toInfty 1).map p))
  have : (DiagSet.toSSet.obj S).Quasicategory :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj S) inferInstance
  have : SSet.InnerFibration (DiagSet.toSSet.map p) :=
    innerFibration_toSSet_map ((DiagSet.toInfty 1).map p) inferInstance
  (DiagSet.isCartesianEdge_iff_isCartesianEdge_toSSet p (DiagSet.Edge.id x)).2 (by
    rw [DiagSet.edgeEquivSSet_id]
    exact SSet.isCartesianEdge_id (DiagSet.toSSet.map p) _)

theorem DiagSet.isCartesianEdge_of_isEquivalence {p : E ⟶ S} (e : E.Edge x y)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (he : IsEquivalence E e.cell) :
    DiagSet.IsCartesianEdge p e := by
  have : (DiagSet.toSSet.obj S).Quasicategory :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj S) inferInstance
  have : (DiagSet.toSSet.obj E).Quasicategory :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj E)
      (isFibrant_of_fibration ((DiagSet.toInfty 1).map p))
  have : SSet.InnerFibration (DiagSet.toSSet.map p) :=
    innerFibration_toSSet_map ((DiagSet.toInfty 1).map p) inferInstance
  obtain ⟨I⟩ := nonempty_invStruct_of_isEquivalence (isInftyCategory_of_isFibrant 1 _
    (isFibrant_of_fibration ((DiagSet.toInfty 1).map p))) (E.edgeEquivSSet e)
    ((isEquivalence_map_iso_iff atomSimplexOneIsoGlobe e.cell).2 he)
  exact DiagSet.isCartesianEdge_of_isCartesianEdge_toSSet
    (SSet.isCartesianEdge_of_invStruct _ ⟨I.ofEq (SSet.yonedaEquiv.apply_symm_apply _).symm⟩)

end Atoms.Diagrammatic
