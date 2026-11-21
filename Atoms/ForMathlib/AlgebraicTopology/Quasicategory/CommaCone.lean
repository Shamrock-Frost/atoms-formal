import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CommaObject
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.MappingSpacePiZero
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.ZeroObject

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory Simplicial
  HomotopicalAlgebra MorphismProperty Opposite

universe u

namespace SSet

variable {K X : SSet.{u}}

noncomputable def constDiagram (K X : SSet.{u}) : X ⟶ (ihom K).obj X :=
  curry (snd K X)

noncomputable def diagramPoint (d : K ⟶ X) : 𝟙_ SSet.{u} ⟶ (ihom K).obj X :=
  curry (fst K (𝟙_ SSet.{u}) ≫ d)

noncomputable def commaConeBase (d : K ⟶ X) : X ⟶ (ihom (∂Δ[1] : SSet.{u})).obj ((ihom K).obj X) :=
  commaObjectBase true (constDiagram K X) (diagramPoint d)

@[reassoc]
theorem commaConeBase_pre_boundary_ι_one (d : K ⟶ X) :
    commaConeBase d ≫ (pre (boundary.ι 1)).app ((ihom K).obj X) =
      constDiagram K X ≫ constDiagram Δ[0] ((ihom K).obj X) := by
  rw [commaConeBase, commaObjectBase, curry_pre_app,
    boundary_ι_one_whiskerRight_boundaryOneTensorDesc, cond_true, constDiagram.eq_1 Δ[0],
    ← curry_natural_left, whiskerLeft_snd]

@[reassoc]
theorem commaConeBase_pre_boundary_ι_zero (d : K ⟶ X) :
    commaConeBase d ≫ (pre (boundary.ι 0)).app ((ihom K).obj X) =
      toUnit X ≫ diagramPoint d ≫ constDiagram Δ[0] ((ihom K).obj X) := by
  rw [commaConeBase, commaObjectBase, curry_pre_app,
    boundary_ι_zero_whiskerRight_boundaryOneTensorDesc, cond_true, constDiagram.eq_1 Δ[0],
    ← curry_natural_left, ← curry_natural_left]
  simp only [whiskerLeft_snd, whiskerLeft_snd_assoc]

noncomputable def commaCone (d : K ⟶ X) : SSet.{u} :=
  commaObject true (constDiagram K X) (diagramPoint d)

noncomputable def commaConeπ (d : K ⟶ X) : commaCone d ⟶ X :=
  commaObjectπ true (constDiagram K X) (diagramPoint d)

noncomputable def commaConeArrow (d : K ⟶ X) :
    commaCone d ⟶ (ihom Δ[1]).obj ((ihom K).obj X) :=
  commaObjectArrow true (constDiagram K X) (diagramPoint d)

theorem isPullback_commaCone (d : K ⟶ X) :
    IsPullback (commaConeArrow d) (commaConeπ d) ((pre (∂Δ[1]).ι).app ((ihom K).obj X))
      (commaConeBase d) :=
  isPullback_commaObject true (constDiagram K X) (diagramPoint d)

instance quasicategory_commaCone (d : K ⟶ X) [X.Quasicategory] : (commaCone d).Quasicategory :=
  quasicategory_commaObject true (constDiagram K X) (diagramPoint d)

theorem isofibration_commaConeπ (d : K ⟶ X) [X.Quasicategory] : Isofibration (commaConeπ d) :=
  isofibration_commaObjectπ true (constDiagram K X) (diagramPoint d)

section UniversalProperty

private lemma curry_comp_pre_boundaryOne_eq_iff (d : K ⟶ X) {T : SSet.{u}} (t : T ⟶ X)
    (h : Δ[1] ⊗ T ⟶ (ihom K).obj X) :
    curry h ≫ (pre (∂Δ[1]).ι).app ((ihom K).obj X) = t ≫ commaConeBase d ↔
      stdSimplex.δ 1 ▷ T ≫ h = snd _ _ ≫ t ≫ constDiagram K X ∧
        stdSimplex.δ 0 ▷ T ≫ h = snd _ _ ≫ toUnit T ≫ diagramPoint d := by
  rw [curry_pre_app, commaConeBase, commaObjectBase, cond_true, cond_true, ← curry_natural_left,
    curry_injective.eq_iff, ← boundary.ι_ι, ← boundary.ι_ι, comp_whiskerRight, comp_whiskerRight,
    Category.assoc, Category.assoc]
  refine ⟨fun e ↦ ⟨?_, ?_⟩, fun ⟨e₁, e₀⟩ ↦ boundaryOneTensor_hom_ext ?_ ?_⟩
  · rw [e, ← whisker_exchange_assoc, boundary_ι_one_whiskerRight_boundaryOneTensorDesc,
      whiskerLeft_snd_assoc]
  · rw [e, ← whisker_exchange_assoc, boundary_ι_zero_whiskerRight_boundaryOneTensorDesc,
      whiskerLeft_snd_assoc]
    simp only [comp_toUnit_assoc]
  · rw [e₁, ← whisker_exchange_assoc, boundary_ι_one_whiskerRight_boundaryOneTensorDesc,
      whiskerLeft_snd_assoc]
  · rw [e₀, ← whisker_exchange_assoc, boundary_ι_zero_whiskerRight_boundaryOneTensorDesc,
      whiskerLeft_snd_assoc]
    simp only [comp_toUnit_assoc]

noncomputable def commaConeHomEquiv (d : K ⟶ X) (T : SSet.{u}) :
    (T ⟶ commaCone d) ≃ {p : (T ⟶ X) × (Δ[1] ⊗ T ⟶ (ihom K).obj X) //
      stdSimplex.δ 1 ▷ T ≫ p.2 = snd _ _ ≫ p.1 ≫ constDiagram K X ∧
        stdSimplex.δ 0 ▷ T ≫ p.2 = snd _ _ ≫ toUnit T ≫ diagramPoint d} where
  toFun f := ⟨(f ≫ commaConeπ d, uncurry (f ≫ commaConeArrow d)),
    (curry_comp_pre_boundaryOne_eq_iff d _ _).1 (by
      rw [curry_uncurry, Category.assoc, (isPullback_commaCone d).w, Category.assoc])⟩
  invFun p := (isPullback_commaCone d).lift (curry p.1.2) p.1.1
    ((curry_comp_pre_boundaryOne_eq_iff d _ _).2 p.2)
  left_inv f := (isPullback_commaCone d).hom_ext (by simp) (by simp)
  right_inv p := Subtype.ext (Prod.ext (by simp) (by simp))

@[reassoc (attr := simp)]
theorem commaConeHomEquiv_symm_apply_arrow (d : K ⟶ X) {T : SSet.{u}}
    (p : {p : (T ⟶ X) × (Δ[1] ⊗ T ⟶ (ihom K).obj X) //
      stdSimplex.δ 1 ▷ T ≫ p.2 = snd _ _ ≫ p.1 ≫ constDiagram K X ∧
        stdSimplex.δ 0 ▷ T ≫ p.2 = snd _ _ ≫ toUnit T ≫ diagramPoint d}) :
    (commaConeHomEquiv d T).symm p ≫ commaConeArrow d = curry p.1.2 :=
  (isPullback_commaCone d).lift_fst _ _ _

@[reassoc (attr := simp)]
theorem commaConeHomEquiv_symm_apply_π (d : K ⟶ X) {T : SSet.{u}}
    (p : {p : (T ⟶ X) × (Δ[1] ⊗ T ⟶ (ihom K).obj X) //
      stdSimplex.δ 1 ▷ T ≫ p.2 = snd _ _ ≫ p.1 ≫ constDiagram K X ∧
        stdSimplex.δ 0 ▷ T ≫ p.2 = snd _ _ ≫ toUnit T ≫ diagramPoint d}) :
    (commaConeHomEquiv d T).symm p ≫ commaConeπ d = p.1.1 :=
  (isPullback_commaCone d).lift_snd _ _ _

theorem isPullback_commaCone_fibre (d : K ⟶ X) {T : SSet.{u}} (t : T ⟶ X) :
    IsPullback (pullback.fst (commaConeπ d) t ≫ commaConeArrow d) (pullback.snd (commaConeπ d) t)
      ((pre (∂Δ[1]).ι).app ((ihom K).obj X)) (t ≫ commaConeBase d) :=
  (IsPullback.of_hasPullback (commaConeπ d) t).paste_horiz (isPullback_commaCone d)

end UniversalProperty

section Fibre

private lemma commaConeBase_comp_boundaryEval (d : K ⟶ X) (a : X _⦋0⦌) :
    yonedaEquiv.symm a ≫ commaConeBase d ≫ boundaryEval ((ihom K).obj X) =
      lift (yonedaEquiv.symm ((constDiagram K X).app _ a))
        (yonedaEquiv.symm (yonedaEquiv ((ihomPointEquiv K X).symm d))) := by
  ext1
  · rw [Category.assoc, Category.assoc, boundaryEval, lift_fst, commaConeBase,
      commaObjectBase_comp_evalVertex_one, cond_true]
    exact yonedaEquiv_symm_comp a _
  · rw [Category.assoc, Category.assoc, boundaryEval, lift_snd, commaConeBase,
      commaObjectBase_comp_evalVertex_zero, cond_true, Equiv.symm_apply_apply, ← Category.assoc,
      diagramPoint, ← curry_natural_left, whiskerLeft_fst_assoc]
    rfl

noncomputable def commaConeFibreIsoMappingSpace (d : K ⟶ X) (a : X _⦋0⦌) :
    pullback (commaConeπ d) (yonedaEquiv.symm a) ≅
      mappingSpace ((ihom K).obj X) ((constDiagram K X).app _ a)
        (yonedaEquiv ((ihomPointEquiv K X).symm d)) :=
  IsPullback.isoPullback (by
    have h := (isPullback_commaCone_fibre d (yonedaEquiv.symm a)).paste_vert
      (IsPullback.of_vert_isIso_mono (snd := 𝟙 _) (f := boundaryEval ((ihom K).obj X))
        ⟨(Category.id_comp _).symm⟩)
    rw [pre_comp_boundaryEval, Category.assoc, commaConeBase_comp_boundaryEval,
      Category.comp_id] at h
    exact h)

end Fibre

section Limits

def IsLimitCone (d : K ⟶ X) (v : (commaCone d) _⦋0⦌) : Prop :=
  IsFinal v

noncomputable def commaCocone (d : K ⟶ X) : SSet.{u} :=
  commaObject false (constDiagram K X) (diagramPoint d)

noncomputable def commaCoconeπ (d : K ⟶ X) : commaCocone d ⟶ X :=
  commaObjectπ false (constDiagram K X) (diagramPoint d)

def IsColimitCocone (d : K ⟶ X) (v : (commaCocone d) _⦋0⦌) : Prop :=
  IsInitialObject v

private noncomputable def isTerminalIhomInitial (X : SSet.{u}) :
    IsTerminal ((ihom (⊥_ SSet.{u})).obj X) :=
  isTerminalTensorUnit.ofIso (powZero initialIsInitial).symm

instance isIso_commaConeπ_empty : IsIso (commaConeπ (initial.to X)) := by
  have h := isTerminalIhomInitial X
  have : IsIso ((pre (∂Δ[1]).ι).app ((ihom (⊥_ SSet.{u})).obj X)) :=
    isIso_of_isTerminal (h.isTerminalObj (ihom Δ[1]) _)
      (h.isTerminalObj (ihom (∂Δ[1] : SSet.{u})) _) _
  exact (isPullback_commaCone (initial.to X)).isIso_snd_of_isIso

theorem isLimitCone_empty_iff (v : (commaCone (initial.to X)) _⦋0⦌) :
    IsLimitCone (initial.to X) v ↔ IsFinal ((commaConeπ (initial.to X)).app _ v) :=
  (isFinal_iso_hom_app_iff (asIso (commaConeπ (initial.to X))) v).symm

end Limits

section Legs

variable (d : K ⟶ X)

noncomputable def commaConeLegMap (k : K _⦋0⦌) : commaCone d ⟶ (ihom Δ[1]).obj X :=
  commaConeArrow d ≫ (ihom Δ[1]).map (evalVertex k X)

private lemma pre_boundary_ι_comp_evalVertex (B : SSet.{u}) (j : Fin 2) :
    (pre (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι).app B ≫
        evalVertex (yonedaEquiv (boundary.ι j : Δ[0] ⟶ (∂Δ[1] : SSet.{u}))) B =
      evalVertex (yonedaEquiv (stdSimplex.δ j)) B := by
  rw [pre_app_comp_evalVertex, ← yonedaEquiv_comp, boundary.ι_ι]

@[reassoc]
theorem commaConeLegMap_comp_evalVertex_zero (k : K _⦋0⦌) :
    commaConeLegMap d k ≫ evalVertex (stdSimplex.obj₀Equiv.symm 0) X = commaConeπ d := by
  have h := pre_boundary_ι_comp_evalVertex ((ihom K).obj X) 1
  rw [stdSimplex_δ_one_eq, Equiv.apply_symm_apply] at h
  rw [commaConeLegMap, Category.assoc, ihom_map_comp_evalVertex, ← h, Category.assoc,
    (isPullback_commaCone d).w_assoc, commaConeBase, commaObjectBase_comp_evalVertex_one_assoc,
    cond_true, constDiagram, comp_evalVertex, uncurry_curry, lift_snd, Category.comp_id]

@[reassoc]
theorem commaConeLegMap_comp_evalVertex_one (k : K _⦋0⦌) :
    commaConeLegMap d k ≫ evalVertex (stdSimplex.obj₀Equiv.symm 1) X =
      stdSimplex.isTerminalObj₀.from _ ≫ yonedaEquiv.symm (d.app _ k) := by
  have h := pre_boundary_ι_comp_evalVertex ((ihom K).obj X) 0
  rw [stdSimplex_δ_zero_eq, Equiv.apply_symm_apply] at h
  have hd : diagramPoint d ≫ evalVertex k X =
      stdSimplex.isTerminalObj₀.from _ ≫ yonedaEquiv.symm (d.app _ k) := by
    rw [diagramPoint, comp_evalVertex, uncurry_curry, lift_fst_assoc, Category.assoc,
      yonedaEquiv_symm_comp]
  rw [commaConeLegMap, Category.assoc, ihom_map_comp_evalVertex, ← h, Category.assoc,
    (isPullback_commaCone d).w_assoc, commaConeBase, commaObjectBase_comp_evalVertex_zero_assoc,
    cond_true, Category.assoc, hd, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ _) (stdSimplex.isTerminalObj₀.hom_ext _ _)

variable {d} {k : K _⦋0⦌} {z : X _⦋0⦌}

noncomputable def commaConeLeg (hz : d.app _ k = z) (v : (commaCone d) _⦋0⦌) :
    Edge ((commaConeπ d).app _ v) z :=
  Edge.mk (ihomStdSimplexOneEdge ((commaConeLegMap d k).app _ v))
    ((δ_one_ihomStdSimplexOneEdge _).trans
      (congrArg (fun f ↦ f.app _ v) (commaConeLegMap_comp_evalVertex_zero d k)))
    ((δ_zero_ihomStdSimplexOneEdge _).trans
      ((congrArg (fun f ↦ f.app _ v) (commaConeLegMap_comp_evalVertex_one d k)).trans (by
        rw [← hz, ← Equiv.apply_symm_apply yonedaEquiv v, ← yonedaEquiv_comp,
          ← Category.assoc, stdSimplex.isTerminalObj₀.hom_ext (_ ≫ _) (𝟙 _), Category.id_comp,
          Equiv.apply_symm_apply])))

theorem homMk_commaConeLeg (hz : d.app _ k = z) {v v' : (commaCone d) _⦋0⦌} (e : Edge v v')
    {a a' : X _⦋0⦌} {f : Edge a z} {f' : Edge a' z} {p : Edge a a'}
    (hf : f.edge = (commaConeLeg hz v).edge) (hf' : f'.edge = (commaConeLeg hz v').edge)
    (hp : p.edge = (commaConeπ d).app _ e.edge) :
    Truncated.HomotopyCategory.homMk (V := (truncation 2).obj X) f.toTruncated =
      Truncated.HomotopyCategory.homMk p.toTruncated ≫
        Truncated.HomotopyCategory.homMk f'.toTruncated := by
  have hq : (Edge.id z).edge = (evalVertex (stdSimplex.obj₀Equiv.symm 1) X).app _
      (e.map (commaConeLegMap d k)).edge :=
    ((congrArg (fun f ↦ f.app _ e.edge) (commaConeLegMap_comp_evalVertex_one d k)).trans (by
      rw [← hz, Edge.id_edge, ← Equiv.apply_symm_apply yonedaEquiv e.edge, ← yonedaEquiv_comp,
        ← Category.assoc, stdSimplex.isTerminalObj₀.hom_ext (_ ≫ _) (stdSimplex.σ 0),
        stdSimplex.σ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply])).symm
  have h := homMk_comp_homMk_of_edge_ihomStdSimplexOne (e.map (commaConeLegMap d k)) hf hf'
    (hp.trans (congrArg (fun f ↦ f.app _ e.edge)
      (commaConeLegMap_comp_evalVertex_zero d k)).symm) hq
  exact (Category.comp_id _).symm.trans
    ((congrArg (_ ≫ ·) (Truncated.HomotopyCategory.homMk_id _).symm).trans h)

end Legs

section Functoriality

variable {Y : SSet.{u}} (F : X ⟶ Y)

@[reassoc]
theorem constDiagram_comp_ihom_map (K : SSet.{u}) :
    constDiagram K X ≫ (ihom K).map F = F ≫ constDiagram K Y := by
  rw [constDiagram, constDiagram, ← curry_natural_right, ← curry_natural_left, whiskerLeft_snd]

@[reassoc]
theorem diagramPoint_comp_ihom_map (d : K ⟶ X) :
    diagramPoint d ≫ (ihom K).map F = diagramPoint (d ≫ F) := by
  rw [diagramPoint, diagramPoint, ← curry_natural_right, Category.assoc]

theorem commaObjectMap_arrow_evalVertex (α : Bool) {b : 𝟙_ SSet.{u} ⟶ (ihom K).obj X}
    {b' : 𝟙_ SSet.{u} ⟶ (ihom K).obj Y} (hb : b ≫ (ihom K).map F = b') (k : K _⦋0⦌) :
    commaObjectMap α F ((ihom K).map F) (constDiagram_comp_ihom_map F K) hb ≫
        commaObjectArrow α _ _ ≫ (ihom Δ[1]).map (evalVertex k Y) =
      commaObjectArrow α _ _ ≫ (ihom Δ[1]).map (evalVertex k X ≫ F) := by
  rw [commaObjectMap_arrow_assoc, ← Functor.map_comp, ihom_map_comp_evalVertex]

end Functoriality

end SSet
