import Atoms.Diagrammatic.Joyal.FaceNerve
import Atoms.Diagrammatic.SimplicialAdjunction
import Atoms.Homotopical.Simplicial.CartesianInduction
import Atoms.Homotopical.Simplicial.Terminalization

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial
open Atoms.Homotopical Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open MarkedSSet.modelCategoryCartesian

section Simplex

variable (n : ℕ)

private theorem atomSimplexVertices_nonempty {n : ℕ} (x : (atomSimplex n).ogp) :
    (atomSimplexVertices n x).Nonempty :=
  Finset.card_pos.1 (by rw [card_atomSimplexVertices]; omega)

def atomSimplexMaxVertex : (atomSimplex n).ogp →o ULift.{u} (Fin (n + 1)) where
  toFun x := ULift.up ((atomSimplexVertices n x).max' (atomSimplexVertices_nonempty x))
  monotone' _ _ h := Finset.max'_subset (atomSimplexVertices_nonempty _)
    (atomSimplexVertices_subset_iff.2 h)

variable {n} in
theorem atomSimplexMaxVertex_down (x : (atomSimplex n).ogp) :
    (atomSimplexMaxVertex.{u} n x).down =
      (atomSimplexVertices n x).max' (atomSimplexVertices_nonempty x) :=
  rfl

variable {n} in
private theorem atomSimplexVertices_eq_of_mem_boundary {x v : (atomSimplex n).ogp}
    (hv : v ∈ (atomSimplex n).ogp.boundary (.Iic x) 0 true) :
    atomSimplexVertices n v = {(atomSimplexMaxVertex.{u} n x).down} := by
  have hd : grade ℕ v = 0 := Nat.le_zero.1 (grade_le_of_mem_boundary hv)
  obtain ⟨j, hj⟩ := Finset.card_eq_one.1 (by rw [card_atomSimplexVertices, hd] :
    (atomSimplexVertices n v).card = 1)
  have hvx : v ≤ x := LowerSet.mem_Iic_iff.1 (boundary_le _ 0 true hv)
  have hjx : j ∈ atomSimplexVertices n x :=
    atomSimplexVertices_subset_iff.2 hvx (hj ▸ Finset.mem_singleton_self j)
  rw [hj]
  rw [atomSimplexMaxVertex_down]
  exact congrArg _ (le_antisymm (Finset.le_max' _ _ hjx) (Finset.max'_le _ _ _
    fun _ hj' ↦ le_of_mem_boundary_zero_true_atomSimplex hv hj hj'))

variable {n} in
theorem boundary_closure_atomSimplex_eq_iff {x y : (atomSimplex n).ogp} :
    (atomSimplex n).ogp.boundary (.Iic x) 0 true = (atomSimplex n).ogp.boundary (.Iic y) 0 true ↔
      atomSimplexMaxVertex.{u} n x = atomSimplexMaxVertex n y := by
  obtain ⟨v, hv⟩ := (((atomSimplex n).isRDC x).boundary 0 true).nonempty
  obtain ⟨w, hw⟩ := (((atomSimplex n).isRDC y).boundary 0 true).nonempty
  refine ⟨fun h ↦ ULift.ext _ _ (Finset.singleton_inj.1
    ((atomSimplexVertices_eq_of_mem_boundary.{u} hv).symm.trans
      (atomSimplexVertices_eq_of_mem_boundary (h ▸ hv)))), fun h ↦ ?_⟩
  have key {x y : (atomSimplex n).ogp} {u w : (atomSimplex n).ogp}
      (h : atomSimplexMaxVertex n x = atomSimplexMaxVertex n y)
      (hu : u ∈ (atomSimplex n).ogp.boundary (.Iic x) 0 true)
      (hw : w ∈ (atomSimplex n).ogp.boundary (.Iic y) 0 true) :
      u ∈ (atomSimplex n).ogp.boundary (.Iic y) 0 true :=
    (atomSimplexVertices_injective n ((atomSimplexVertices_eq_of_mem_boundary.{u} hu).trans
      ((congrArg (fun z ↦ ({z.down} : Finset _)) h).trans
        (atomSimplexVertices_eq_of_mem_boundary.{u} hw).symm))) ▸ hw
  exact SetLike.ext fun u ↦ ⟨fun hu ↦ key h hu hw, fun hu ↦ key h.symm hu hv⟩

noncomputable def atomSimplexIicFace : ULift.{u} (Fin (n + 1)) →o (atomSimplex n).ogp where
  toFun j := (exists_atomSimplexVertices_eq n (S := Finset.Iic j.down) Finset.nonempty_Iic).choose
  monotone' i j h := atomSimplexVertices_subset_iff.1 (by
    rw [(exists_atomSimplexVertices_eq n (S := Finset.Iic i.down) Finset.nonempty_Iic).choose_spec,
      (exists_atomSimplexVertices_eq n (S := Finset.Iic j.down) Finset.nonempty_Iic).choose_spec]
    exact Finset.Iic_subset_Iic.2 h)

theorem atomSimplexVertices_atomSimplexIicFace (j : ULift.{u} (Fin (n + 1))) :
    atomSimplexVertices n (atomSimplexIicFace n j) = Finset.Iic j.down :=
  (exists_atomSimplexVertices_eq n (S := Finset.Iic j.down) Finset.nonempty_Iic).choose_spec

theorem atomSimplexMaxVertex_atomSimplexIicFace (j : ULift.{u} (Fin (n + 1))) :
    atomSimplexMaxVertex n (atomSimplexIicFace n j) = j := by
  have h := atomSimplexVertices_atomSimplexIicFace n j
  refine ULift.ext _ _ ((atomSimplexMaxVertex_down _).trans
    (le_antisymm (Finset.max'_le _ _ _ fun a ha ↦ ?_) (Finset.le_max' _ _ ?_)))
  · rw [h] at ha
    exact Finset.mem_Iic.1 ha
  · rw [h]
    exact Finset.mem_Iic.2 le_rfl

variable {n} in
theorem le_atomSimplexIicFace_atomSimplexMaxVertex (x : (atomSimplex n).ogp) :
    x ≤ atomSimplexIicFace.{u} n (atomSimplexMaxVertex n x) := by
  refine atomSimplexVertices_subset_iff.1 fun a ha ↦ ?_
  rw [atomSimplexVertices_atomSimplexIicFace]
  exact Finset.mem_Iic.2 ((Finset.le_max' _ a ha).trans_eq (atomSimplexMaxVertex_down.{u} x).symm)

noncomputable def atomSimplexContraction :
    ULift.{u} (Fin 2) × (atomSimplex n).ogp →o (atomSimplex n).ogp where
  toFun p := if p.1.down = 0 then p.2 else atomSimplexIicFace.{u} n (atomSimplexMaxVertex n p.2)
  monotone' := by
    rintro ⟨⟨a⟩, x⟩ ⟨⟨b⟩, y⟩ ⟨hab, hxy⟩
    have hab' : a ≤ b := hab
    change (if a = 0 then x else _) ≤ (if b = 0 then y else _)
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · rw [if_pos ha, if_pos hb]
      exact hxy
    · rw [if_pos ha, if_neg hb]
      exact hxy.trans (le_atomSimplexIicFace_atomSimplexMaxVertex.{u} y)
    · exact absurd (le_antisymm (hb ▸ hab') (Fin.zero_le a)) ha
    · rw [if_neg ha, if_neg hb]
      exact (atomSimplexIicFace n).monotone ((atomSimplexMaxVertex n).monotone hxy)

variable {n} in
theorem atomSimplexContraction_zero (x : (atomSimplex n).ogp) :
    atomSimplexContraction.{u} n (ULift.up 0, x) = x := by
  change (if (0 : Fin 2) = 0 then x else atomSimplexIicFace.{u} n (atomSimplexMaxVertex n x)) = x
  exact if_pos rfl

variable {n} in
theorem atomSimplexContraction_one (x : (atomSimplex n).ogp) :
    atomSimplexContraction.{u} n (ULift.up 1, x) =
      atomSimplexIicFace.{u} n (atomSimplexMaxVertex n x) := by
  change (if (1 : Fin 2) = 0 then x else atomSimplexIicFace.{u} n (atomSimplexMaxVertex n x)) = _
  exact if_neg (by decide)

theorem atomSimplexMaxVertex_atomSimplexContraction
    (p : ULift.{u} (Fin 2) × (atomSimplex n).ogp) :
    atomSimplexMaxVertex.{u} n (atomSimplexContraction n p) = atomSimplexMaxVertex n p.2 := by
  change atomSimplexMaxVertex n (if p.1.down = 0 then _ else _) = _
  split_ifs
  · rfl
  · exact atomSimplexMaxVertex_atomSimplexIicFace n _

variable {n} in
theorem atomSimplexMaxVertex_simplexHom {m : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (x : (atomSimplex m).ogp) :
    atomSimplexMaxVertex.{u} n (simplexHom f x) =
      ULift.up (f (atomSimplexMaxVertex.{u} m x).down) := by
  refine ULift.ext _ _ ?_
  simp only [atomSimplexMaxVertex_down, atomSimplexVertices_simplexHom]
  exact Finset.max'_image f.monotone _ _

end Simplex

section Contraction

open MonoidalCategory

variable (n : ℕ)

noncomputable def faceNerveSimplexMaxVertex :
    rdcFaceNerve.{u}.obj (atomToRDCpx.obj (atomSimplex n)) ⟶
      (MarkedPresheaf.flat edgeMarking).obj Δ[n] :=
  edgeHomMk (nerveMap (atomSimplexMaxVertex n).uliftLeftMap.monotone.functor ≫
    (SSet.stdSimplex.isoNerve n).inv) fun e he ↦ by
    obtain ⟨-, h | ⟨h, -⟩⟩ := (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 he
    · have h' : (atomSimplexMaxVertex.{u} n (e.obj 0).down).down =
          (atomSimplexMaxVertex n (e.obj 1).down).down :=
        congrArg ULift.down ((boundary_closure_atomSimplex_eq_iff).1 h)
      exact (congrArg (· ∈ _) (stdSimplex_eq_σ_δ_of_apply_eq
        (((nerveMap (atomSimplexMaxVertex n).uliftLeftMap.monotone.functor ≫
          (SSet.stdSimplex.isoNerve n).inv).app _ e) : (Δ[n] : SSet.{u}) _⦋1⦌) h')).mpr
        (MarkedSSet.map_σ_mem_marked _ _)
    · exact absurd h (Set.notMem_empty _)

noncomputable def faceNerveSimplexIicFace :
    (MarkedPresheaf.flat edgeMarking).obj Δ[n] ⟶
      rdcFaceNerve.{u}.obj (atomToRDCpx.obj (atomSimplex n)) :=
  edgeHomMk ((SSet.stdSimplex.isoNerve n).hom ≫
    nerveMap (atomSimplexIicFace n).uliftRightMap.monotone.functor) fun e he ↦ by
    obtain ⟨v, rfl⟩ := exists_eq_σ_of_mem_marked_flat e he
    exact (congrArg (· ∈ _) (SSet.σ_naturality_apply _ 0 v)).mpr (MarkedSSet.map_σ_mem_marked _ _)

noncomputable def faceNerveSimplexContraction :
    sharpEdgeProd.obj (rdcFaceNerve.{u}.obj (atomToRDCpx.obj (atomSimplex n))) ⟶
      rdcFaceNerve.obj (atomToRDCpx.obj (atomSimplex n)) :=
  edgeHomMk (nerveHomotopy (atomSimplexContraction n)) fun e he ↦ by
    obtain ⟨-, h | ⟨h, -⟩⟩ := (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1
      ((mem_marked_sharpEdgeProdObj _ e).1 he)
    · refine (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 ⟨rfl, Or.inl ?_⟩
      refine (boundary_closure_atomSimplex_eq_iff.{u}).2 ?_
      refine (atomSimplexMaxVertex_atomSimplexContraction n _).trans (Eq.trans ?_
        (atomSimplexMaxVertex_atomSimplexContraction n _).symm)
      exact (boundary_closure_atomSimplex_eq_iff).1 h
    · exact absurd h (Set.notMem_empty _)

@[reassoc]
theorem faceNerveSimplexIicFace_comp_faceNerveSimplexMaxVertex :
    faceNerveSimplexIicFace.{u} n ≫ faceNerveSimplexMaxVertex n = 𝟙 _ :=
  MarkedPresheaf.hom_ext (by
    ext ⟨⟨k⟩⟩ z
    exact SSet.stdSimplex.ext _ _ fun i ↦
      congrArg ULift.down (atomSimplexMaxVertex_atomSimplexIicFace n _))

@[reassoc]
theorem sharpEdgeEndpoint_zero_app_comp_faceNerveSimplexContraction :
    (sharpEdgeEndpoint 0).app _ ≫ faceNerveSimplexContraction.{u} n = 𝟙 _ :=
  MarkedPresheaf.hom_ext (by
    ext ⟨⟨k⟩⟩ z
    exact nerve.ext_of_isThin (C := ULift.{u} (atomSimplex n).ogp)
      (funext fun _ ↦ ULift.ext _ _ (atomSimplexContraction_zero _)))

@[reassoc]
theorem sharpEdgeEndpoint_one_app_comp_faceNerveSimplexContraction :
    (sharpEdgeEndpoint 1).app _ ≫ faceNerveSimplexContraction.{u} n =
      faceNerveSimplexMaxVertex n ≫ faceNerveSimplexIicFace n :=
  MarkedPresheaf.hom_ext (by
    ext ⟨⟨k⟩⟩ z
    exact nerve.ext_of_isThin (C := ULift.{u} (atomSimplex n).ogp)
      (funext fun _ ↦ ULift.ext _ _ (atomSimplexContraction_one _)))

theorem weakEquivalence_faceNerveSimplexMaxVertex :
    WeakEquivalence (faceNerveSimplexMaxVertex.{u} n) :=
  weakEquivalence_of_sharpEdgeHomotopy _ _
    (faceNerveSimplexIicFace_comp_faceNerveSimplexMaxVertex n) (faceNerveSimplexContraction n)
    (sharpEdgeEndpoint_zero_app_comp_faceNerveSimplexContraction n)
    (sharpEdgeEndpoint_one_app_comp_faceNerveSimplexContraction n)

noncomputable def faceNerveSimplexMaxVertexNatTrans :
    simplexFunctor ⋙ atomToRDCpx ⋙ rdcFaceNerve.{u} ⟶
      SSet.stdSimplex ⋙ MarkedPresheaf.flat edgeMarking where
  app k := faceNerveSimplexMaxVertex k.len
  naturality k m θ := by
    induction k using SimplexCategory.rec with | _ k
    induction m using SimplexCategory.rec with | _ m
    refine MarkedPresheaf.hom_ext ?_
    ext ⟨⟨d⟩⟩ z
    exact SSet.stdSimplex.ext _ _ fun i ↦
      congrArg ULift.down (atomSimplexMaxVertex_simplexHom.{u} θ.toOrderHom (z.obj i).down)

private noncomputable def stdSimplexCompFaceNerveIso :
    SSet.stdSimplex ⋙ SSet.toDiagSet.{u} ⋙ faceNerve ≅
      simplexFunctor ⋙ atomToRDCpx ⋙ rdcFaceNerve :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight stdSimplexCompToDiagSetIso faceNerve ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft simplexFunctor yonedaCompFaceNerveIso

private theorem isLeftKanExtension_toDiagSet_comp_faceNerve :
    (SSet.toDiagSet.{u} ⋙ faceNerve).IsLeftKanExtension
      (𝟙 (SSet.stdSimplex ⋙ SSet.toDiagSet ⋙ faceNerve)) :=
  have : PreservesColimitsOfSize.{0, u} SSet.toDiagSet.{u} :=
    sSetDiagSetAdj.leftAdjoint_preservesColimits
  Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} _ (Iso.refl _)

noncomputable def faceNerveToDiagSetFlat :
    SSet.toDiagSet.{u} ⋙ faceNerve ⟶ MarkedPresheaf.flat edgeMarking :=
  have := isLeftKanExtension_toDiagSet_comp_faceNerve.{u}
  (SSet.toDiagSet.{u} ⋙ faceNerve).descOfIsLeftKanExtension (𝟙 _) _
    (stdSimplexCompFaceNerveIso.hom ≫ faceNerveSimplexMaxVertexNatTrans)

theorem weakEquivalence_faceNerveToDiagSetFlat_app (K : SSet.{u}) :
    WeakEquivalence (faceNerveToDiagSetFlat.app K) := by
  have : PreservesColimitsOfSize.{u, u} SSet.toDiagSet.{u} :=
    sSetDiagSetAdj.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u, u} (MarkedPresheaf.flat.{u, 0} edgeMarking) :=
    (MarkedPresheaf.flatForgetAdjunction edgeMarking).leftAdjoint_preservesColimits
  have := isLeftKanExtension_toDiagSet_comp_faceNerve.{u}
  refine MarkedSSet.weakEquivalence_app_of_stdSimplex _ _ _ (fun n ↦ ?_) K
  have h := (SSet.toDiagSet.{u} ⋙ faceNerve).descOfIsLeftKanExtension_fac_app (𝟙 _)
    (MarkedPresheaf.flat edgeMarking)
    (stdSimplexCompFaceNerveIso.hom ≫ faceNerveSimplexMaxVertexNatTrans) ⦋n⦌
  rw [NatTrans.id_app, Category.id_comp] at h
  change WeakEquivalence ((SSet.toDiagSet.{u} ⋙ faceNerve).descOfIsLeftKanExtension (𝟙 _) _
    (stdSimplexCompFaceNerveIso.hom ≫ faceNerveSimplexMaxVertexNatTrans) |>.app _)
  rw [h]
  exact (weakEquivalence_iff _).2 ((weakEquivalences MarkedSSet).comp_mem _ _
    ((weakEquivalences MarkedSSet).of_isIso (stdSimplexCompFaceNerveIso.hom.app ⦋n⦌))
    ((weakEquivalence_iff _).1 (weakEquivalence_faceNerveSimplexMaxVertex n)))

theorem exists_weakEquivalence_faceNerve_toDiagSet :
    ∃ l : SSet.toDiagSet.{u} ⋙ faceNerve ⟶ MarkedPresheaf.flat edgeMarking,
      ∀ K : SSet.{u}, WeakEquivalence (l.app K) :=
  ⟨faceNerveToDiagSetFlat, weakEquivalence_faceNerveToDiagSetFlat_app⟩

end Contraction

end Atoms.Diagrammatic
