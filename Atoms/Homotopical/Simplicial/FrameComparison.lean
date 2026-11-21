import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Comparison
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.FrameKan
import Atoms.Homotopical.Simplicial.FunctionComplex

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open Atoms.Homotopical SSet.modelCategoryQuillen

universe v u

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasLimits C] [HasColimits C]
  {F : SSet.{v} ⥤ C} {G : C ⥤ SSet.{v}} {adj : F ⊣ G}

theorem IsQuillen.functionComplexCospan (h : adj.IsQuillen) {X : C}
    (Y : SimplicialFrame X) :
    ∃ (D : SSet.{v}) (l : G.obj X ⟶ D)
      (r : Y.obj.functionComplex (F.obj Δ[0]) ⟶ D),
      WeakEquivalence l ∧ WeakEquivalence r := by
  let A := h.cosimplicialFrame
  let B := doubleFunctionComplex A.obj Y.obj
  let e : G.obj X ≅ B _⦋0⦌ :=
    G.mapIso Y.iso.symm ≪≫ (adj.functionComplexStdSimplexIso.app (Y.obj _⦋0⦌)).symm
  let e' : Y.obj.functionComplex (F.obj Δ[0]) ≅
      (SSet.transpose.obj B) _⦋0⦌ :=
    (transposeDoubleFunctionComplexIso A.obj Y.obj).app _ |>.symm
  have : WeakEquivalence (SSet.toDiag B) :=
    (weakEquivalence_iff _).2 (kanWeak_toDiag_cotensorSide A Y)
  have : WeakEquivalence (SSet.toDiag (SSet.transpose.obj B)) :=
    (weakEquivalence_iff _).2 (kanWeak_toDiag_functionComplexSide A Y)
  exact ⟨SSet.diag.obj B, e.hom ≫ SSet.toDiag B,
    e'.hom ≫ SSet.toDiag (SSet.transpose.obj B) ≫ SSet.diagTransposeIso.hom.app B,
    inferInstance, inferInstance⟩

theorem IsQuillen.exists_weakEquivalence_functionComplex (h : adj.IsQuillen) {X : C}
    (Y : SimplicialFrame X) :
    ∃ f : G.obj X ⟶ Y.obj.functionComplex (F.obj Δ[0]), WeakEquivalence f := by
  have (K : SSet.{v}) : IsCofibrant K := cofibration_of_mono _
  have : IsCofibrant (F.obj Δ[0]) := h.isCofibrant_obj Δ[0]
  have := Y.kanComplex_functionComplex (F.obj Δ[0])
  obtain ⟨D, l, r, hl, hr⟩ := h.functionComplexCospan Y
  have := hl
  have := hr
  exact exists_weakEquivalence_of_cospan l r

theorem IsQuillen.exists_weakEquivalence_of_point_iso
    {F' : SSet.{v} ⥤ C} {G' : C ⥤ SSet.{v}} {adj' : F' ⊣ G'}
    (h : adj.IsQuillen) (h' : adj'.IsQuillen) {X : C} (Y : SimplicialFrame X)
    (e : F.obj Δ[0] ≅ F'.obj Δ[0]) :
    ∃ f : G.obj X ⟶ G'.obj X, WeakEquivalence f := by
  have (K : SSet.{v}) : IsCofibrant K := cofibration_of_mono _
  have : IsCofibrant (F'.obj Δ[0]) := h'.isCofibrant_obj Δ[0]
  have := Y.kanComplex_functionComplex (F'.obj Δ[0])
  have := Y.isFibrant
  have := h'.isFibrant_obj X
  obtain ⟨f, hf⟩ := h.exists_weakEquivalence_functionComplex Y
  obtain ⟨g, hg⟩ := h'.exists_weakEquivalence_functionComplex Y
  have hf' : WeakEquivalence f := hf
  have hg' : WeakEquivalence g := hg
  obtain ⟨g', h₁, h₂⟩ := RightHomotopyClass.whitehead g
  have hg'' : WeakEquivalence g' := weakEquivalence_of_rightHomotopyRel g' g h₂ h₁
  let i : Y.obj.functionComplex (F.obj Δ[0]) ≅ Y.obj.functionComplex (F'.obj Δ[0]) :=
    Y.obj.functionComplexFunctor.mapIso e.symm.op
  have hi : WeakEquivalence i.hom := inferInstance
  exact ⟨f ≫ i.hom ≫ g', inferInstance⟩

theorem IsQuillen.exists_weakEquivalence_of_point_iso_of_replacement
    {F' : SSet.{v} ⥤ C} {G' : C ⥤ SSet.{v}} {adj' : F' ⊣ G'}
    (h : adj.IsQuillen) (h' : adj'.IsQuillen) {X Z : C} [IsFibrant X]
    (Y : SimplicialFrame Z) (η : X ⟶ Z) [WeakEquivalence η]
    (e : F.obj Δ[0] ≅ F'.obj Δ[0]) :
    ∃ f : G.obj X ⟶ G'.obj X, WeakEquivalence f := by
  have hZ : IsFibrant Z := Y.isFibrant
  have hG'X : IsFibrant (G'.obj X) := h'.isFibrant_obj X
  have hG'Z : IsFibrant (G'.obj Z) := h'.isFibrant_obj Z
  have (K : SSet.{v}) : IsCofibrant K := cofibration_of_mono _
  have hη : WeakEquivalence (G.map η) := h.weakEquivalence_map_of_isFibrant η
  have hη' : WeakEquivalence (G'.map η) := h'.weakEquivalence_map_of_isFibrant η
  obtain ⟨g, hg⟩ := h.exists_weakEquivalence_of_point_iso h' Y e
  obtain ⟨r, h₁, h₂⟩ := RightHomotopyClass.whitehead (G'.map η)
  have hr : WeakEquivalence r := weakEquivalence_of_rightHomotopyRel r (G'.map η) h₂ h₁
  exact ⟨G.map η ≫ g ≫ r, inferInstance⟩

private lemma comp_eq_comp_of_squares {D : Type*} [Category D] {X₀ X₁ X₂ Y₀ Y₁ Y₂ : D}
    {f₁ : X₀ ⟶ X₁} {f₂ : X₁ ⟶ X₂} {g₁ : Y₀ ⟶ Y₁} {g₂ : Y₁ ⟶ Y₂}
    {v₀ : X₀ ⟶ Y₀} {v₁ : X₁ ⟶ Y₁} {v₂ : X₂ ⟶ Y₂} (h₁ : f₁ ≫ v₁ = v₀ ≫ g₁)
    (h₂ : f₂ ≫ v₂ = v₁ ≫ g₂) : (f₁ ≫ f₂) ≫ v₂ = v₀ ≫ g₁ ≫ g₂ := by
  rw [Category.assoc, h₂, reassoc_of% h₁]

theorem IsQuillen.weakEquivalence_map_iff_functionComplex (h : adj.IsQuillen) {X X' : C}
    (Y : SimplicialFrame X) (Y' : SimplicialFrame X') (φ : X ⟶ X') (ψ : Y.obj ⟶ Y'.obj)
    (hψ : ψ.app (Opposite.op ⦋0⦌) ≫ Y'.iso.hom = Y.iso.hom ≫ φ) :
    WeakEquivalence (G.map φ) ↔ WeakEquivalence
      (Functor.whiskerRight ψ (coyoneda.obj (Opposite.op (F.obj Δ[0]))) :
        Y.obj.functionComplex (F.obj Δ[0]) ⟶ Y'.obj.functionComplex (F.obj Δ[0])) := by
  let A := h.cosimplicialFrame
  let B := doubleFunctionComplex A.obj Y.obj
  let B' := doubleFunctionComplex A.obj Y'.obj
  let β : B ⟶ B' := Functor.whiskerRight ψ (opOp C ⋙ A.obj.functionComplexFunctor)
  have : WeakEquivalence (SSet.toDiag B) :=
    (weakEquivalence_iff _).2 (kanWeak_toDiag_cotensorSide A Y)
  have : WeakEquivalence (SSet.toDiag B') :=
    (weakEquivalence_iff _).2 (kanWeak_toDiag_cotensorSide A Y')
  have : WeakEquivalence (SSet.toDiag (SSet.transpose.obj B)) :=
    (weakEquivalence_iff _).2 (kanWeak_toDiag_functionComplexSide A Y)
  have : WeakEquivalence (SSet.toDiag (SSet.transpose.obj B')) :=
    (weakEquivalence_iff _).2 (kanWeak_toDiag_functionComplexSide A Y')
  let fc := adj.functionComplexStdSimplexIso
  let ψ₀ := ψ.app (Opposite.op ⦋0⦌)
  let fψ : Y.obj.functionComplex (F.obj Δ[0]) ⟶ Y'.obj.functionComplex (F.obj Δ[0]) :=
    Functor.whiskerRight ψ (coyoneda.obj (Opposite.op (F.obj Δ[0])))
  let e : G.obj X ≅ B _⦋0⦌ := G.mapIso Y.iso.symm ≪≫ (fc.app (Y.obj _⦋0⦌)).symm
  let e' : G.obj X' ≅ B' _⦋0⦌ := G.mapIso Y'.iso.symm ≪≫ (fc.app (Y'.obj _⦋0⦌)).symm
  let t : Y.obj.functionComplex (F.obj Δ[0]) ≅ (SSet.transpose.obj B) _⦋0⦌ :=
    ((transposeDoubleFunctionComplexIso A.obj Y.obj).app _).symm
  let t' : Y'.obj.functionComplex (F.obj Δ[0]) ≅ (SSet.transpose.obj B') _⦋0⦌ :=
    ((transposeDoubleFunctionComplexIso A.obj Y'.obj).app _).symm
  have hφ : G.map Y.iso.inv ≫ G.map ψ₀ = G.map φ ≫ G.map Y'.iso.inv := by
    rw [← G.map_comp, ← G.map_comp]
    congr 1
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have he : e.hom ≫ β.app (Opposite.op ⦋0⦌) = G.map φ ≫ e'.hom :=
    comp_eq_comp_of_squares hφ (fc.inv.naturality ψ₀).symm
  have sq₁ : (e.hom ≫ SSet.toDiag B) ≫ SSet.diag.map β = G.map φ ≫ e'.hom ≫ SSet.toDiag B' :=
    comp_eq_comp_of_squares he (SSet.toDiag_naturality β)
  have ht : t.hom ≫ (SSet.transpose.map β).app (Opposite.op ⦋0⦌) = fψ ≫ t'.hom := by
    ext b x
    rfl
  have sq₂ : (t.hom ≫ SSet.toDiag (SSet.transpose.obj B) ≫ SSet.diagTransposeIso.hom.app B) ≫
      SSet.diag.map β = fψ ≫ t'.hom ≫ SSet.toDiag (SSet.transpose.obj B') ≫
        SSet.diagTransposeIso.hom.app B' :=
    comp_eq_comp_of_squares ht (comp_eq_comp_of_squares
      (SSet.toDiag_naturality (SSet.transpose.map β))
      (SSet.diagTransposeIso.hom.naturality β).symm)
  have hl : WeakEquivalence (e.hom ≫ SSet.toDiag B) := inferInstance
  have hl' : WeakEquivalence (e'.hom ≫ SSet.toDiag B') := inferInstance
  have hr : WeakEquivalence
      (t.hom ≫ SSet.toDiag (SSet.transpose.obj B) ≫ SSet.diagTransposeIso.hom.app B) :=
    inferInstance
  have hr' : WeakEquivalence
      (t'.hom ≫ SSet.toDiag (SSet.transpose.obj B') ≫ SSet.diagTransposeIso.hom.app B') :=
    inferInstance
  exact (weakEquivalence_postcomp_iff (G.map φ) (e'.hom ≫ SSet.toDiag B')).symm.trans
    ((iff_of_eq (congrArg (WeakEquivalence ·) sq₁.symm)).trans
      ((weakEquivalence_precomp_iff (e.hom ≫ SSet.toDiag B) (SSet.diag.map β)).trans
        ((weakEquivalence_precomp_iff
          (t.hom ≫ SSet.toDiag (SSet.transpose.obj B) ≫ SSet.diagTransposeIso.hom.app B)
          (SSet.diag.map β)).symm.trans
          ((iff_of_eq (congrArg (WeakEquivalence ·) sq₂)).trans
            (weakEquivalence_postcomp_iff fψ _)))))

omit [HasLimits C] [HasColimits C] in
theorem IsQuillen.weakEquivalence_map_iff_of_comp_eq (h : adj.IsQuillen) {X X' Z Z' : C}
    [hX : IsFibrant X] [hX' : IsFibrant X'] [hZ : IsFibrant Z] [hZ' : IsFibrant Z'] (η : X ⟶ Z)
    [hη : WeakEquivalence η] (η' : X' ⟶ Z') [hη' : WeakEquivalence η'] (φ : X ⟶ X')
    (ζ : Z ⟶ Z') (hζ : η ≫ ζ = φ ≫ η') :
    WeakEquivalence (G.map φ) ↔ WeakEquivalence (G.map ζ) := by
  have := h.weakEquivalence_map_of_isFibrant η
  have := h.weakEquivalence_map_of_isFibrant η'
  have sq : G.map η ≫ G.map ζ = G.map φ ≫ G.map η' := by rw [← G.map_comp, hζ, G.map_comp]
  exact (weakEquivalence_postcomp_iff (G.map φ) (G.map η')).symm.trans
    ((iff_of_eq (congrArg (WeakEquivalence ·) sq.symm)).trans
      (weakEquivalence_precomp_iff (G.map η) (G.map ζ)))

theorem IsQuillen.weakEquivalence_map_iff_of_point_iso
    {F' : SSet.{v} ⥤ C} {G' : C ⥤ SSet.{v}} {adj' : F' ⊣ G'}
    (h : adj.IsQuillen) (h' : adj'.IsQuillen) {X X' : C} (Y : SimplicialFrame X)
    (Y' : SimplicialFrame X') (φ : X ⟶ X') (ψ : Y.obj ⟶ Y'.obj)
    (hψ : ψ.app (Opposite.op ⦋0⦌) ≫ Y'.iso.hom = Y.iso.hom ≫ φ)
    (e : F.obj Δ[0] ≅ F'.obj Δ[0]) :
    WeakEquivalence (G.map φ) ↔ WeakEquivalence (G'.map φ) := by
  let i : Y.obj.functionComplex (F.obj Δ[0]) ≅ Y.obj.functionComplex (F'.obj Δ[0]) :=
    Y.obj.functionComplexFunctor.mapIso e.symm.op
  let i' : Y'.obj.functionComplex (F.obj Δ[0]) ≅ Y'.obj.functionComplex (F'.obj Δ[0]) :=
    Y'.obj.functionComplexFunctor.mapIso e.symm.op
  have sq : i.hom ≫ Functor.whiskerRight ψ (coyoneda.obj (Opposite.op (F'.obj Δ[0]))) =
      Functor.whiskerRight ψ (coyoneda.obj (Opposite.op (F.obj Δ[0]))) ≫ i'.hom := by
    ext n x
    exact Category.assoc _ _ _
  have hi : WeakEquivalence i.hom := inferInstance
  have hi' : WeakEquivalence i'.hom := inferInstance
  exact (h.weakEquivalence_map_iff_functionComplex Y Y' φ ψ hψ).trans
    (((weakEquivalence_postcomp_iff _ i'.hom).symm.trans
      ((iff_of_eq (congrArg (WeakEquivalence ·) sq.symm)).trans
        (weakEquivalence_precomp_iff i.hom _))).trans
      (h'.weakEquivalence_map_iff_functionComplex Y Y' φ ψ hψ).symm)

end CategoryTheory.Adjunction
