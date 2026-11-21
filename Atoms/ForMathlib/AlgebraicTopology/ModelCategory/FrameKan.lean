import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Frame
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Spine

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe v u

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasLimits C]

namespace CategoryTheory.SimplicialObject

omit [ModelCategory C] in
theorem isPullback_cotensorFunctor_bicartSq (Y : SimplicialObject C) {X : SSet.{v}}
    {A₁ A₂ A₃ A₄ : X.Subcomplex} (sq : SSet.Subcomplex.BicartSq A₁ A₂ A₃ A₄) :
    IsPullback ((cotensorFunctor Y).map (SSet.Subcomplex.homOfLE sq.le₃₄)).unop
      ((cotensorFunctor Y).map (SSet.Subcomplex.homOfLE sq.le₂₄)).unop
      ((cotensorFunctor Y).map (SSet.Subcomplex.homOfLE sq.le₁₃)).unop
      ((cotensorFunctor Y).map (SSet.Subcomplex.homOfLE sq.le₁₂)).unop :=
  (sq.isPushout.map (cotensorFunctor Y)).unop

omit [ModelCategory C] in
theorem cotensorFunctor_map_stdSimplex_unop_comp (Y : SimplicialObject C) {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) :
    ((cotensorFunctor Y).map (SSet.stdSimplex.map f)).unop ≫ (cotensorStdSimplexIso Y m).hom =
      (cotensorStdSimplexIso Y n).hom ≫ Y.map f.op := by
  have h := (Functor.pointwiseLeftKanExtensionUnit uliftYoneda.{v} Y.rightOp).naturality f
  exact congrArg Quiver.Hom.unop h.symm

omit [HasLimits C] in
private lemma weakEquivalence_of_isIso' {A B : C} (e : A ⟶ B) [IsIso e] : WeakEquivalence e :=
  (weakEquivalence_iff _).2 ((weakEquivalences C).of_isIso e)

private instance (Y : SimplicialObject C) (n : ℕ) :
    WeakEquivalence (cotensorStdSimplexIso.{v} Y n).hom :=
  weakEquivalence_of_isIso' _

theorem trivialFibrations_cotensorFunctor_map_face_ι {Y : SimplicialObject C}
    (hY : Y.IsReedyFibrant) (hY' : Y.IsHomotopicallyConstant) (n : ℕ) (i : Fin (n + 2)) :
    trivialFibrations C
      ((cotensorFunctor Y).map (SSet.stdSimplex.face.{v} {i}ᶜ).ι).unop := by
  rw [← SSet.stdSimplex.range_δ]
  set δi : (Δ[n] : SSet.{v}) ⟶ Δ[n + 1] := SSet.stdSimplex.δ i with hδi
  have : IsIso ((cotensorFunctor Y).map (SSet.Subcomplex.toRange δi)).unop := inferInstance
  have := weakEquivalence_of_isIso' ((cotensorFunctor Y).map (SSet.Subcomplex.toRange δi)).unop
  have hf := hY.fibration_cotensorFunctor_map_unop (SSet.Subcomplex.range δi).ι
  have h1 : WeakEquivalence ((cotensorFunctor Y).map δi).unop := by
    have h := cotensorFunctor_map_stdSimplex_unop_comp.{v} Y (m := n) (n := n + 1)
      (SimplexCategory.δ i)
    refine (weakEquivalence_iff _).2 ((weakEquivalences C).of_postcomp _
      (cotensorStdSimplexIso Y n).hom ((weakEquivalences C).of_isIso _) ?_)
    have h3 : weakEquivalences C
        ((cotensorStdSimplexIso Y (n + 1)).hom ≫ Y.map (SimplexCategory.δ i).op) :=
      (weakEquivalences C).comp_mem _ _ ((weakEquivalences C).of_isIso _)
        ((weakEquivalence_iff _).1 (hY' (SimplexCategory.δ i)))
    exact h.symm ▸ h3
  have h2 : ((cotensorFunctor Y).map (SSet.Subcomplex.range δi).ι).unop ≫
      ((cotensorFunctor Y).map (SSet.Subcomplex.toRange δi)).unop =
        ((cotensorFunctor Y).map δi).unop := by
    rw [← unop_comp, ← Functor.map_comp, SSet.Subcomplex.toRange_ι]
  have := weakEquivalence_of_postcomp_of_fac h2
  exact ⟨(fibration_iff _).1 hf, (weakEquivalence_iff _).1 this⟩

private noncomputable def arrowIsoCotensor (Y : SimplicialObject C) {K L K' L' : SSet.{v}}
    {f : K ⟶ L} {g : K' ⟶ L'} (e : Arrow.mk f ≅ Arrow.mk g) :
    Arrow.mk ((cotensorFunctor Y).map f).unop ≅ Arrow.mk ((cotensorFunctor Y).map g).unop :=
  Arrow.isoMk
    { hom := ((cotensorFunctor Y).map e.inv.right).unop
      inv := ((cotensorFunctor Y).map e.hom.right).unop
      hom_inv_id := by
        rw [← unop_comp, ← Functor.map_comp, Arrow.hom_inv_id_right]; simp
      inv_hom_id := by
        rw [← unop_comp, ← Functor.map_comp, Arrow.inv_hom_id_right]; simp }
    { hom := ((cotensorFunctor Y).map e.inv.left).unop
      inv := ((cotensorFunctor Y).map e.hom.left).unop
      hom_inv_id := by
        rw [← unop_comp, ← Functor.map_comp, Arrow.hom_inv_id_left]; simp
      inv_hom_id := by
        rw [← unop_comp, ← Functor.map_comp, Arrow.inv_hom_id_left]; simp }
    (by
      dsimp
      rw [← unop_comp, ← unop_comp, ← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (fun t => ((cotensorFunctor Y).map t).unop) (Arrow.w e.inv).symm)

private lemma trivialFibrations_map_sup_face_ι {Y : SimplicialObject C} (hY : Y.IsReedyFibrant)
    {m : ℕ} (i : Fin (m + 2)) (A : (Δ[m + 1] : SSet.{v}).Subcomplex)
    (hA : trivialFibrations C ((cotensorFunctor Y).map A.ι).unop)
    (hB : trivialFibrations C
      ((cotensorFunctor Y).map (A.preimage (SSet.stdSimplex.δ i)).ι).unop) :
    trivialFibrations C ((cotensorFunctor Y).map (A ⊔ SSet.stdSimplex.face {i}ᶜ).ι).unop := by
  have sq : SSet.Subcomplex.BicartSq (A ⊓ SSet.stdSimplex.face {i}ᶜ) A
      (SSet.stdSimplex.face {i}ᶜ) (A ⊔ SSet.stdSimplex.face {i}ᶜ) :=
    { sup_eq := rfl, inf_eq := rfl }
  have h' := (MorphismProperty.arrow_mk_iso_iff (trivialFibrations C)
    (arrowIsoCotensor Y (SSet.Subcomplex.preimageιArrowIso (SSet.stdSimplex.δ i) A))).1 hB
  rw [SSet.stdSimplex.range_δ] at h'
  have hg := MorphismProperty.of_isPullback (isPullback_cotensorFunctor_bicartSq Y sq) h'
  have hf := hY.fibration_cotensorFunctor_map_unop (A ⊔ SSet.stdSimplex.face {i}ᶜ).ι
  have fac : ((cotensorFunctor Y).map (A ⊔ SSet.stdSimplex.face {i}ᶜ).ι).unop ≫
      ((cotensorFunctor Y).map (SSet.Subcomplex.homOfLE sq.le₂₄)).unop =
        ((cotensorFunctor Y).map A.ι).unop := by
    rw [← unop_comp, ← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]
  have := (weakEquivalence_iff _).2 hg.2
  have := (weakEquivalence_iff _).2 hA.2
  have := weakEquivalence_of_postcomp_of_fac fac
  exact ⟨(fibration_iff _).1 hf, (weakEquivalence_iff _).1 this⟩

private lemma facesOutside_compl_singleton (n : ℕ) (i : Fin (n + 1)) :
    SSet.stdSimplex.facesOutside.{v} n {i}ᶜ = SSet.stdSimplex.face {i}ᶜ := by
  ext ⟨d⟩ x
  induction d using SimplexCategory.rec with | _ d => ?_
  simp [SSet.stdSimplex.mem_face_iff]

theorem trivialFibrations_cotensorFunctor_map_facesOutside_ι {Y : SimplicialObject C}
    (hY : Y.IsReedyFibrant) (hY' : Y.IsHomotopicallyConstant) {n : ℕ}
    (S : Finset (Fin (n + 1))) (hS : S.Nonempty) (hS' : S ≠ Finset.univ) :
    trivialFibrations C
      ((cotensorFunctor Y).map (SSet.stdSimplex.facesOutside.{v} n S).ι).unop := by
  induction n with
  | zero =>
    obtain ⟨x, hx⟩ := hS
    exact absurd (Finset.eq_univ_of_forall fun a ↦ by
      rw [Fin.ext (show (a : ℕ) = x by have := a.isLt; have := x.isLt; omega)]; exact hx) hS'
  | succ m ih =>
    suffices h : ∀ Z : Finset (Fin (m + 2)), Z.Nonempty → Z ≠ Finset.univ →
        trivialFibrations C
          ((cotensorFunctor Y).map (SSet.stdSimplex.facesOutside.{v} (m + 1) Zᶜ).ι).unop by
      have := h Sᶜ (by simpa [Finset.nonempty_iff_ne_empty] using hS')
        ((Finset.compl_ne_univ_iff_nonempty _).2 hS)
      rwa [compl_compl] at this
    intro Z
    induction Z using Finset.induction_on with
    | empty => intro h; exact absurd h (by simp)
    | insert i Z' hi ihZ =>
      intro _ hne
      by_cases hZ' : Z' = ∅
      · subst hZ'
        rw [Finset.insert_empty, facesOutside_compl_singleton]
        exact trivialFibrations_cotensorFunctor_map_face_ι hY hY' m i
      · have hZ'ne : Z'.Nonempty := Finset.nonempty_iff_ne_empty.2 hZ'
        have hZ'u : Z' ≠ Finset.univ := fun h ↦ hi (h ▸ Finset.mem_univ i)
        have hA := ihZ hZ'ne hZ'u
        have hiC : i ∈ Z'ᶜ := Finset.mem_compl.2 hi
        have hpre := SSet.stdSimplex.preimage_facesOutside.{v} Z'ᶜ i hiC
        obtain ⟨s, hs⟩ : ∃ s, s ∉ insert i Z' := by
          by_contra! h
          exact hne (Finset.eq_univ_of_forall h)
        obtain ⟨z, hz⟩ := hZ'ne
        obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq (x := s) (y := i)
          (by rintro rfl; exact hs (Finset.mem_insert_self _ _))
        obtain ⟨u, rfl⟩ := Fin.exists_succAbove_eq (x := z) (y := i)
          (by rintro rfl; exact hi hz)
        have hB := ih (Z'ᶜ.preimage i.succAbove (Fin.succAbove_right_injective.injOn))
          ⟨t, by simpa using fun h ↦ hs (Finset.mem_insert_of_mem h)⟩
          (fun h ↦ by
            have : u ∈ Z'ᶜ.preimage i.succAbove (Fin.succAbove_right_injective.injOn) := by
              rw [h]; exact Finset.mem_univ _
            exact Finset.mem_compl.1 (Finset.mem_preimage.1 this) hz)
        rw [← hpre] at hB
        have key := trivialFibrations_map_sup_face_ι hY i _ hA hB
        rw [SSet.stdSimplex.facesOutside_sup_face] at key
        have hset : Z'ᶜ.erase i = (insert i Z')ᶜ := by
          ext a; simp [Finset.mem_erase]
        rwa [hset] at key

theorem trivialFibrations_cotensorFunctor_map_horn_ι {Y : SimplicialObject C}
    (hY : Y.IsReedyFibrant) (hY' : Y.IsHomotopicallyConstant) (n : ℕ) (k : Fin (n + 2)) :
    trivialFibrations C ((cotensorFunctor Y).map Λ[n + 1, k].ι).unop := by
  have h := trivialFibrations_cotensorFunctor_map_facesOutside_ι hY hY' {k}
    (Finset.singleton_nonempty k) (fun h ↦ by
      have := congrArg Finset.card h
      simp at this)
  rwa [SSet.stdSimplex.facesOutside_singleton] at h

theorem IsReedyFibrant.rlp_J_functionComplex_map {Y : SimplicialObject C}
    (hY : Y.IsReedyFibrant) (hY' : Y.IsHomotopicallyConstant) {A B : C} (j : A ⟶ B)
    [Cofibration j] :
    SSet.modelCategoryQuillen.J.rlp ((functionComplexFunctor Y).map j.op) := by
  have hlift (n : ℕ) (k : Fin (n + 2)) :
      HasLiftingProperty Λ[n + 1, k].ι ((functionComplexFunctor Y).map j.op) := by
    have h := trivialFibrations_cotensorFunctor_map_horn_ι hY hY' n k
    have := (fibration_iff _).2 h.1
    have := (weakEquivalence_iff _).2 h.2
    have h2 : HasLiftingProperty j ((cotensorFunctor Y).map Λ[n + 1, k].ι).unop := inferInstance
    exact (hasLiftingProperty_cotensor_map_iff Y j Λ[n + 1, k].ι).1 h2
  intro K L i hi
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  exact hlift n k

private noncomputable def isTerminalFunctionComplex (Y : SimplicialObject C) {A : C}
    (hA : IsInitial A) : IsTerminal (Y.functionComplex A) :=
  IsTerminal.ofUniqueHom
    (fun X ↦ { app := fun n ↦
                 TypeCat.ofHom fun _ ↦ (hA.to (Y.obj n) : (Y.functionComplex A).obj n)
               naturality := fun _ _ _ ↦ by ext; exact hA.hom_ext _ _ })
    (fun X m ↦ by ext n x; exact hA.hom_ext _ _)

theorem IsReedyFibrant.kanComplex_functionComplex {Y : SimplicialObject C}
    (hY : Y.IsReedyFibrant) (hY' : Y.IsHomotopicallyConstant) (A : C) [IsCofibrant A] :
    (Y.functionComplex A).KanComplex := by
  have := hY.rlp_J_functionComplex_map hY' (initial.to A)
  exact (isFibrant_iff_of_isTerminal _
    (isTerminalFunctionComplex Y (initialIsInitial (C := C)))).2
    ((SSet.modelCategoryQuillen.fibration_iff _).2 this)

end CategoryTheory.SimplicialObject

namespace HomotopicalAlgebra

theorem SimplicialFrame.rlp_J_functionComplex_map {X : C} (Y : SimplicialFrame X) {A B : C}
    (j : A ⟶ B) [Cofibration j] :
    SSet.modelCategoryQuillen.J.rlp ((SimplicialObject.functionComplexFunctor Y.obj).map j.op) :=
  Y.isReedyFibrant.rlp_J_functionComplex_map Y.isHomotopicallyConstant j

theorem SimplicialFrame.kanComplex_functionComplex {X : C} (Y : SimplicialFrame X) (A : C)
    [IsCofibrant A] : (Y.obj.functionComplex A).KanComplex :=
  Y.isReedyFibrant.kanComplex_functionComplex Y.isHomotopicallyConstant A

end HomotopicalAlgebra
