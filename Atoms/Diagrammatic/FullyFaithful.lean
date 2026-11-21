import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.PiZero
import Atoms.Diagrammatic.Suspension.Hom
import Atoms.Diagrammatic.HomotopyCategory
import Atoms.Diagrammatic.Localization.MappingPathSpace
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

open CategoryTheory Limits Simplicial HomotopicalAlgebra Opposite MorphismProperty
open Atoms.Homotopical Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open scoped ReversiblePathSpace

variable {X Y Z : DiagSet.{u}}

private theorem bijective_mapπ₀_of_rlp_monomorphisms {A B : DiagSet.{u}} {g : A ⟶ B}
    (hg : (MorphismProperty.monomorphisms DiagSet.{u}).rlp g) :
    Function.Bijective (SSet.mapπ₀ (DiagSet.toSSet.map g)) := by
  refine SSet.bijective_mapπ₀_of_rlp_monomorphisms (fun _ _ i hi => ?_)
  have : Mono i := hi
  rw [← sSetDiagSetAdj.hasLiftingProperty_iff]
  exact hg _ (MorphismProperty.monomorphisms.infer_property _)

theorem DiagSet.bijective_mapπ₀_of_weakEquivalence {G H : DiagSet.{u}}
    (hG : IsInftyCategory 0 G) (hH : IsInftyCategory 0 H) (f : G ⟶ H)
    [WeakEquivalence ((DiagSet.toInfty 0).map f)] :
    Function.Bijective (SSet.mapπ₀ (DiagSet.toSSet.map f)) := by
  have : WeakEquivalence ((DiagSet.toInfty 0).map (reversibleMappingPathSpaceIncl f)) :=
    weakEquivalence_reversibleMappingPathSpaceIncl f 0 hH
  have : Fibration ((DiagSet.toInfty 0).map (reversibleMappingPathSpaceProj f)) :=
    fibration_reversibleMappingPathSpaceProj f 0 hG hH
  have : WeakEquivalence ((DiagSet.toInfty 0).map (reversibleMappingPathSpaceProj f)) :=
    weakEquivalence_of_precomp_of_fac (f := (DiagSet.toInfty 0).map
      (reversibleMappingPathSpaceIncl f))
      (by rw [← CategoryTheory.Functor.map_comp, reversibleMappingPathSpaceIncl_proj])
  have hπ := bijective_mapπ₀_of_rlp_monomorphisms
    (rlp_monomorphisms_of_trivialFibration_toInfty_map 0
      (g := reversibleMappingPathSpaceProj f))
  have hr := bijective_mapπ₀_of_rlp_monomorphisms
    (rlp_monomorphisms_reversibleMappingPathSpace_fst f 0 hH)
  have hri : ∀ x, SSet.mapπ₀ (DiagSet.toSSet.map (pullback.fst f ((π̃ false).app H)))
      (SSet.mapπ₀ (DiagSet.toSSet.map (reversibleMappingPathSpaceIncl f)) x) = x := fun x => by
    rw [← SSet.mapπ₀_comp_apply, ← CategoryTheory.Functor.map_comp,
      reversibleMappingPathSpaceIncl_fst, CategoryTheory.Functor.map_id, SSet.mapπ₀_id_apply]
  have hi : Function.Bijective
      (SSet.mapπ₀ (DiagSet.toSSet.map (reversibleMappingPathSpaceIncl f))) :=
    ⟨Function.LeftInverse.injective hri, fun y => ⟨_, hr.1 (hri _)⟩⟩
  have hcomp : SSet.mapπ₀ (DiagSet.toSSet.map f) =
      SSet.mapπ₀ (DiagSet.toSSet.map (reversibleMappingPathSpaceProj f)) ∘
        SSet.mapπ₀ (DiagSet.toSSet.map (reversibleMappingPathSpaceIncl f)) := funext fun x => by
    rw [Function.comp_apply, ← SSet.mapπ₀_comp_apply, ← CategoryTheory.Functor.map_comp,
      reversibleMappingPathSpaceIncl_proj]
  rw [hcomp]
  exact hπ.comp hi

variable {x y : X.Vertex}

private theorem bipointedHomVerticesEquiv_map (F : X ⟶ Y)
    (w : (bipointedHom.obj (X.bipoint x y)).Vertex) :
    Y.bipointedHomVerticesEquiv (x.map F) (y.map F)
        (w.map (bipointedHom.map (DiagSet.bipointMap F x y))) =
      (X.bipointedHomVerticesEquiv x y w).map F := by
  refine Y.edgeEquivSSet.injective ((SSet.Edge.ext ?_).trans (DiagSet.edgeEquivSSet_map _ F).symm)
  refine (DiagSet.bipointedHomVerticesEquiv_edge _ _ _).trans (Eq.trans ?_
    (congrArg (F.app _) (DiagSet.bipointedHomVerticesEquiv_edge x y _).symm))
  refine Eq.trans (congrArg _ ?_) (NatTrans.naturality_apply F _ _).symm
  exact uliftYonedaEquiv_comp (F := X) (bipointedHomObjEquiv (X.bipoint x y) (atomSimplex 0) w).1 F

theorem DiagSet.bipointedHomπ₀Equiv_mapπ₀ (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (F : X ⟶ Y) (x y : X.Vertex)
    (v : SSet.π₀ (DiagSet.toSSet.obj (bipointedHom.obj (X.bipoint x y)))) :
    Y.bipointedHomπ₀Equiv hY _ _
        (SSet.mapπ₀ (DiagSet.toSSet.map (bipointedHom.map (DiagSet.bipointMap F x y))) v) =
      (homotopyFunctor hX.1 hY.1 F).map (X.bipointedHomπ₀Equiv hX x y v) := by
  induction v with | mk w => ?_
  obtain ⟨e, rfl⟩ :=
    ((DiagSet.vertexEquivSSet _).symm.trans (X.bipointedHomVerticesEquiv x y)).symm.surjective w
  rw [SSet.mapπ₀_mk]
  have h : (DiagSet.toSSet.map (bipointedHom.map (DiagSet.bipointMap F x y))).app _
      (DiagSet.vertexEquivSSet _ ((X.bipointedHomVerticesEquiv x y).symm e)) =
        DiagSet.vertexEquivSSet _ ((Y.bipointedHomVerticesEquiv (x.map F) (y.map F)).symm
          (e.map F)) := by
    refine ((DiagSet.vertexEquivSSet _).symm.trans
      (Y.bipointedHomVerticesEquiv _ _)).injective ?_
    rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    exact (bipointedHomVerticesEquiv_map F _).trans
      (congrArg (·.map F) (Equiv.apply_symm_apply _ e))
  refine Eq.trans (congrArg _ (congrArg SSet.π₀.mk h)) ?_
  exact (DiagSet.bipointedHomπ₀Equiv_mk hY _ _ _).trans
    (congrArg (homotopyFunctor hX.1 hY.1 F).map (DiagSet.bipointedHomπ₀Equiv_mk hX x y e)).symm

def DiagSet.IsFullyFaithful (F : X ⟶ Y) : Prop :=
  ∀ x y : X.Vertex,
    WeakEquivalence ((DiagSet.toInfty 0).map (bipointedHom.map (DiagSet.bipointMap F x y)))

def DiagSet.IsEssentiallySurjective (F : X ⟶ Y) : Prop :=
  ∀ y : Y.Vertex, ∃ x : X.Vertex, ∃ e : Y.Edge (x.map F) y, IsEquivalence Y e.cell

theorem DiagSet.isFullyFaithful_of_weakEquivalence (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (F : X ⟶ Y) [WeakEquivalence ((DiagSet.toInfty 1).map F)] :
    DiagSet.IsFullyFaithful F := fun x y => by
  have : WeakEquivalence ((DiagSet.toInfty 1).map (DiagSet.bipointMap F x y).right) :=
    ‹WeakEquivalence ((DiagSet.toInfty 1).map F)›
  exact weakEquivalence_bipointedHom_map (DiagSet.bipointMap F x y) hX hY

theorem DiagSet.bipointMap_id (x y : X.Vertex) :
    DiagSet.bipointMap (𝟙 X) x y = 𝟙 (X.bipoint x y) := by
  ext1
  rfl

theorem DiagSet.bipointMap_comp (F : X ⟶ Y) (G : Y ⟶ Z) (x y : X.Vertex) :
    DiagSet.bipointMap (F ≫ G) x y =
      DiagSet.bipointMap F x y ≫ DiagSet.bipointMap G _ _ := by
  ext1
  rfl

private theorem weakEquivalence_hom_map_congr {p q : Under pointPair.{u}} {f f' : p ⟶ q}
    (h : f = f') (hf : WeakEquivalence ((DiagSet.toInfty 0).map (bipointedHom.map f))) :
    WeakEquivalence ((DiagSet.toInfty 0).map (bipointedHom.map f')) := h ▸ hf

private theorem weakEquivalence_hom_map_id (p : Under pointPair.{u}) :
    WeakEquivalence ((DiagSet.toInfty 0).map (bipointedHom.map (𝟙 p))) := by
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  infer_instance

private theorem weakEquivalence_hom_map_comp {p q r : Under pointPair.{u}} {f : p ⟶ q}
    {g : q ⟶ r} (hf : WeakEquivalence ((DiagSet.toInfty 0).map (bipointedHom.map f)))
    (hg : WeakEquivalence ((DiagSet.toInfty 0).map (bipointedHom.map g))) :
    WeakEquivalence ((DiagSet.toInfty 0).map (bipointedHom.map (f ≫ g))) := by
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

private theorem weakEquivalence_hom_map_of_comp {p q r : Under pointPair.{u}} {f : p ⟶ q}
    {g : q ⟶ r} (hg : WeakEquivalence ((DiagSet.toInfty 0).map (bipointedHom.map g)))
    (hfg : WeakEquivalence ((DiagSet.toInfty 0).map (bipointedHom.map (f ≫ g)))) :
    WeakEquivalence ((DiagSet.toInfty 0).map (bipointedHom.map f)) := by
  rw [Functor.map_comp, Functor.map_comp] at hfg
  exact weakEquivalence_of_postcomp _ ((DiagSet.toInfty 0).map (bipointedHom.map g))

theorem DiagSet.isFullyFaithful_id (X : DiagSet.{u}) : DiagSet.IsFullyFaithful (𝟙 X) :=
  fun x y => weakEquivalence_hom_map_congr (DiagSet.bipointMap_id x y).symm
    (weakEquivalence_hom_map_id _)

theorem DiagSet.IsFullyFaithful.comp {F : X ⟶ Y} {G : Y ⟶ Z} (hF : DiagSet.IsFullyFaithful F)
    (hG : DiagSet.IsFullyFaithful G) : DiagSet.IsFullyFaithful (F ≫ G) := fun x y =>
  weakEquivalence_hom_map_congr (DiagSet.bipointMap_comp F G x y).symm
    (weakEquivalence_hom_map_comp (hF x y) (hG _ _))

theorem DiagSet.IsFullyFaithful.of_comp {F : X ⟶ Y} {G : Y ⟶ Z}
    (hG : DiagSet.IsFullyFaithful G) (hFG : DiagSet.IsFullyFaithful (F ≫ G)) :
    DiagSet.IsFullyFaithful F := fun x y =>
  weakEquivalence_hom_map_of_comp (hG _ _)
    (weakEquivalence_hom_map_congr (DiagSet.bipointMap_comp F G x y) (hFG x y))

theorem DiagSet.IsEssentiallySurjective.comp (hY : IsInftyCategory 1 Y)
    (hZ : IsInftyCategory 1 Z) {F : X ⟶ Y} {G : Y ⟶ Z}
    (hF : DiagSet.IsEssentiallySurjective F) (hG : DiagSet.IsEssentiallySurjective G) :
    DiagSet.IsEssentiallySurjective (F ≫ G) := by
  intro z
  obtain ⟨y, e₂, h₂⟩ := hG z
  obtain ⟨x, e₁, h₁⟩ := hF y
  obtain ⟨h, hh⟩ := exists_edge_equivalent_pasteEdges hZ.1 (e₁.map G) e₂
  refine ⟨x, h, (HomotopyCategory.isIso_homMk_iff hZ.1 h).1 ?_⟩
  rw [← HomotopyCategory.isIso_homMk_iff hZ.1] at h₂
  have h₁' := (HomotopyCategory.isIso_homMk_iff hY.1 e₁).2 h₁
  have : IsIso ((homotopyFunctor hY.1 hZ.1 G).map (HomotopyCategory.homMk hY.1 e₁)) :=
    inferInstance
  rw [homotopyFunctor_map_homMk] at this
  have hc := (HomotopyCategory.homMk_comp_homMk_iff hZ.1 (e₁.map G) e₂ h).2 hh
  rw [← hc]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ this h₂

private theorem bijective_homotopyFunctor_map (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) {F : X ⟶ Y} (hF : DiagSet.IsFullyFaithful F)
    (x y : X.Vertex) :
    Function.Bijective
      (fun φ : (⟨x⟩ : HomotopyCategory X hX.1) ⟶ ⟨y⟩ =>
        (homotopyFunctor hX.1 hY.1 F).map φ) := by
  have := hF x y
  have hb := DiagSet.bijective_mapπ₀_of_weakEquivalence
    (isInftyCategory_bipointedHom (n := 0) (by simpa using hX))
    (isInftyCategory_bipointedHom (n := 0) (p := Y.bipoint (x.map F)
      (y.map F)) (by simpa using hY))
    (bipointedHom.map (DiagSet.bipointMap F x y))
  have h : (fun φ : (⟨x⟩ : HomotopyCategory X hX.1) ⟶ ⟨y⟩ =>
      (homotopyFunctor hX.1 hY.1 F).map φ) =
      (Y.bipointedHomπ₀Equiv hY _ _) ∘
        (SSet.mapπ₀ (DiagSet.toSSet.map (bipointedHom.map (DiagSet.bipointMap F x y)))) ∘
          (X.bipointedHomπ₀Equiv hX x y).symm := funext fun φ => by
    rw [Function.comp_apply, Function.comp_apply, DiagSet.bipointedHomπ₀Equiv_mapπ₀ hX hY,
      Equiv.apply_symm_apply]
  rw [h]
  exact (Y.bipointedHomπ₀Equiv hY _ _).bijective.comp
    (hb.comp (X.bipointedHomπ₀Equiv hX x y).symm.bijective)

noncomputable def DiagSet.IsFullyFaithful.homotopyFunctor (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) {F : X ⟶ Y} (hF : DiagSet.IsFullyFaithful F) :
    (Atoms.Diagrammatic.homotopyFunctor hX.1 hY.1 F).FullyFaithful :=
  have : (Atoms.Diagrammatic.homotopyFunctor hX.1 hY.1 F).Full :=
    ⟨fun {a b} φ => (bijective_homotopyFunctor_map hX hY hF a.pt b.pt).2 φ⟩
  have : (Atoms.Diagrammatic.homotopyFunctor hX.1 hY.1 F).Faithful :=
    ⟨fun {a b} _ _ h => (bijective_homotopyFunctor_map hX hY hF a.pt b.pt).1 h⟩
  Functor.FullyFaithful.ofFullyFaithful _

theorem DiagSet.isEssentiallySurjective_iff_essSurj (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) (F : X ⟶ Y) :
    DiagSet.IsEssentiallySurjective F ↔ (homotopyFunctor hX.1 hY.1 F).EssSurj := by
  constructor
  · intro h
    refine ⟨fun b => ?_⟩
    obtain ⟨x, e, he⟩ := h b.pt
    have hiso := (HomotopyCategory.isIso_homMk_iff hY.1 e).2 he
    exact ⟨⟨x⟩, ⟨@asIso _ _ _ _ (HomotopyCategory.homMk hY.1 e) hiso⟩⟩
  · intro h y
    obtain ⟨a, ⟨i⟩⟩ := h.mem_essImage (⟨y⟩ : HomotopyCategory Y hY.1)
    obtain ⟨e, he⟩ := HomotopyCategory.homMk_surjective hY.1 i.hom
    have : IsIso i.hom := inferInstance
    rw [← he] at this
    exact ⟨a.pt, e, (HomotopyCategory.isIso_homMk_iff hY.1 e).1 this⟩

theorem DiagSet.isEquivalence_homotopyFunctor (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) {F : X ⟶ Y} (hF : DiagSet.IsFullyFaithful F)
    (hF' : DiagSet.IsEssentiallySurjective F) : (homotopyFunctor hX.1 hY.1 F).IsEquivalence :=
  { faithful := (hF.homotopyFunctor hX hY).faithful
    full := (hF.homotopyFunctor hX hY).full
    essSurj := (DiagSet.isEssentiallySurjective_iff_essSurj hX hY F).1 hF' }

theorem DiagSet.IsFullyFaithful.isEquivalence_edge_iff (hX : IsInftyCategory 1 X)
    (hY : IsInftyCategory 1 Y) {F : X ⟶ Y} (hF : DiagSet.IsFullyFaithful F)
    (e : X.Edge x y) : IsEquivalence Y (e.map F).cell ↔ IsEquivalence X e.cell := by
  have := (hF.homotopyFunctor hX hY).full
  have := (hF.homotopyFunctor hX hY).faithful
  rw [← HomotopyCategory.isIso_homMk_iff hY.1, ← HomotopyCategory.isIso_homMk_iff hX.1,
    ← homotopyFunctor_map_homMk hX.1 hY.1 F]
  exact isIso_iff_of_reflects_iso (HomotopyCategory.homMk hX.1 e)
    (Atoms.Diagrammatic.homotopyFunctor hX.1 hY.1 F)

end Atoms.Diagrammatic
