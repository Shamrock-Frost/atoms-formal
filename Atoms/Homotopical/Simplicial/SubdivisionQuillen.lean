import Atoms.Homotopical.Simplicial.KanQuillen
import Atoms.Homotopical.Localizer.LeftProper
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Quillen

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial PartialOrder

universe u

namespace Atoms.Homotopical

theorem kanWeak_lastVertex_app_stdSimplex (n : ℕ) : kanWeak (lastVertex.{u}.app Δ[n]) := by
  let : OrderTop (NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :=
    { top := chainIic ⦋n⦌ ⊤
      le_top := fun S a _ => (mem_chainIic _ _).2 le_top }
  have : HasTerminal (NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :=
    isTerminalTop.hasTerminal
  have hs : kanWeak (simplexLastVertex.app ⦋n⦌) := by
    apply kanWeak.of_postcomp _ (terminal.from Δ[n])
      (terminal_from_stdSimplex_mem_kanWeak n)
    rw [terminal.hom_ext (simplexLastVertex.app ⦋n⦌ ≫ terminal.from Δ[n]) (terminal.from _)]
    exact terminal_from_nerve_mem_kanWeak (NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))
  have hi : kanWeak (SSet.stdSimplex.sdIso.inv.app ⦋n⦌) :=
    isomorphisms_le_of_containsIdentities kanWeak _ (isomorphisms.infer_property _)
  exact kanWeak.of_precomp _ _ hi (by rwa [sdIso_inv_app_lastVertex_app])

theorem kanWeak_lastVertex_app (X : SSet.{u}) : kanWeak (lastVertex.app X) := by
  have := SSet.sdExAdjunction.isLeftAdjoint
  refine forall_of_stdSimplex
    (IsALocalizer.isMonoSaturatedClass_app SSet.sd (𝟭 SSet.{u})
      (fun f _ => mono_sd_map f) (fun _ h => h) lastVertex) ?_
    kanWeak_lastVertex_app_stdSimplex X
  intro Y Z i r hir hZ
  let R : RetractArrow (lastVertex.app Y) (lastVertex.app Z) :=
    { i := Arrow.homMk (SSet.sd.map i) i (lastVertex.naturality i)
      r := Arrow.homMk (SSet.sd.map r) r (lastVertex.naturality r)
      retract := by ext <;> simp [← Functor.map_comp, hir] }
  exact MorphismProperty.of_retract R hZ

theorem kanWeak_sd_map_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    kanWeak (SSet.sd.map f) ↔ kanWeak f := by
  have hn : SSet.sd.map f ≫ lastVertex.app Y = lastVertex.app X ≫ f :=
    lastVertex.naturality f
  constructor
  · intro hf
    apply kanWeak.of_precomp (lastVertex.app X) f (kanWeak_lastVertex_app X)
    rw [← hn]
    exact kanWeak.comp_mem _ _ hf (kanWeak_lastVertex_app Y)
  · intro hf
    apply kanWeak.of_postcomp (SSet.sd.map f) (lastVertex.app Y) (kanWeak_lastVertex_app Y)
    rw [hn]
    exact kanWeak.comp_mem _ _ (kanWeak_lastVertex_app X) hf

theorem kanWeak_exUnit_app (X : SSet.{u}) : kanWeak (exUnit.app X) :=
  anodyneExtensions_le_kanWeak _ (SSet.strongAnodyneExtensions_le_anodyneExtensions _
    (strongAnodyneExtensions_exUnit_app X))

theorem kanWeak_ex_map_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    kanWeak (SSet.ex.map f) ↔ kanWeak f := by
  have hn : f ≫ exUnit.app Y = exUnit.app X ≫ SSet.ex.map f := exUnit.naturality f
  constructor
  · intro hf
    apply kanWeak.of_postcomp f (exUnit.app Y) (kanWeak_exUnit_app Y)
    rw [hn]
    exact kanWeak.comp_mem _ _ (kanWeak_exUnit_app X) hf
  · intro hf
    apply kanWeak.of_precomp (exUnit.app X) (SSet.ex.map f) (kanWeak_exUnit_app X)
    rw [← hn]
    exact kanWeak.comp_mem _ _ hf (kanWeak_exUnit_app Y)

open SSet.modelCategoryQuillen in
theorem isQuillen_sdExAdjunction : SSet.sdExAdjunction.{u}.IsQuillen := by
  refine SSet.sdExAdjunction.isQuillen_of_fibrations_between_fibrant ?_ ?_
  · intro X Y f hf
    have : Mono f := hf
    exact mono_sd_map f
  · intro X Y p _ _ hp
    exact (fibration_iff _).2 (J_rlp_ex_map ((fibration_iff _).1 hp))

open SSet.modelCategoryQuillen in
theorem isQuillenEquivalence_sdExAdjunction : SSet.sdExAdjunction.{u}.IsQuillenEquivalence := by
  refine ⟨isQuillen_sdExAdjunction, fun {A X} _ _ f => ?_⟩
  have hη : kanWeak (SSet.sdExAdjunction.unit.app A) := by
    apply kanWeak.of_postcomp _ (SSet.ex.map (lastVertex.app A))
      ((kanWeak_ex_map_iff _).2 (kanWeak_lastVertex_app A))
    have h := kanWeak_exUnit_app A
    change kanWeak (SSet.sdExAdjunction.unit.app A ≫
      SSet.ex.map (lastVertex.app A) ≫ 𝟙 _) at h
    rwa [Category.comp_id] at h
  rw [weakEquivalence_iff, weakEquivalence_iff, Adjunction.homEquiv_unit]
  constructor
  · intro hf
    exact kanWeak.comp_mem _ _ hη ((kanWeak_ex_map_iff f).2 hf)
  · intro hf
    exact (kanWeak_ex_map_iff f).1 (kanWeak.of_precomp _ _ hη hf)

end Atoms.Homotopical
